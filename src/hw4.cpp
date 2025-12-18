#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <climits>
#include <cmath>
#include <chrono>
#include <queue>
#include <limits>
#include <numeric>
#include <deque>

using namespace std;
using Clock = std::chrono::high_resolution_clock;

struct Pin
{
    string name;
    int x, y;
};

struct nets
{
    string netname;
    Pin pin1;
    Pin pin2;
};

struct EdgeData
{
    int cap = 0;
    int demand = 0;
    double history = 0;
};

struct PQNode
{
    int x, y;
    double g, f;
    bool operator<(const PQNode &o) const { return f > o.f; } // min-heap
};

struct Segment
{
    int x1, y1, x2, y2;
};

int GRID_C = 0;
int GRID_R = 0;
int H_CAP = 0;
int V_CAP = 0;

vector<nets> netlist;
vector<vector<EdgeData>> horizEdges; // (GRID_C-1) x GRID_R
vector<vector<EdgeData>> vertEdges;  // GRID_C x (GRID_R-1)

using Path = vector<pair<int, int>>;
vector<Path> all_paths;

// Forward declarations
inline EdgeData &getEdgeRef(int x1, int y1, int x2, int y2);
inline long long path_wirelength(const Path &p);

static long long TOTAL_OVERFLOW = 0;
static long long TOTAL_WL = 0;

inline int edge_overflow(const EdgeData &e)
{
    return (e.demand > e.cap) ? (e.demand - e.cap) : 0;
}

inline int manhattan(int x, int y, int tx, int ty)
{
    return abs(x - tx) + abs(y - ty);
}

// ==========================
// Edge access
// ==========================
inline EdgeData &getEdgeRef(int x1, int y1, int x2, int y2)
{
#ifndef NDEBUG
    if (abs(x1 - x2) + abs(y1 - y2) != 1)
    {
        cerr << "getEdgeRef: non-adjacent move (" << x1 << "," << y1
             << ") -> (" << x2 << "," << y2 << ")\n";
        exit(1);
    }
#endif

    if (y1 == y2)
    {
        int x = min(x1, x2);
        return horizEdges[x][y1];
    }
    else
    {
        int y = min(y1, y2);
        return vertEdges[x1][y];
    }
}

// feasibility under hard-cap
static inline bool edge_feasible_add1(int x1, int y1, int x2, int y2, bool forbidOverflow)
{
    EdgeData &e = getEdgeRef(x1, y1, x2, y2);
    if (!forbidOverflow)
        return true;
    return (e.demand + 1 <= e.cap);
}

inline double gcost(int cur_x, int cur_y, int next_x, int next_y,
                    double ALPHA, double BETA,
                    bool forbidOverflow)
{
    EdgeData &e = getEdgeRef(cur_x, cur_y, next_x, next_y);

    if (forbidOverflow && e.demand + 1 > e.cap)
    {
        return numeric_limits<double>::infinity();
    }

    double cap = (double)max(1, e.cap);
    double util = (double)(e.demand + 1) / cap;
    return 1.0 + ALPHA * util + BETA * e.history;
}

// ==========================
// Demand update (incremental overflow)
// ==========================
inline long long path_wirelength(const Path &p)
{
    return (p.size() >= 2) ? (long long)(p.size() - 1) : 0LL;
}

inline void apply_path_demand(const Path &path)
{
    for (size_t i = 1; i < path.size(); ++i)
    {
        auto [x1, y1] = path[i - 1];
        auto [x2, y2] = path[i];
        EdgeData &e = getEdgeRef(x1, y1, x2, y2);

        int old_of = edge_overflow(e);
        e.demand += 1;
        int new_of = edge_overflow(e);
        TOTAL_OVERFLOW += (new_of - old_of);
    }
}

inline void remove_path_demand(const Path &path)
{
    for (size_t i = 1; i < path.size(); ++i)
    {
        auto [x1, y1] = path[i - 1];
        auto [x2, y2] = path[i];
        EdgeData &e = getEdgeRef(x1, y1, x2, y2);

        int old_of = edge_overflow(e);
        e.demand -= 1;
        int new_of = edge_overflow(e);
        TOTAL_OVERFLOW += (new_of - old_of);
    }
}

// ==========================
// Reset
// ==========================
void reset_all_demands()
{
    for (int x = 0; x < GRID_C - 1; ++x)
        for (int y = 0; y < GRID_R; ++y)
            horizEdges[x][y].demand = 0;

    for (int x = 0; x < GRID_C; ++x)
        for (int y = 0; y < GRID_R - 1; ++y)
            vertEdges[x][y].demand = 0;

    TOTAL_OVERFLOW = 0;
    TOTAL_WL = 0;
}

// ==========================
// History update
// ==========================
void update_history_from_overflow()
{
    for (int x = 0; x < GRID_C - 1; ++x)
    {
        for (int y = 0; y < GRID_R; ++y)
        {
            auto &e = horizEdges[x][y];
            int of = max(0, e.demand - e.cap);
            if (of > 0)
                e.history += of;
        }
    }
    for (int x = 0; x < GRID_C; ++x)
    {
        for (int y = 0; y < GRID_R - 1; ++y)
        {
            auto &e = vertEdges[x][y];
            int of = max(0, e.demand - e.cap);
            if (of > 0)
                e.history += of;
        }
    }
}

// ==========================
// Net scoring for selective rip-up
// ==========================
long long net_overflow_score(const Path &path)
{
    long long s = 0;
    for (size_t i = 1; i < path.size(); ++i)
    {
        auto [x1, y1] = path[i - 1];
        auto [x2, y2] = path[i];
        const EdgeData &e = getEdgeRef(x1, y1, x2, y2);
        if (e.demand > e.cap)
            s += (e.demand - e.cap);
    }
    return s;
}

vector<int> pick_topK_nets_by_score(const vector<Path> &paths, int K)
{
    vector<pair<long long, int>> score_id;
    score_id.reserve(paths.size());

    for (int i = 0; i < (int)paths.size(); ++i)
    {
        long long sc = net_overflow_score(paths[i]);
        if (sc > 0)
            score_id.push_back({sc, i});
    }

    sort(score_id.begin(), score_id.end(),
         [](const auto &a, const auto &b)
         { return a.first > b.first; });

    vector<int> pick;
    pick.reserve(K);
    for (int i = 0; i < (int)score_id.size() && (int)pick.size() < K; ++i)
        pick.push_back(score_id[i].second);

    return pick;
}

// ==========================
// Fast global A* buffers (1D + timestamp)
// ==========================
static vector<double> gScore1D;
static vector<int> parent1D;
static vector<int> seenStamp;
static vector<int> closedStamp;
static int CUR_STAMP = 1;

inline int vid(int x, int y) { return x * GRID_R + y; }

void init_astar_buffers()
{
    int N = GRID_C * GRID_R;
    gScore1D.assign(N, 0.0);
    parent1D.assign(N, -1);
    seenStamp.assign(N, 0);
    closedStamp.assign(N, 0);
    CUR_STAMP = 1;
}

// ==========================
// Monotonic router (0-1 BFS with detour budget)
// - detourBudget = 0: strict monotone (every step reduces Manhattan)
// - detourBudget > 0: allow limited steps that do NOT reduce Manhattan (escape saturated edges)
// - Always respects hard-cap when forbidOverflow=true
// ==========================
Path monotonic_route_01bfs(int sx, int sy, int tx, int ty, int detourBudget, bool forbidOverflow)
{
    if (sx == tx && sy == ty)
        return {{sx, sy}};

    const int N = GRID_C * GRID_R;
    auto inb = [&](int x, int y)
    { return x >= 0 && x < GRID_C && y >= 0 && y < GRID_R; };

    const int K = detourBudget;
    const int INF = 1e9;

    // dist[state] where state = k*N + v
    vector<int> dist((K + 1) * N, INF);
    vector<int> parent((K + 1) * N, -1);

    auto sid = [&](int v, int k)
    { return k * N + v; };

    deque<int> dq;
    int s = vid(sx, sy), t = vid(tx, ty);
    dist[sid(s, 0)] = 0;
    dq.push_front(sid(s, 0));

    static const int dx[4] = {1, -1, 0, 0};
    static const int dy[4] = {0, 0, 1, -1};

    while (!dq.empty())
    {
        int st = dq.front();
        dq.pop_front();
        int k = st / N;
        int v = st % N;
        int x = v / GRID_R;
        int y = v % GRID_R;

        if (v == t)
        {
            // reconstruct
            Path path;
            int cur = st;
            while (cur != -1)
            {
                int vv = cur % N;
                int cx = vv / GRID_R;
                int cy = vv % GRID_R;
                path.push_back({cx, cy});
                cur = parent[cur];
            }
            reverse(path.begin(), path.end());
            return path;
        }

        int curD = dist[st];
        int curH = manhattan(x, y, tx, ty);

        for (int dir = 0; dir < 4; ++dir)
        {
            int nx = x + dx[dir];
            int ny = y + dy[dir];
            if (!inb(nx, ny))
                continue;

            if (!edge_feasible_add1(x, y, nx, ny, forbidOverflow))
                continue;

            int nv = vid(nx, ny);
            int nh = manhattan(nx, ny, tx, ty);

            // monotone step: strictly reduces Manhattan
            // non-monotone (or equal): counted as detour
            int w = (nh < curH) ? 0 : 1;
            int nk = k + w;
            if (nk > K)
                continue;

            int nst = sid(nv, nk);
            if (curD + 1 < dist[nst])
            {
                dist[nst] = curD + 1;
                parent[nst] = st;
                if (w == 0)
                    dq.push_front(nst);
                else
                    dq.push_back(nst);
            }
        }
    }
    return {};
}

Path monotonic_route_try_budgets(int sx, int sy, int tx, int ty, bool forbidOverflow)
{
    static const int budgets[] = {0, 2, 4, 6, 8, 10, 12};

    for (int b : budgets)
    {
        Path p = monotonic_route_01bfs(sx, sy, tx, ty, b, forbidOverflow);
        if (!p.empty())
            return p;
    }
    return {};
}

// ==========================
// Fast A* (fallback) with stamps
// ==========================
Path astar_route_one_net_fast(int sx, int sy, int tx, int ty,
                              double ALPHA, double BETA,
                              bool forbidOverflow,
                              bool debug_print_g_h_f)
{
    // Monotonic-first: try monotone/near-monotone routes first to reduce WL.
    // If it fails, fall back to A* (still respecting forbidOverflow).
    if (forbidOverflow || (ALPHA == 0.0 && BETA == 0.0))
    {
        Path mono = monotonic_route_try_budgets(sx, sy, tx, ty, /*forbidOverflow=*/forbidOverflow);
        if (!mono.empty())
            return mono;
    }

    const double INF = 1e30;

    ++CUR_STAMP;
    if (CUR_STAMP == INT_MAX)
    {
        fill(seenStamp.begin(), seenStamp.end(), 0);
        fill(closedStamp.begin(), closedStamp.end(), 0);
        CUR_STAMP = 1;
    }

    priority_queue<PQNode> pq;

    int s = vid(sx, sy);
    int t = vid(tx, ty);

    seenStamp[s] = CUR_STAMP;
    gScore1D[s] = 0.0;
    parent1D[s] = -1;

    double h0 = (double)manhattan(sx, sy, tx, ty);
    pq.push({sx, sy, 0.0, h0});

    static const int dir_x[4] = {1, -1, 0, 0};
    static const int dir_y[4] = {0, 0, 1, -1};

    while (!pq.empty())
    {
        PQNode cur = pq.top();
        pq.pop();
        int x = cur.x, y = cur.y;
        int u = vid(x, y);

        if (closedStamp[u] == CUR_STAMP)
            continue;
        closedStamp[u] = CUR_STAMP;

        if (debug_print_g_h_f)
        {
            double g = (seenStamp[u] == CUR_STAMP) ? gScore1D[u] : INF;
            double h = (double)manhattan(x, y, tx, ty);
            cerr << "[POP] (" << x << "," << y << ") g=" << g << " h=" << h << " f=" << (g + h) << "\n";
        }

        if (u == t)
        {
            Path path;
            int curv = t;
            while (curv != -1)
            {
                int cx = curv / GRID_R;
                int cy = curv % GRID_R;
                path.push_back({cx, cy});
                if (curv == s)
                    break;
                curv = parent1D[curv];
            }
            reverse(path.begin(), path.end());
            return path;
        }

        double gu = (seenStamp[u] == CUR_STAMP) ? gScore1D[u] : INF;

        for (int d = 0; d < 4; ++d)
        {
            int nx = x + dir_x[d];
            int ny = y + dir_y[d];
            if (nx < 0 || nx >= GRID_C || ny < 0 || ny >= GRID_R)
                continue;

            int v = vid(nx, ny);
            if (closedStamp[v] == CUR_STAMP)
                continue;

            double step = gcost(x, y, nx, ny, ALPHA, BETA, forbidOverflow);
            if (!isfinite(step))
                continue;

            double ng = gu + step;
            if (seenStamp[v] != CUR_STAMP || ng < gScore1D[v])
            {
                seenStamp[v] = CUR_STAMP;
                gScore1D[v] = ng;
                parent1D[v] = u;

                double h = (double)manhattan(nx, ny, tx, ty);
                pq.push({nx, ny, ng, ng + h});
            }
        }
    }

    return {};
}

// ==========================
// WL Polish: overflow=0 hard constraint, accept only if shorter
// ==========================
void polish_wirelength(vector<Path> &cur_paths, int rounds = 8)
{
    int noImp = 0;
    for (int r = 0; r < rounds; ++r)
    {
        bool improved = false;

        vector<int> order(cur_paths.size());
        iota(order.begin(), order.end(), 0);

        // prioritize long nets
        sort(order.begin(), order.end(), [&](int a, int b)
             { return cur_paths[a].size() > cur_paths[b].size(); });

        for (int id : order)
        {
            const Path oldp = cur_paths[id];
            long long old_wl = path_wirelength(oldp);
            if (old_wl <= 0)
                continue;

            // rip old
            remove_path_demand(oldp);
            TOTAL_WL -= old_wl;

            int sx = netlist[id].pin1.x, sy = netlist[id].pin1.y;
            int tx = netlist[id].pin2.x, ty = netlist[id].pin2.y;

            // monotonic-first, hard-cap
            Path newp = monotonic_route_try_budgets(sx, sy, tx, ty, /*forbidOverflow=*/true);
            if (newp.empty())
            {
                newp = astar_route_one_net_fast(
                    sx, sy, tx, ty,
                    /*ALPHA=*/0.0, /*BETA=*/0.0,
                    /*forbidOverflow=*/true,
                    /*debug=*/false);
            }

            bool accept = false;
            if (!newp.empty())
            {
                long long new_wl = path_wirelength(newp);
                if (new_wl < old_wl)
                    accept = true;
            }

            if (accept)
            {
                cur_paths[id] = newp;
                apply_path_demand(newp);
                TOTAL_WL += path_wirelength(newp);
                improved = true;
            }
            else
            {
                // revert
                apply_path_demand(oldp);
                TOTAL_WL += old_wl;
            }
        }

        cerr << "[POLISH " << r << "] wirelength=" << TOTAL_WL
             << " overflow=" << TOTAL_OVERFLOW << "\n";

        if (!improved)
        {
            if (++noImp >= 3)
                break;
        }
        else
        {
            noImp = 0;
        }
    }
}

// ==========================
// Main routing (initial + selective RNR (hard-cap) + WL polish (hard-cap))
// ==========================
void Astar_search_fast()
{
    const int INITIAL_ONLY = 40;
    const int REPAIR_ITERS = 60;

    const double ALPHA_INIT = 3.0;
    const double BETA_INIT = 0.5;

    const double ALPHA_RNR = 5.0;
    const double BETA_RNR = 1.0;

    const int K_MIN = 1;
    const double K_RATIO = 0.03;

    vector<Path> cur_paths(netlist.size());
    vector<Path> best_paths;
    long long best_of = LLONG_MAX;
    long long best_wl = LLONG_MAX;

    // 0) initial routing (may overflow; repair will remove overflow under hard-cap)
    reset_all_demands();

    for (int t = 0; t < INITIAL_ONLY; ++t)
    {
        if (t > 0)
            reset_all_demands();

        for (int i = 0; i < (int)netlist.size(); ++i)
        {
            int sx = netlist[i].pin1.x, sy = netlist[i].pin1.y;
            int tx = netlist[i].pin2.x, ty = netlist[i].pin2.y;

            Path path = astar_route_one_net_fast(
                sx, sy, tx, ty,
                ALPHA_INIT, BETA_INIT,
                /*forbidOverflow=*/false,
                /*debug=*/false);

            if (path.empty())
            {
                // If A* fails even in soft mode, fallback Manhattan (may overflow in initial)
                int x = sx, y = sy;
                path.push_back({x, y});
                while (x != tx)
                {
                    x += (tx > x ? 1 : -1);
                    path.push_back({x, y});
                }
                while (y != ty)
                {
                    y += (ty > y ? 1 : -1);
                    path.push_back({x, y});
                }
            }

            cur_paths[i] = path;
            apply_path_demand(path);
            TOTAL_WL += path_wirelength(path);
        }

        update_history_from_overflow();
    }

    cerr << "[INIT] wirelength=" << TOTAL_WL << " overflow=" << TOTAL_OVERFLOW << "\n";

    best_of = TOTAL_OVERFLOW;
    best_wl = TOTAL_WL;
    best_paths = cur_paths;

    // 1) repair loop: selective rip-up & reroute (HARD-CAP ONLY, rollback on failure)
    for (int iter = 0; iter < REPAIR_ITERS; ++iter)
    {
        if (TOTAL_OVERFLOW == 0)
        {
            cerr << "Zero overflow reached, stop early.\n";
            break;
        }

        int K = max(K_MIN, (int)llround(K_RATIO * (double)netlist.size()));
        vector<int> rip_ids = pick_topK_nets_by_score(cur_paths, K);

        if (rip_ids.empty() && !cur_paths.empty())
        {
            int worst = 0;
            for (int i = 1; i < (int)cur_paths.size(); ++i)
                if (cur_paths[i].size() > cur_paths[worst].size())
                    worst = i;
            rip_ids.push_back(worst);
        }

        // backup for rollback
        unordered_map<int, Path> backup;
        backup.reserve(rip_ids.size());
        for (int id : rip_ids)
            backup[id] = cur_paths[id];

        // rip-up
        for (int id : rip_ids)
        {
            remove_path_demand(cur_paths[id]);
            TOTAL_WL -= path_wirelength(cur_paths[id]);
        }

        // reroute (hard-cap only)
        for (int id : rip_ids)
        {
            int sx = netlist[id].pin1.x, sy = netlist[id].pin1.y;
            int tx = netlist[id].pin2.x, ty = netlist[id].pin2.y;

            Path newp = astar_route_one_net_fast(
                sx, sy, tx, ty,
                ALPHA_RNR, BETA_RNR,
                /*forbidOverflow=*/true,
                /*debug=*/false);

            if (newp.empty())
            {
                // rollback old path (hard-cap safety)
                cur_paths[id] = backup[id];
            }
            else
            {
                cur_paths[id] = newp;
            }

            apply_path_demand(cur_paths[id]);
            TOTAL_WL += path_wirelength(cur_paths[id]);
        }

        update_history_from_overflow();

        cerr << "[RNR " << iter << "] wirelength=" << TOTAL_WL
             << " overflow=" << TOTAL_OVERFLOW
             << " ripped=" << rip_ids.size() << "\n";

        if (TOTAL_OVERFLOW < best_of || (TOTAL_OVERFLOW == best_of && TOTAL_WL < best_wl))
        {
            best_of = TOTAL_OVERFLOW;
            best_wl = TOTAL_WL;
            best_paths = cur_paths;
        }

        if (best_of == 0)
            break;
    }

    // 2) Build best solution as base
    reset_all_demands();
    for (const auto &p : best_paths)
    {
        apply_path_demand(p);
        TOTAL_WL += path_wirelength(p);
    }

    // 3) WL Polish on best solution (hard-cap, accept only shorter)
    all_paths = best_paths;
    polish_wirelength(all_paths, /*rounds=*/12);

    // 4) Rebuild again for output consistency
    reset_all_demands();
    for (const auto &p : all_paths)
    {
        apply_path_demand(p);
        TOTAL_WL += path_wirelength(p);
    }

    cerr << "=== FINAL ===\n";
    cerr << "Best wirelength = " << TOTAL_WL << "\n";
    cerr << "Best overflow   = " << TOTAL_OVERFLOW << "\n";
}

// ==========================
// Output formatting
// ==========================
vector<Segment> compress_to_segments(const Path &path)
{
    vector<Segment> segs;
    if (path.size() < 2)
        return segs;

    int sx = path[0].first, sy = path[0].second;
    int px = path[1].first, py = path[1].second;

    int dx = px - sx;
    int dy = py - sy;

    int seg_x1 = sx, seg_y1 = sy;

    for (size_t i = 2; i < path.size(); ++i)
    {
        int cx = path[i].first, cy = path[i].second;
        int ndx = cx - px;
        int ndy = cy - py;

        if (ndx != dx || ndy != dy)
        {
            segs.push_back({seg_x1, seg_y1, px, py});
            seg_x1 = px;
            seg_y1 = py;
            dx = ndx;
            dy = ndy;
        }

        px = cx;
        py = cy;
    }

    segs.push_back({seg_x1, seg_y1, px, py});
    return segs;
}

void outputSolution(const string &outFile, const vector<Path> &paths)
{
    ofstream fout(outFile);
    if (!fout)
    {
        cerr << "Cannot open output file: " << outFile << "\n";
        exit(1);
    }

    fout << "Wirelength " << TOTAL_WL << "\n";

    for (int i = 0; i < (int)netlist.size(); ++i)
    {
        fout << "Net " << netlist[i].netname << "\n";
        const auto &path = paths[i];
        if (path.size() < 2)
            continue;

        auto segs = compress_to_segments(path);
        for (const auto &s : segs)
        {
            fout << "Segment " << s.x1 << " " << s.y1 << " "
                 << s.x2 << " " << s.y2 << "\n";
        }
    }
    fout.close();
}

// ==========================
// Input parsing
// ==========================
void parseInput(string &inFile, unordered_map<string, int> &netMap)
{
    ifstream fin(inFile);
    if (!fin)
    {
        cerr << "Cannot open input file: " << inFile << endl;
        exit(1);
    }

    string line, name;
    int numNets = 0;

    while (getline(fin, line))
    {
        istringstream info(line);
        info >> name;
        if (name == "Grid")
        {
            info >> GRID_C >> GRID_R;
        }
        else if (name == "Capacity")
        {
            info >> H_CAP >> V_CAP;
        }
        else if (name == "NumNets")
        {
            info >> numNets;
            netlist.reserve(numNets);
            break;
        }
    }

    for (int i = 0; i < numNets; i++)
    {
        getline(fin, line);
        istringstream netinfo(line);
        string temp, netname;
        int pinCount;
        netinfo >> temp;
        if (temp == "Net")
        {
            netinfo >> netname >> pinCount;
            nets newnet;
            newnet.netname = netname;
            netMap[netname] = i;

            for (int j = 0; j < pinCount; j++)
            {
                getline(fin, line);
                istringstream pininfo(line);
                string pintemp, pinname;
                int x, y;
                pininfo >> pintemp;
                if (pintemp == "Pin")
                {
                    pininfo >> pinname >> x >> y;
                    Pin newpin{pinname, x, y};

                    if (j == 0)
                    {
                        newnet.pin1 = newpin;
                        netlist.push_back(newnet);
                    }
                    else if (j == 1)
                    {
                        newnet.pin2 = newpin;
                        netlist[i] = newnet;
                    }
                }
            }
        }
    }

    horizEdges.assign(GRID_C - 1, vector<EdgeData>(GRID_R));
    vertEdges.assign(GRID_C, vector<EdgeData>(GRID_R - 1));

    for (int y = 0; y < GRID_R; ++y)
        for (int x = 0; x < GRID_C - 1; ++x)
            horizEdges[x][y].cap = H_CAP;

    for (int y = 0; y < GRID_R - 1; ++y)
        for (int x = 0; x < GRID_C; ++x)
            vertEdges[x][y].cap = V_CAP;
}

int main(int argc, char *argv[])
{
    auto start = Clock::now();

    if (argc != 3)
    {
        cerr << "Usage: " << argv[0] << " <input_file> <output_file>\n";
        return 1;
    }

    cerr << "[VERSION] monotonic-first + hardcap-repair+polish\n";

    string inFile = argv[1];
    string outFile = argv[2];

    unordered_map<string, int> netMap;
    parseInput(inFile, netMap);

    init_astar_buffers();

    Astar_search_fast();
    outputSolution(outFile, all_paths);

    auto end = Clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    cout << "Execution time: " << duration.count() << " milliseconds" << endl;
    return 0;
}
