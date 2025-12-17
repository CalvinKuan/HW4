#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <queue>
#include <string>
#include <algorithm>
#include <cmath>
#include <limits>
#include <unordered_map>
#include <climits>
using namespace std;

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
    int cap = 0;        // capacity
    int demand = 0;     // current demand
    double history = 0; // history cost
};

struct PQNode {
    int x, y;
    double g, f;
    bool operator<(const PQNode& o) const { return f > o.f; } // min-heap
};

struct Stats {
    long long overflow = 0;
    long long wirelength = 0;
};

struct Segment {
    int x1, y1, x2, y2;
};



int GRID_C = 0;        // grid columns
int GRID_R = 0;        // grid rows
int H_CAP = 0;
int V_CAP = 0;
vector<nets> netlist;
vector<vector<int>> routing_graph;
vector<vector<int>> g_graph;
vector<vector<EdgeData>> horizEdges;
vector<vector<EdgeData>> vertEdges;

inline int manhattan(int x, int y, int tx, int ty){
    return abs(x - tx) + abs(y - ty);
}

EdgeData& getEdgeRef(int x1, int y1, int x2, int y2) {
    // 只允許走一步
    if (abs(x1 - x2) + abs(y1 - y2) != 1) {
        cerr << "getEdgeRef: non-adjacent move (" << x1 << "," << y1
             << ") -> (" << x2 << "," << y2 << ")\n";
        exit(1);
    }

    if (y1 == y2) {
        // horizontal move: (x,y) <-> (x+1,y)
        int x = min(x1, x2);  // x in [0..GRID_C-2]
        return horizEdges[x][y1];
    } else {
        // vertical move: (x,y) <-> (x,y+1)
        int y = min(y1, y2);  // y in [0..GRID_R-2]
        return vertEdges[x1][y];
    }
}

inline double gcost(int cur_x, int cur_y, int next_x, int next_y,
                    double ALPHA, double BETA,
                    bool forbidOverflow)
{
    EdgeData &e = getEdgeRef(cur_x, cur_y, next_x, next_y);

    // 若你要「不允許 overflow」：走這一步會讓 demand+1 > cap 就禁止
    if (forbidOverflow && e.demand + 1 > e.cap) {
        return numeric_limits<double>::infinity();
    }

    // 避免 cap=0 除零（理論上不該發生，但保險）
    double cap = (double)max(1, e.cap);

    // 你原本的 util：用 demand+1 評估「我走上去」後的擁塞程度
    double util = (double)(e.demand + 1) / cap;

    // 單步成本：長度 1 + 擁塞懲罰 + 歷史懲罰
    return 1.0 + ALPHA * util + BETA * e.history;
}

using Path = vector<pair<int,int>>;

inline void apply_path_demand(const Path& path) {
    for (size_t i = 1; i < path.size(); ++i) {
        auto [x1,y1] = path[i-1];
        auto [x2,y2] = path[i];
        getEdgeRef(x1,y1,x2,y2).demand += 1;
    }
}

long long compute_total_overflow() {
    long long of = 0;

    // horizontal edges: (GRID_C-1) x GRID_R
    for (int x = 0; x < GRID_C - 1; ++x) {
        for (int y = 0; y < GRID_R; ++y) {
            const EdgeData &e = horizEdges[x][y];
            if (e.demand > e.cap) of += (e.demand - e.cap);
        }
    }

    // vertical edges: GRID_C x (GRID_R-1)
    for (int x = 0; x < GRID_C; ++x) {
        for (int y = 0; y < GRID_R - 1; ++y) {
            const EdgeData &e = vertEdges[x][y];
            if (e.demand > e.cap) of += (e.demand - e.cap);
        }
    }

    return of;
}

long long compute_total_wirelength(const vector<vector<pair<int,int>>> &all_paths) {
    long long wl = 0;
    for (const auto &path : all_paths) {
        if (path.size() >= 2) wl += (long long)(path.size() - 1);
    }
    return wl;
}

Stats evaluateSolution(const vector<vector<pair<int,int>>> &all_paths) {
    Stats s;
    s.wirelength = compute_total_wirelength(all_paths);
    s.overflow   = compute_total_overflow();
    return s;
}

void reset_all_demands() {
    for (int x = 0; x < GRID_C - 1; ++x)
        for (int y = 0; y < GRID_R; ++y)
            horizEdges[x][y].demand = 0;

    for (int x = 0; x < GRID_C; ++x)
        for (int y = 0; y < GRID_R - 1; ++y)
            vertEdges[x][y].demand = 0;
}

void update_history_from_overflow() {
    for (int x = 0; x < GRID_C - 1; ++x) {
        for (int y = 0; y < GRID_R; ++y) {
            auto &e = horizEdges[x][y];
            int of = max(0, e.demand - e.cap);
            if (of > 0) e.history += of;
        }
    }
    for (int x = 0; x < GRID_C; ++x) {
        for (int y = 0; y < GRID_R - 1; ++y) {
            auto &e = vertEdges[x][y];
            int of = max(0, e.demand - e.cap);
            if (of > 0) e.history += of;
        }
    }
}




Path astar_route_one_net(int sx, int sy, int tx, int ty,
                         double ALPHA, double BETA,
                         bool forbidOverflow,
                         bool debug_print_g_h_f)
{
    const double INF = 1e30;

    // gScore[x][y] = g(x)
    vector<vector<double>> gScore(GRID_C, vector<double>(GRID_R, INF));
    // closed[x][y] = 是否已 finalized
    vector<vector<char>> closed(GRID_C, vector<char>(GRID_R, 0));
    // parent[x][y] = 走到 (x,y) 的前一格，用於回溯
    vector<vector<pair<int,int>>> parent(GRID_C, vector<pair<int,int>>(GRID_R, {-1,-1}));

    priority_queue<PQNode> pq;

    gScore[sx][sy] = 0.0;
    double h0 = (double)manhattan(sx, sy, tx, ty);
    pq.push({sx, sy, 0.0, 0.0 + h0}); // f = g + h

    int dir_x[4] = {1, -1, 0, 0};
    int dir_y[4] = {0, 0, 1, -1};

    while (!pq.empty()) {
        PQNode cur = pq.top(); pq.pop();
        int x = cur.x, y = cur.y;

        if (closed[x][y]) continue;
        closed[x][y] = 1;

        // 這裡「看到」g(x)+h(x)
        if (debug_print_g_h_f) {
            double g = gScore[x][y];
            double h = (double)manhattan(x, y, tx, ty);
            double f = g + h;
            cerr << "[POP] (" << x << "," << y << ") "
                 << "g=" << g << " h=" << h << " f=g+h=" << f << "\n";
        }

        // 到終點：回溯路徑
        if (x == tx && y == ty) {
            Path path;
            int cx = tx, cy = ty;
            while (!(cx == sx && cy == sy)) {
                path.push_back({cx, cy});
                auto p = parent[cx][cy];
                cx = p.first;
                cy = p.second;
                if (cx == -1) { // 保險
                    return {};
                }
            }
            path.push_back({sx, sy});
            reverse(path.begin(), path.end());
            return path;
        }

        // 展開 4 鄰居
        for (int d = 0; d < 4; ++d) {
            int nx = x + dir_x[d];
            int ny = y + dir_y[d];

            if (nx < 0 || nx >= GRID_C || ny < 0 || ny >= GRID_R) continue;
            if (closed[nx][ny]) continue;

            // 單步 cost
            double step = gcost(x, y, nx, ny, ALPHA, BETA, forbidOverflow);
            if (!isfinite(step)) continue; // forbidOverflow=true 會用到

            double ng = gScore[x][y] + step;
            if (ng < gScore[nx][ny]) {
                gScore[nx][ny] = ng;
                parent[nx][ny] = {x, y};

                double h = (double)manhattan(nx, ny, tx, ty);
                double nf = ng + h; // f = g + h

                pq.push({nx, ny, ng, nf});
            }
        }
    }
    cout << "A* failed to find a path from ("
         << sx << "," << sy << ") to ("
         << tx << "," << ty << ")\n";
    return {}; // 找不到路
}

vector<vector<pair<int,int>>> all_paths; // 全域或回傳都可

void Astar_search() {
    const int MAX_ITER = 10;
    const double ALPHA = 5.0;
    const double BETA  = 1.0;
    const bool forbidOverflow = false; // 跟 hw4 一樣，先允許爆

    vector<vector<pair<int,int>>> best_paths;
    Stats best_stats;
    best_stats.overflow   = LLONG_MAX;
    best_stats.wirelength = LLONG_MAX;

    for (int iter = 0; iter < MAX_ITER; ++iter) {
        cerr << "=== Iteration " << iter << " ===\n";

        // 1) reset demand
        reset_all_demands();

        vector<vector<pair<int,int>>> cur_paths(netlist.size());

        // 2) route all nets
        for (int i = 0; i < (int)netlist.size(); ++i) {
            int sx = netlist[i].pin1.x, sy = netlist[i].pin1.y;
            int tx = netlist[i].pin2.x, ty = netlist[i].pin2.y;

            Path path = astar_route_one_net(
                sx, sy, tx, ty,
                ALPHA, BETA,
                forbidOverflow,
                false
            );

            // hw4-style fallback：一定給一條路
         

            cur_paths[i] = path;
            apply_path_demand(path);
        }

        // 3) evaluate
        Stats st = evaluateSolution(cur_paths);
        cerr << "wirelength=" << st.wirelength
             << " overflow=" << st.overflow << "\n";

        // 4) keep best
        if (st.overflow < best_stats.overflow ||
           (st.overflow == best_stats.overflow &&
            st.wirelength < best_stats.wirelength)) {
            best_stats = st;
            best_paths = cur_paths;
        }

        // 5) update history
        update_history_from_overflow();

        if (best_stats.overflow == 0) {
            cerr << "Zero overflow reached, stop early.\n";
            break;
        }
    }

    all_paths = best_paths;
    cerr << "=== FINAL ===\n";
    cerr << "Best wirelength = " << best_stats.wirelength << "\n";
    cerr << "Best overflow   = " << best_stats.overflow << "\n";
}



vector<Segment> compress_to_segments(const Path& path) {
    vector<Segment> segs;
    if (path.size() < 2) return segs;

    int sx = path[0].first, sy = path[0].second;
    int px = path[1].first, py = path[1].second;

    int dx = px - sx;
    int dy = py - sy;

    // 一段 segment 的起點
    int seg_x1 = sx, seg_y1 = sy;

    for (size_t i = 2; i < path.size(); ++i) {
        int cx = path[i].first, cy = path[i].second;
        int ndx = cx - px;
        int ndy = cy - py;

        // 方向改變 -> 關閉上一段
        if (ndx != dx || ndy != dy) {
            segs.push_back({seg_x1, seg_y1, px, py});
            seg_x1 = px; seg_y1 = py;
            dx = ndx; dy = ndy;
        }

        px = cx; py = cy;
    }

    // 最後一段
    segs.push_back({seg_x1, seg_y1, px, py});
    return segs;
}

void outputSolution(const string& outFile,
                    const vector<vector<pair<int,int>>>& all_paths)
{
    ofstream fout(outFile);
    if (!fout) {
        cerr << "Cannot open output file: " << outFile << "\n";
        exit(1);
    }

    Stats st = evaluateSolution(all_paths);
    fout << "Wirelength " << st.wirelength << "\n";

    for (int i = 0; i < (int)netlist.size(); ++i) {
        fout << "Net " << netlist[i].netname << "\n";

        const auto& path = all_paths[i];
        if (path.size() < 2) continue;  // 沒路或只有一點就不輸出 segment

        auto segs = compress_to_segments(path);
        for (const auto& s : segs) {
            fout << "Segment " << s.x1 << " " << s.y1 << " "
                          << s.x2 << " " << s.y2 << "\n";
        }
    }

    fout.close();
}

void parseInput(string &inFile, unordered_map<string, int> &netMap)
{
    ifstream fin(inFile);
    if (!fin)
    {
        cerr << "Cannot open input file: " << inFile << endl;
        exit(1);
    }
    string line;
    string name;
    int numNets = 0;
    while (getline(fin, line))
    {
        std::istringstream info(line);
        info >> name;
        if (name == "Grid")
        {
            info >> GRID_C >> GRID_R;
        }
        if (name == "Capacity")
        {
            info >> H_CAP >> V_CAP;
        }
        if (name == "NumNets")
        {
            info >> numNets;
            netlist.reserve(numNets);
            break;
        }
    }
    for (int i = 0; i < numNets; i++)
    {
        getline(fin, line);
        std::istringstream netinfo(line);
        string temp;
        string netname;
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
                std::istringstream pininfo(line);
                string pintemp;
                string pinname;
                int x, y;
                pininfo >> pintemp;
                if (pintemp == "Pin")
                {
                    pininfo >> pinname >> x >> y;
                    Pin newpin;
                    newpin.name = pinname;
                    newpin.x = x;
                    newpin.y = y;
                    if (j == 0)
                    {
                        newnet.pin1 = newpin;
                        netlist.push_back(newnet);
                    }
                    if (j == 1)
                    {
                        newnet.pin2 = newpin;
                        netlist[i] = newnet;
                    }
                }
            }
        }
    }
    horizEdges.assign(GRID_C-1, vector<EdgeData>(GRID_R));
    vertEdges.assign(GRID_C, vector<EdgeData>(GRID_R-1));

    for(int y=0; y<GRID_R; ++y)
        for(int x=0; x<GRID_C-1; ++x)
            horizEdges[x][y].cap = H_CAP;
    for(int y=0; y<GRID_R-1; ++y)
        for(int x=0; x<GRID_C; ++x)
            vertEdges[x][y].cap = V_CAP;
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        cerr << "Usage: " << argv[0] << " <input_file> <output_file>\n";
        return 1;
    }

    string inFile  = argv[1];
    string outFile = argv[2];

    unordered_map<string,int> netMap;
    parseInput(inFile, netMap);

    Astar_search();

    outputSolution(outFile, all_paths);
    return 0;
}
