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

using namespace std;
using Clock = std::chrono::high_resolution_clock;

// --- 結構定義 ---
struct Pin
{
    string name;
    int x, y;
};
struct nets
{
    string netname;
    Pin pin1, pin2;
};
struct EdgeData
{
    int cap = 0;
    int demand = 0;
    double history = 1.0; // 歷史代價基礎值為 1
};
struct PQNode
{
    int x, y, prev_x, prev_y;
    double g, f;
    bool operator<(const PQNode &o) const { return f > o.f; }
};
struct Segment
{
    int x1, y1, x2, y2;
};

// --- 全域變數 ---
int GRID_C = 0, GRID_R = 0, H_CAP = 0, V_CAP = 0;
vector<nets> netlist;
vector<vector<EdgeData>> horizEdges, vertEdges;
using Path = vector<pair<int, int>>;
vector<Path> all_paths;
long long TOTAL_OVERFLOW = 0, TOTAL_WL = 0;

// --- 輔助函式 ---
inline EdgeData &getEdgeRef(int x1, int y1, int x2, int y2)
{
    if (y1 == y2)
        return horizEdges[min(x1, x2)][y1];
    else
        return vertEdges[x1][min(y1, y2)];
}
inline int edge_overflow(const EdgeData &e) { return (e.demand > e.cap) ? (e.demand - e.cap) : 0; }
inline int manhattan(int x, int y, int tx, int ty) { return abs(x - tx) + abs(y - ty); }
inline long long path_wirelength(const Path &p) { return (p.size() >= 2) ? (long long)(p.size() - 1) : 0LL; }

void apply_path_demand(const Path &path)
{
    for (size_t i = 1; i < path.size(); ++i)
    {
        EdgeData &e = getEdgeRef(path[i - 1].first, path[i - 1].second, path[i].first, path[i].second);
        int old_of = edge_overflow(e);
        e.demand++;
        TOTAL_OVERFLOW += (edge_overflow(e) - old_of);
    }
}

void remove_path_demand(const Path &path)
{
    for (size_t i = 1; i < path.size(); ++i)
    {
        EdgeData &e = getEdgeRef(path[i - 1].first, path[i - 1].second, path[i].first, path[i].second);
        int old_of = edge_overflow(e);
        e.demand--;
        TOTAL_OVERFLOW += (edge_overflow(e) - old_of);
    }
}

// --- A* 搜尋演算法 (含歷史代價與動態視窗) ---
Path astar_route(int sx, int sy, int tx, int ty, double h_weight, int window_ext, bool forbid)
{
    priority_queue<PQNode> pq;
    unordered_map<int, double> gScore;
    unordered_map<int, pair<int, int>> parent;

    int start_id = sx * GRID_R + sy;
    gScore[start_id] = 0.0;
    pq.push({sx, sy, sx, sy, 0.0, (double)manhattan(sx, sy, tx, ty)});

    int dx[] = {1, -1, 0, 0}, dy[] = {0, 0, 1, -1};
    int minX = max(0, min(sx, tx) - window_ext), maxX = min(GRID_C - 1, max(sx, tx) + window_ext);
    int minY = max(0, min(sy, ty) - window_ext), maxY = min(GRID_R - 1, max(sy, ty) + window_ext);

    while (!pq.empty())
    {
        PQNode curr = pq.top();
        pq.pop();
        if (curr.x == tx && curr.y == ty)
        {
            Path p;
            pair<int, int> c = {tx, ty};
            while (!(c.first == sx && c.second == sy))
            {
                p.push_back(c);
                c = parent[c.first * GRID_R + c.second];
            }
            p.push_back({sx, sy});
            reverse(p.begin(), p.end());
            return p;
        }
        if (curr.g > gScore[curr.x * GRID_R + curr.y])
            continue;

        for (int i = 0; i < 4; ++i)
        {
            int nx = curr.x + dx[i], ny = curr.y + dy[i];
            if (nx < minX || nx > maxX || ny < minY || ny > maxY)
                continue;

            EdgeData &e = getEdgeRef(curr.x, curr.y, nx, ny);
            if (forbid && e.demand >= e.cap)
                continue;

            // Negotiated Congestion Cost Function:
            // Cost = Base_Cost(1) + Congestion_Penalty * History_Penalty
            double congestion = (double)e.demand / (double)max(1, e.cap);
            double cost = 1.0 + (congestion * e.history * h_weight);

            // 微小轉角懲罰 (0.01) 用於拉直路徑
            if (!(curr.x == sx && curr.y == sy) && (nx != curr.prev_x && ny != curr.prev_y))
                cost += 0.01;

            double next_g = curr.g + cost;
            int nid = nx * GRID_R + ny;
            if (gScore.find(nid) == gScore.end() || next_g < gScore[nid])
            {
                gScore[nid] = next_g;
                parent[nid] = {curr.x, curr.y};
                pq.push({nx, ny, curr.x, curr.y, next_g, next_g + manhattan(nx, ny, tx, ty)});
            }
        }
    }
    return {};
}


void solve_routing()
{
    all_paths.assign(netlist.size(), {});

    // 1. 初始佈線
    for (int i = 0; i < (int)netlist.size(); ++i)
    {
        Path p = astar_route(netlist[i].pin1.x, netlist[i].pin1.y, netlist[i].pin2.x, netlist[i].pin2.y, 0.5, 10, false);
        all_paths[i] = p;
        apply_path_demand(p);
    }

    // 2. Negotiated Congestion 迭代 (消除 Overflow)
    double h_weight = 1.5;
    for (int iter = 0; iter < 100; ++iter)
    {
        // 每一輪開始前，先計算目前的總線長
        long long current_iter_wl = 0;
        for (const auto &p : all_paths)
            current_iter_wl += path_wirelength(p);

        cout << "Iter " << iter << " | Wirelength: " << current_iter_wl << " | Overflow: " << TOTAL_OVERFLOW << endl;

        if (TOTAL_OVERFLOW == 0)
            break;

        // 更新歷史代價：對於目前仍溢出的邊，增加其歷史權重
        for (auto &row : horizEdges)
            for (auto &e : row)
                if (e.demand > e.cap)
                    e.history += 1.0;
        for (auto &row : vertEdges)
            for (auto &e : row)
                if (e.demand > e.cap)
                    e.history += 1.0;

        for (int i = 0; i < (int)netlist.size(); ++i)
        {
            bool on_overflow = false;
            for (size_t j = 1; j < all_paths[i].size(); ++j)
            {
                if (edge_overflow(getEdgeRef(all_paths[i][j - 1].first, all_paths[i][j - 1].second, all_paths[i][j].first, all_paths[i][j].second)) > 0)
                {
                    on_overflow = true;
                    break;
                }
            }

            if (on_overflow)
            {
                remove_path_demand(all_paths[i]);
                // 如果失敗，則擴大搜尋視窗
                Path np = astar_route(netlist[i].pin1.x, netlist[i].pin1.y, netlist[i].pin2.x, netlist[i].pin2.y, h_weight, 5 + iter / 10, false);
                if (!np.empty())
                    all_paths[i] = np;
                apply_path_demand(all_paths[i]);
            }
        }
        h_weight += 0.5; // 逐漸增加擁塞懲罰
    }

    // 3. 線長優化 (Polish) - 在 OF=0 的前提下尋找更短路徑
    if (TOTAL_OVERFLOW == 0)
    {
        cout << "--- Starting Polish Phase (OF=0) ---" << endl;
        for (int r = 0; r < 10; ++r)
        {
            for (int i = 0; i < (int)netlist.size(); ++i)
            {
                long long cur_wl = path_wirelength(all_paths[i]);
                if (cur_wl <= manhattan(netlist[i].pin1.x, netlist[i].pin1.y, netlist[i].pin2.x, netlist[i].pin2.y))
                    continue;

                remove_path_demand(all_paths[i]);
                Path np = astar_route(netlist[i].pin1.x, netlist[i].pin1.y, netlist[i].pin2.x, netlist[i].pin2.y, 0.0, 50, true);
                if (!np.empty() && path_wirelength(np) < cur_wl)
                    all_paths[i] = np;
                apply_path_demand(all_paths[i]);
            }
            // Polish 期間也即時顯示線長變化
            long long polish_wl = 0;
            for (const auto &p : all_paths)
                polish_wl += path_wirelength(p);
            cout << "Polish Round " << r << " | Wirelength: " << polish_wl << endl;
        }
    }

    TOTAL_WL = 0;
    for (const auto &p : all_paths)
        TOTAL_WL += path_wirelength(p);
}

// --- 輸出與解析 (保持原結構) ---
vector<Segment> compress_to_segments(const Path &path)
{
    vector<Segment> segs;
    if (path.size() < 2)
        return segs;
    int sx = path[0].first, sy = path[0].second, px = path[1].first, py = path[1].second;
    int dx = px - sx, dy = py - sy, seg_x1 = sx, seg_y1 = sy;
    for (size_t i = 2; i < path.size(); ++i)
    {
        int cx = path[i].first, cy = path[i].second, ndx = cx - px, ndy = cy - py;
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

void outputSolution(const string &outFile)
{
    ofstream fout(outFile);
    fout << "Wirelength " << TOTAL_WL << "\n";
    for (int i = 0; i < (int)netlist.size(); ++i)
    {
        fout << "Net " << netlist[i].netname << "\n";
        auto segs = compress_to_segments(all_paths[i]);
        for (const auto &s : segs)
            fout << "Segment " << s.x1 << " " << s.y1 << " " << s.x2 << " " << s.y2 << "\n";
    }
}

void parseInput(const string &inFile)
{
    ifstream fin(inFile);
    string line, name;
    int numNets = 0;
    while (getline(fin, line))
    {
        istringstream info(line);
        info >> name;
        if (name == "Grid")
            info >> GRID_C >> GRID_R;
        else if (name == "Capacity")
            info >> H_CAP >> V_CAP;
        else if (name == "NumNets")
        {
            info >> numNets;
            break;
        }
    }
    for (int i = 0; i < numNets; i++)
    {
        getline(fin, line);
        istringstream netinfo(line);
        string temp, netname;
        int pinCount;
        netinfo >> temp >> netname >> pinCount;
        nets n;
        n.netname = netname;
        for (int j = 0; j < pinCount; j++)
        {
            getline(fin, line);
            istringstream pininfo(line);
            string pt, pn;
            int x, y;
            pininfo >> pt >> pn >> x >> y;
            if (j == 0)
                n.pin1 = {pn, x, y};
            else
                n.pin2 = {pn, x, y};
        }
        netlist.push_back(n);
    }
    horizEdges.assign(GRID_C - 1, vector<EdgeData>(GRID_R, {H_CAP, 0, 1.0}));
    vertEdges.assign(GRID_C, vector<EdgeData>(GRID_R - 1, {V_CAP, 0, 1.0}));
}

int main(int argc, char *argv[])
{
    if (argc != 3)
        return 1;
    parseInput(argv[1]);
    solve_routing();
    outputSolution(argv[2]);
    cout << "Final Results -> Wirelength: " << TOTAL_WL << " | Overflow: " << TOTAL_OVERFLOW << endl;
    return 0;
}
