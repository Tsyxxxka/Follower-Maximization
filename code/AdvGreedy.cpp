#include <bits/stdc++.h>
using namespace std;
#define LL long long
#define LD long double
#define PII pair<int, int>
#define inf 0x3fffffff
#define INITIAL -1
mt19937 rand_num(2023);

unordered_map<int, int> id2name, name2id;
unordered_map<int, unordered_set<int>> graph;
vector<vector<int>> edge;
int n, m;
vector<int> core;
vector<int> shell_tag, total_order, order_pointer;
vector<pair<int, int>> shell_layer;
vector<int> anchor_tag;
int sc_num;
vector<int> id2sc, sc_vis, scC, scSize;
vector<vector<int>> scV, coreEEdge, coreELdge;
vector<int> shell_layer_order, scMaxLayer;
vector<int> upperBound, UBOrder, critical_tag;
vector<int> affected, numFollower;
vector<unordered_map<int, int>> followers;
unordered_map<int, int> scID;

void shellLayerDecomp()
{
    int max_degree = 0;
    shell_tag.clear();
    total_order.clear();
    shell_layer_order.clear();
    vector<vector<int>> bin;
    bin.resize(n + m);
    int bin_len = 0;
    for (int i = 0; i < n; i++)
        max_degree = max(max_degree, (int)edge[i].size());
    for (int i = 0; i < n; i++)
    {
        int degree = edge[i].size();
        core[i] = degree;
        order_pointer[i]=INITIAL;
        shell_layer[i]=make_pair(INITIAL, INITIAL);
        if (anchor_tag[i] == 1)
            core[i] = max_degree + edge[i].size();
        bin[core[i]].push_back(i);
        bin_len = max(bin_len, core[i]);
    }

    for (int i = 0; i <= bin_len; i++)
        for (auto x : bin[i])
            total_order.push_back(x);

    int bi = 0;
    for (int i = 0; i < total_order.size(); i++)
    {
        int id = total_order[i];
        int degree = core[id];
        order_pointer[id] = i;

        while (degree >= bi)
        {
            shell_tag.push_back(i);
            bi++;
        }
    }

    for (int i = 0; i < total_order.size(); i++)
    {
        int v = total_order[i];
        shell_layer_order.push_back(v);
        if (shell_layer[v].first < core[v])
        {
            shell_layer[v].first = core[v];
            shell_layer[v].second = 1;
        }
        else if (shell_layer[v].first == core[v])
        {
            shell_layer[v].second = shell_layer[v].second + 1;
        }

        for (int j = 0; j < edge[v].size(); j++)
        {
            int u = edge[v][j];
            if (core[u] > core[v])
            {
                int du = core[u];
                int pu = order_pointer[u];
                int pw = shell_tag[du];
                int w = total_order[pw];

                if (u != w)
                {
                    total_order[pu] = w;
                    total_order[pw] = u;
                    order_pointer[u] = pw;
                    order_pointer[w] = pu;
                }

                shell_tag[du]++;
                core[u]--;

                shell_layer[u].first = shell_layer[v].first;
                shell_layer[u].second = shell_layer[v].second;
            }
        }
    }
    coreEEdge.clear();
    coreEEdge.resize(n);
    coreELdge.clear();
    coreELdge.resize(n);
    critical_tag.clear();
    critical_tag.resize(n);
    for (int i = 0; i < n; i++)
    {
        critical_tag[i] = core[i] + 1;
        for (auto j : edge[i])
            if (core[j] == core[i])
            {
                coreEEdge[i].push_back(j);
                critical_tag[i]--;
                if (shell_layer[j] > shell_layer[i])
                    coreELdge[i].push_back(j);
            }
            else if (core[j] > core[i])
                critical_tag[i]--;
    }
}

void buildSC()
{
    vector<vector<int>> bin;
    bin.resize(n);
    sc_vis.clear();
    id2sc.clear();
    scC.clear();
    scV.clear();
    scMaxLayer.clear();
    scID.clear();
    sc_vis.resize(n);
    id2sc.resize(n);
    for (int i = 0; i < n; i++)
        bin[core[i]].push_back(i),
            sc_vis[i] = 0;
    sc_num = 0;
    for (int i = 0; i < n; i++)
        for (auto x : bin[i])
            if (sc_vis[x] == 0)
            {
                int id = -1, maxLayer = 0;
                scC.push_back(i);
                vector<int> vec;
                queue<int> Q;
                Q.push(x);
                sc_vis[x] = 1;
                while (!Q.empty())
                {
                    int u = Q.front();
                    vec.push_back(u);
                    id = max(id, u);
                    Q.pop();
                    for (auto v : edge[u])
                        if (sc_vis[v] == 0 && core[v] == core[u])
                            Q.push(v), sc_vis[v] = 1;
                }
                for (auto u : vec)
                    id2sc[u] = id, maxLayer = max(maxLayer, shell_layer[u].second);
                scID[id] = sc_num;
                scV.push_back(vec);
                scMaxLayer.push_back(maxLayer + 1);
                sc_num++;
            }
}

void computeUpperBound()
{
    UBOrder.clear();
    upperBound.clear();
    upperBound.resize(n);
    vector<int> upperBoundL, upperBoundE;
    upperBoundL.resize(n);
    upperBoundE.resize(n);
    vector<vector<int>> bin;
    bin.resize(n);
    for (auto it = shell_layer_order.rbegin(); it != shell_layer_order.rend(); it++)
    {
        int x = *it;
        if (anchor_tag[x] == 1)
            continue;
        unordered_map<int, int> shell_num;
        upperBoundL[x] = 0;
        if (affected[x] == 0)
            upperBoundE[x] = 1;
        else
            upperBoundE[x] = 0;
        for (auto ru : followers[x])
        {
            int id = ru.first, value = ru.second;
            if (id == id2sc[x])
                upperBoundE[x] += value;
            else
                upperBoundL[x] += value;
        }
        for (auto y : edge[x])
        {
            int id = id2sc[y];
            if (followers[x].find(id) != followers[x].end())
                continue;

            if (shell_layer[y].first > shell_layer[x].first && critical_tag[y] - 1 <= 0)
            {
                int t = scID[id2sc[y]];
                int num = shell_num[t];
                if (num == scV[t].size())
                    continue;
                if (num + upperBoundE[y] <= scV[t].size())
                    upperBoundL[x] += upperBoundE[y], shell_num[t] += upperBoundE[y];
                else
                    upperBoundL[x] = upperBoundL[x] - num + scV[t].size(), shell_num[t] = scV[t].size();
            }
            else if (shell_layer[y] > shell_layer[x] && critical_tag[y] <= 0)
            {
                int t = scID[id2sc[y]];
                int num = shell_num[t];
                if (num == scV[t].size())
                    continue;
                if (num + upperBoundE[y] <= scV[t].size())
                    upperBoundE[x] += upperBoundE[y], shell_num[t] += upperBoundE[y];
                else
                    upperBoundE[x] = upperBoundE[x] - num + scV[t].size(), shell_num[t] = scV[t].size();
            }
        }
        upperBound[x] = upperBoundL[x] + upperBoundE[x];
        bin[upperBound[x]].push_back(x);
    }
    for (int i = n - 1; i >= 0; i--)
        for (auto x : bin[i])
            UBOrder.push_back(x);
}

vector<int> score, vis, candidate_tag;

vector<unordered_map<int, vector<int>>> shellVec;
vector<vector<int>> vec;
vector<int> vec_len;
vector<LL> vec_tag;

void computeshellVec()
{
    shellVec.clear();
    // vec.clear();
    vec_len.clear();
    vec_tag.clear();
    shellVec.resize(n);
    // vec.resize(n);
    vec_len.resize(n);
    vec_tag.resize(n);
    for (int x = 0; x < n; x++)
    {
        for (auto y : edge[x])
        {
            if (anchor_tag[y] == 1)
                continue;
            if (shell_layer[y] > shell_layer[x] && followers[x].find(id2sc[y]) == followers[x].end())
                shellVec[x][id2sc[y]].push_back(y);
        }
    }
}

void insert_vec(int x, int l, LL tag)
{
    l--;
    // cout<<id2name[x]<<" "<<l<<" "<<tag<<" "<<vec_len[l]<<" "<<vec_tag[l]<<endl;
    if (vec_tag[l] != tag)
    {
        vec_len[l] = 0;
        vec_tag[l] = tag;
    }
    if (vec_len[l] < vec[l].size())
    {
        vec[l][vec_len[l]] = x;
        vec_len[l]++;
    }
    else
    {
        vec[l].push_back(x);
        vec_len[l]++;
    }
}

int computeFollower(int x)
{
    int tag = x + 1;
    unordered_set<int> shellid;

    for (auto y : edge[x])
    {
        if (core[y] > core[x])
            critical_tag[y]--;
        if (anchor_tag[y] == 1)
            continue;
        if (shell_layer[y] > shell_layer[x] && followers[x].find(id2sc[y]) == followers[x].end())
        {
            shellid.insert(id2sc[y]);
            // shellVec[id2sc[y]].push_back(y);
            vis[y] = tag;
        }
    }
    // // return 0;
    // puts("---------");
    // cout << id2name[x] << endl;
    for (auto it : shellid)
    {
        LL vectag=1LL * x * n + it + 1;
        int id = scID[it];
        int maxLayer = scMaxLayer[id], candidateSize = 0;
        // vec.clear();
        // vec.resize(maxLayer);
        for (auto u : shellVec[x][it])
        {
            insert_vec(u, shell_layer[u].second, vectag);
            vec[shell_layer[x].second].push_back(x);
        }
        for (int l = 0; l < maxLayer; l++)
        {
            // cout<<l<<" "<<vec_tag[l]<<" "<<1LL*x*n+it+1<<endl;
            if (vec_tag[l] == vectag)
            {
                int i = 0;
                candidate_tag[x] = tag;
                while (i < vec_len[l])
                {
                    double time1 = clock();
                    int u = vec[l][i];
                    if (affected[u] == 0)
                        candidateSize++;
                    score[u] = critical_tag[u];
                    for (auto v : coreEEdge[u])
                    {
                        if (v == x || anchor_tag[v] == 1)
                            continue;
                        if (candidate_tag[v] == -tag || (shell_layer[v] <= shell_layer[u] && vis[v] != tag))
                        {
                            score[u]++;
                            if (score[u] > 0)
                                break;
                        }
                    }
                    candidate_tag[u] = tag;

                    if (score[u] > 0)
                    {
                        queue<int> q;
                        q.push(u);
                        if (affected[u] == 0)
                            candidateSize--;
                        candidate_tag[u] = -tag;
                        while (!q.empty())
                        {
                            int u = q.front();
                            q.pop();
                            for (auto v : coreEEdge[u])
                                if (candidate_tag[v] == tag)
                                {
                                    if (v == x || anchor_tag[v] == 1)
                                        continue;
                                    score[v]++;
                                    if (score[v] == 1)
                                    {
                                        if (affected[v] == 0)
                                            candidateSize--;
                                        candidate_tag[v] = -tag;
                                        q.push(v);
                                    }
                                }
                        }
                        // removeCandidate(u, candidate_tag, score, tag, candidateSize, vis, x);
                        i++;

                        continue;
                    }

                    for (auto v : coreELdge[u])
                        if (vis[v] != tag)
                        {
                            vis[v] = tag;
                            insert_vec(v, shell_layer[v].second, vectag);
                            // vec[shell_layer[v].second].push_back(v);
                        }
                    i++;

                }
            }
        }
        //     cout << id2name[it] << " " << candidateSize << endl;

        // puts("---------");
        followers[x][it] = candidateSize;
        numFollower[x] += candidateSize;
    }

    for (auto y : edge[x])
    {
        if (core[y] > core[x])
            critical_tag[y]++;
    }

    if (affected[x] == 0)
        return numFollower[x] + 1;
    return numFollower[x];
}

void Reuse(int x)
{
    vector<int> id2scTMP;
    id2scTMP = id2sc;
    vector<PII> preshell_layer;
    preshell_layer.resize(n);
    for (int u = 0; u < n; u++)
        preshell_layer[u] = shell_layer[u];

    shellLayerDecomp();
    unordered_set<int> affectSC;
    for (int u = 0; u < n; u++)
    {
        if (shell_layer[u].first != preshell_layer[u].first)
            affected[u] = 1;
    }
    for (auto y : edge[x])
        if (preshell_layer[x] < preshell_layer[y])
        {
            affectSC.insert(scID[id2sc[y]]);
        }
    affectSC.insert(scID[id2sc[x]]);
    unordered_set<int> affectV;
    for (auto id : affectSC)
        for (auto u : scV[id])
            affectV.insert(u);
    for (auto u : affectV)
    {
        int id = id2sc[u];
        if (followers[u].find(id) != followers[u].end())
            numFollower[u] -= followers[u][id], followers[u].erase(id);
        for (auto v : edge[u])
            if (preshell_layer[v] < preshell_layer[u])
            {
                if (followers[v].find(id) != followers[v].end())
                    numFollower[v] -= followers[v][id], followers[v].erase(id);
            }
    }
    buildSC();

    unordered_set<int> newAffectSC;
    for (auto u : affectV)
        newAffectSC.insert(scID[id2sc[u]]);

    unordered_set<int> newAffectV;
    for (auto id : newAffectSC)
        for (auto u : scV[id])
            if (affectV.find(u) == affectV.end())
                newAffectV.insert(u);
    for (auto u : newAffectV)
    {
        int id = id2scTMP[u];
        if (followers[u].find(id) != followers[u].end())
            numFollower[u] -= followers[u][id], followers[u].erase(id);
        for (auto v : edge[u])
            if (preshell_layer[v] < preshell_layer[u])
            {
                if (followers[v].find(id) != followers[v].end())
                    numFollower[v] -= followers[v][id], followers[v].erase(id);
            }
    }
}

int main(int argc, char **argv)
{
    char input[100], output[100];
    int budget = atoi(argv[2]);
    sprintf(input, "../data/%s", argv[1]);
    sprintf(output, "../result/AdvGreedy-%s_b=%d", argv[1], budget);

    double begin_time = clock();
    ifstream in(input);
    ofstream out(output);
    n = 0;
    m = 0;
    int x, y;
    while (in >> x >> y)
    {
        if (name2id.find(x) == name2id.end())
            name2id[x] = n, id2name[n] = x, n++;
        if (name2id.find(y) == name2id.end())
            name2id[y] = n, id2name[n] = y, n++;
        x = name2id[x];
        y = name2id[y];
        graph[x].insert(y);
        graph[y].insert(x);
    }
    edge.resize(n);
    for (int x = 0; x < n; x++)
        for (auto y : graph[x])
            edge[x].push_back(y), m++;
    graph.clear();
    m /= 2;
    out << "#vertices: " << n << "\t#edges:" << m << endl;
    double end_time = clock();
    out << "finish reading graph, time: " << (end_time - begin_time) / CLOCKS_PER_SEC << endl;
    
    begin_time = clock();

    anchor_tag.resize(n);
    vec.resize(n);
    core.resize(n);
    shell_layer.resize(n);
    order_pointer.resize(n);

    shellLayerDecomp();
    buildSC();

    vector<int> preCore;
    preCore.resize(n);
    for (int i = 0; i < n; i++)
        preCore[i] = core[i];

    affected.resize(n);
    followers.resize(n);
    numFollower.resize(n);
    
    computeshellVec();
    end_time = clock();
    out << "finish building index, time: " << (end_time - begin_time) / CLOCKS_PER_SEC << endl;
    
    begin_time = clock();

    int sumNum = 0;
    for (int i = 1; i <= budget; i++)
    {

        score.clear();
        vis.clear();
        candidate_tag.clear();
        score.resize(n);
        vis.resize(n);
        candidate_tag.resize(n);
        vector<int> affectSC;
        computeUpperBound();
        double endtime;

        int anchor = 0, followerNum = 0;
        for (int x : UBOrder) {
            if (upperBound[x] > followerNum)
            {
                int num = computeFollower(x);
                if (num > followerNum) {
                    followerNum = num, anchor = x;
                }
            }
            else {
                break;
            }
        }
        endtime = clock();
        anchor_tag[anchor] = 1;
        sumNum += followerNum;
        Reuse(anchor);
        computeshellVec();
        end_time = clock();
        out << i << "\t" << id2name[anchor] << "\t" << sumNum << "\t" << (end_time - begin_time) / CLOCKS_PER_SEC << endl;
    }

    end_time = clock();
    out << "finish, time: " << (end_time - begin_time) / CLOCKS_PER_SEC << endl;

    return 0;
}
