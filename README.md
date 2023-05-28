Thanks for your attention. This is the source code of our VLDB submission "Network Resilience Reinforcement via Vertex Anchoring".

# Experimental Environment

The experiments are performed on a CentOS Linux serve (Release 7.5.1804) with Quad-Core Intel Xeon CPU (E5-2640 v4 @ 2.20GHz) and 128G memory. All the algorithms are implemented in C++17. The source code is compiled by GCC (10.2.1) under the -O3 optimization.

# Datasets

The experiments are conducted on 8 datasets, obtained from SNAP (http://snap.stanford.edu) and KONECT (http://konect.cc/networks/):
* Arxiv: https://snap.stanford.edu/data/cit-HepPh.html;
* Gowalla: https://snap.stanford.edu/data/loc-Gowalla.html;
* Notredame: https://snap.stanford.edu/data/web-NotreDame.html;
* Stanford: https://snap.stanford.edu/data/web-Stanford.html;
* Youtube: https://snap.stanford.edu/data/com-Youtube.html;
* Wiki: http://konect.cc/networks/wikipedia_link_hy;
* Livejournal: https://snap.stanford.edu/data/com-LiveJournal.html;
* Orkut: https://snap.stanford.edu/data/com-Orkut.html.

# Codes

* **AdvGAC**: Greedily select the best anchor from pruned candidates in each of the $b$ iterations, based on the shell component structure, accelerating by reusing the intermediate results and applying the upper bound technique.

* **Time-dependent Search Framework**: Greedy-based search framework based on a search tree, with effective pruning strategies, aiming to quickly produce a solution and continue to discover better solutions if time permits. It can be extended to use other heuristics by simply modifying the code. 


# Compile

```shell
cd code
g++ -o AdvGAC AdvGAC.cpp -std=c++17 -O3
g++ -o search search.cpp -std=c++17 -O3
```
# Run

## DataGraph

Save datasets in `./data`, e.g., `./data/gowalla`.

Each line in the input file contains two integers `u v`, which means there exists one edge (u,v) in the input graph.

## Run code

For AdvGAC, we run the code by inputing the name of the graph file and the budget, e.g. , we run the code on Gowalla with budget=100 as follows.

```shell
./AdvGAC gowalla 100
```
For the search framework, we run the search code by inputing the graph file name, the budget and the parameter $\lambda$. To redirect the output to a file, we need to use the command nohup, and an example is as follows.

```shell
nohup ./search gowalla 100 1 > search-gowalla_b=100_l=1 &
```

## Output

The experiment results will be saved in `./results`, e.g., `./results/AdvGAC-gowalla_b=100`. For AdvGAC, the chosen best anchor, the resilience gain and the running time will be printed for each iteration. For the search framework, we will print these infomation every time we discover a new solution. 
