% finding the cheapest subgraph from start to dest in a graph

int: graph_size;
int: start;
int: n_dests;
array[int] of int: dest;
array[int] of int: from;
array[int] of int: to;
array[int] of int: cost;

array[1..graph_size] of var 0..graph_size: subgraph;

%constraint subgraph = something;

% if from[i] == start: go to cheapest
%constraint forall(i in n_dests)()

% cost = sum of costs for subgraph
%var int: totalcost = sum(i in 1..subgraph_size)(subgraph[i]);

%output["This is the output: ", show(subgraph)];
