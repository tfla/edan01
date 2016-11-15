% finding the cheapest subgraph from start to dest in a graph

% parameters

int: graph_size;
int: start;
int: n_dests;
int: n_edges;
array[int] of int: dest;
array[int] of int: from;
array[int] of int: to;
array[int] of int: cost;

% decision variables

%array[int,int] of int: t;
%t = [| 0,  4, 2,  0,  0, 0,  0,
%		 | 4,  0, 5, 10,  0, 0,  0,
%		 | 2,  5, 0,  0,  3, 0,  0,
%		 | 0, 10, 0,  0,  0, 4, 11,
%		 | 0,  0, 3,  4,  0, 0,  0,
%		 | 0,  0, 0,  0, 11, 0,  0 |];

%array[1..graph_size,1..graph_size] of var int: graph;

% constraints

% if start[i,j] > 0 then puzzle[i,j] = start[i,j] else	true	endif
% 
%%constraint forall(i in 1..graph_size)(forall(j in 1..graph_size)( graph[i,j] = cost[i]) ); 
%%constraint forall(i in 1..graph_size)(forall(j in 1..graph_size)(if to[i] = from[j] then graph[i,j] = cost[i] else true endif));

%array[1..graph_size] of var 0..graph_size: subgraph;

% add edge from end to start... (add `dest[i]' to `from' and `start' to `to' for all i in `n_dest')
constraint forall(i in 1..n_dests)(from[graph_size+1] = dest[i] /\ to[graph_size+1] = start);

% change domain of end node to only `start', maybe like this...
constraint forall(i in 1..n_dests)(forall(j in 1..graph_size)(if from[j] = dest[i] /\ to[j] != start then  from[j] = 0 /\ to[j] = 0 endif));

% remove start from start-domain
constraint forall(i in 1..graph_size)(if to[i] = start /\ from[i] = start then to[i] = 0 /\ from [i] = 0 endif);

% subcircuit(1-5) will find all paths, we then need to pick the cheapest.
%constraint subcircuit.... somehow...

% element constraint to see cost
% element(l,[1,2,3],V)
%constraint subgraph = something;

% if from[i] == start: go to cheapest
%constraint forall(i in n_dests)()

% cost = sum of costs for subgraph
%var int: totalcost = sum(i in 1..subgraph_size)(subgraph[i]);

% solve

solve maximize graph_size;

% output

%output["This is the output: ", show(subgraph)];
output["graph =", show(graph), "\n",
			 "test  =", show(t), "\n"];
