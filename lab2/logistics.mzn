% finding the cheapest subgraph from start to dest in a graph
include "globals.mzn";


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

array[1..n_dests,1..graph_size] of var set of int: next;

% constraints

constraint forall(j in 1..n_dests, i in 1..graph_size)(
	next[j,i] =
	{to[x]   | x in 1..n_edges    where (from[x] == i /\ from[x] != dest[j])}
	union
	{from[x] | x in 1..n_edges    where (to[x] == i /\ to[x] != dest[j])}
	union
	{x       | x in 1..graph_size where (x == i /\ x != start /\ x != dest[j])}
	union
	{start   | x in 1..n_dests    where (dest[j] == i)}
);

array[1..n_dests, 1..graph_size] of var int: flatnext;

constraint forall(i in 1..n_dests, j in 1..graph_size) (flatnext[i,j] in next[i,j]);

constraint forall (i in 1..n_dests) (subcircuit([flatnext[i,j] | j in 1..graph_size]));

array[1..graph_size,1..graph_size] of var 0..1000: distance;

constraint forall(i in 1..graph_size)(distance[from[i],to[i]] = cost[i]);

constraint forall(i in 1..graph_size)(distance[to[i],from[i]] = cost[i]);

solve satisfy; %actually supposed to minimize the cost or whatever

var int: totalcost;
array[1..n_dests] of var int: sub_cost;

constraint forall(i in 1..n_dests)(
	sub_cost[i] = sum(j in 1..graph_size)(distance[j,flatnext[i,j]])
);

constraint totalcost = sum(j in 1..n_dests)(sub_cost[j]);

% output

%output["This is the output: ", show(subgraph)];
output["next     = ", show(next), "\n",
			 "flatnext = ", show(flatnext), "\n",
			 "distance = ", show(distance), "\n",
			 "sub_cost = ", show(sub_cost), "\n",
			 "totalcost = ", show(totalcost), "\n"];
