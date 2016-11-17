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

array[1..n_dests,1..graph_size] of var set of int: next;

% constraints

constraint forall(j in 1..n_dests, i in 1..graph_size)(
	next[j,i] =
	{to[x]   | x in 1..n_edges    where from[x] == i}
	union
	{from[x] | x in 1..n_edges    where (to[x] == i /\ to[x] != dest[j])}
	union
	{x       | x in 1..graph_size where (x == i /\ x != start /\ x != dest[j])}
	union
	{start   | x in 1..n_dests    where dest[x] == i }
);

%constraint next[dest[1]] = {start};

% add edge from end to start... (add `dest[i]' to `from' and `start' to `to' for all i in `n_dest')
%%constraint forall(i in 1..n_dests)(from[graph_size+1] = dest[i] /\ to[graph_size+1] = start);

% change domain of end node to only `start', maybe like this...
%%constraint forall(i in 1..n_dests)(forall(j in 1..graph_size)(if from[j] = dest[i] /\ to[j] != start then from[j] = 0 /\ to[j] = 0 else true endif));

% remove start from start-domain
%%constraint forall(i in 1..graph_size)(if to[i] = start /\ from[i] = start then to[i] = 0 /\ from [i] = 0 else true endif);

% value-graph:
%array[1..graph_size*graph_size] of var int: v;

%v[i,x[i]] = d[i]
%constraint forall(i in 1..graph_size)(v[to[i],from[i]] = cost[i]);

% subcircuit(1-5) will find all paths, we then need to pick the cheapest.
%constraint subcircuit.... somehow...
%constraint subcircuit(v);

% element constraint to see cost
% element(l,[1,2,3],V) means V = List[I]
%constraint forall(1 in 1..)(element(1,[],v));
%constraint subgraph = something;

% if from[i] == start: go to cheapest
%constraint forall(i in n_dests)()

% cost = sum of costs for subgraph
%var int: totalcost = sum(i in 1..subgraph_size)(subgraph[i]);

% solve

solve maximize graph_size;

% output

%output["This is the output: ", show(subgraph)];
output["next     =", show(next), "\n"];
