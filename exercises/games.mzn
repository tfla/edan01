% playing games at a block party in brooklyn

int: num;
int: cap;
int: refill;
array[0..num] of int: fun;
array[0..num] of int: games;
array[0..num] of int: tokens;

constraint assert(num >= 0, "Invalid datafile: " ++
									"Number of games is negative.");

constraint assert(cap >= 0, "Invalid datafile: " ++
									"Token capacity is negative.");

constraint assert(refill >= 0, "Invalid datafile: " ++
									"Token refill is negative.");

constraint forall(i in 0..num-1)(games[i] <= tokens[i]);

constraint forall(i in 0..num-1)(tokens[i-1] = tokens[i]+games[i-1]-refill);

solve :: int_search(fun, first_fail, indomain_min, complete)
			satisfy;


