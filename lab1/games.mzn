% playing games at a block party in brooklyn
include "globals.mzn";

% params and vars
int: num;
int: cap;
int: refill;
array[int] of int: fun;

array[1..num] of var 0..cap: tokens;
array[1..num] of var 0..cap: visits;


% at most cap tokens
constraint tokens[1] = cap;

% tokens = min(T_in = T_in-1 - V_in-1 + refill, cap)
constraint forall (i in 2..num) (minimum(tokens[i], [tokens[i-1] - visits[i-1] + refill, cap]));
			
% V_i less than or equal T_i ( AND V_i > 0 if noskip )
constraint forall (i in 1..num) ((visits[i] <= tokens[i]));  %/\ (visits[i] > 0));

% 0 < visits < 1
constraint at_most(1, visits, 0);

% totalfun equals linear combination of visits and fun
var int: totalfun = sum(i in 1..num) (visits[i]*fun[i]);

% maximise totalfun
solve maximize totalfun;

% show totalfun
output ["totalfun = ", show(totalfun)];
