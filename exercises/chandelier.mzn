include "alldifferent.mzn";

% balancing a chandelier
var 1..9: a;
var 1..9: b;
var 1..9: c;
var 1..9: d;
var 1..9: e;
var 1..9: f;
var 1..9: g;
var 1..9: h;
var 1..9: i;

% only one of each weight
constraint all_different([a,b,c,d,e,f,g,h,i]);

% constraints, using principle of lever
constraint 2*a = b+2*c;
constraint 2*d+e = f;
constraint 2*g+h = 3*i;
constraint 3*(a+b+c) = 2*(d+e+f)+3*(g+h+i);

solve satisfy;

output["a = ", show(a), "\n",
			 "b = ", show(b), "\n",
			 "c = ", show(c), "\n",
			 "d = ", show(d), "\n",
			 "e = ", show(e), "\n",
			 "f = ", show(f), "\n",
			 "g = ", show(g), "\n",
			 "h = ", show(h), "\n",
			 "i = ", show(i), "\n"];
