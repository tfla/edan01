% Making a burger
%include "globals.mzn";

var 0..10: beef;    % beef patties
var 0..10: bun;     % buns
var 0..10: cheese;  % cheese
var 0..10: onion;   % onion
var 0..10: pickle;  % pickle
var 0..10: lettuce; % lettuce
var 0..10: ketchup; % ketchup
var 0..10: tomato;  % tomato

% ammounts (0 < x < 6)
constraint beef > 0;
constraint bun > 0;
constraint cheese > 0;
constraint onion > 0;
constraint pickle > 0;
constraint lettuce > 0;
constraint ketchup > 0;
constraint tomato > 0;
constraint beef < 6;
constraint bun < 6;
constraint cheese < 6;
constraint onion < 6;
constraint pickle < 6;
constraint lettuce < 6;
constraint ketchup < 6;
constraint tomato < 6;

% < 3000mg sodium
constraint 50*beef + 330*bun + 310*cheese + 1*onion + 260*pickle + 3*lettuce + 160*ketchup + 3*tomato < 3000;

% < 150g fat
constraint 17*beef + 9*bun + 6*cheese + 2*onion + 0*pickle + 0*lettuce + 0*ketchup + 0*tomato < 150;

% < 3000cal
constraint 220*beef + 260*bun + 70*cheese + 10*onion + 5*pickle + 4*lettuce + 20*ketchup + 9*tomato < 3000;

% taste standards
constraint ketchup = lettuce;
constraint pickle = tomato;

% maximise burger cost
solve maximize 0.25*beef + 0.15*bun + 0.1*cheese + 0.09*onion + 0.03*pickle + 0.04*lettuce + 0.02*ketchup + 0.04*tomato;

% print results
output ["no. of beef = ", show(beef), "\n",
				"no. of bun = ", show(bun), "\n",
  			"no. of cheese = ", show(cheese), "\n",
				"no. of onion = ", show(onion), "\n",
				"no. of pickle = ", show(pickle), "\n",
				"no. of lettuce = ", show(lettuce), "\n",
				"no. of ketchup = ", show(ketchup), "\n",
				"no. of tomato = ", show(tomato), "\n",
				"burger price: $", show(0.25*beef + 0.15*bun + 0.1*cheese + 0.09*onion + 0.03*pickle + 0.04*lettuce + 0.02*ketchup + 0.04*tomato), "\n"];

