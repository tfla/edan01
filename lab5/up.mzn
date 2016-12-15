include "globals.mzn";

% parameters

int: n;
int: n_commercial;
int: n_residential;
array[0..n] of int: point_distribution;

% decision variables

% 0 commerical, 1 residential
array[1..n, 1..n] of var 0..1: placements; 

% number of residentials
array[1..n] of var int: sum_rows; 
array[1..n] of var int: sum_cols; 

% points
array[1..n] of var int: points_rows; 
array[1..n] of var int: points_cols; 
var int: total_points;

% constriants

% sum all ones in the rows (number of residential lots per row)
constraint forall (i in 1..n)(
	sum_rows[i] = sum(j in 1..n)(placements[i,j])
);

% sum all ones in the cols (number of residential lots per column)
constraint forall (i in 1..n)(
	sum_cols[i] = sum(j in 1..n)(placements[j,i])
);

% sum total amount of residential plots
constraint n_residential = sum(i in 1..n)(sum_rows[i]);

% get point value for each row
constraint forall(i in 1..n)(
	points_rows[i] = point_distribution[sum_rows[i]]
);

% get point value for each column
constraint forall(i in 1..n)(
	points_cols[i] = point_distribution[sum_cols[i]]
);

% sum of all the points
constraint total_points = sum(i in 1..n)(points_rows[i])+sum(i in 1..n)(points_cols[i]);

% model is done. break the symmetry
constraint lex2(placements);

solve maximize total_points;

output["points = ", show(total_points), "\n", "solution = ", "\n"] ++
       [show_int(1,placements[i,j]) ++ " " ++
       if j mod n == 0 then "\n" else "" endif | i,j in 1..n];
