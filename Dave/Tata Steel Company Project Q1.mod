// Assignment | Tata Steel Company Project
// Supply Chain Lub | March, 2021
// Britt, Christa, Michelle and Dave

// Sets and Parameters

int nf = ...;
range F = 1 .. nf; // Factories

int ns = ...;
range S = 1 .. ns; // Transshipment Points

int nc = ...;
range C = 1  .. nc; // Customers

int np = ...;
range P = 1 .. np; // Periods

float km = ...; // Costs Truck per KM per Ton
float cap = ...; // Maximum Capacity Truck
float fixed = ...; // Fixed Costs Truck

int production[F] = ...; // Production Factories
float demand[P][C] = ...; // Demand Customers
float handlingCost[S] = ...; // Handeling Cost Transshipment Point

// Arcs from Factory to Transshipment Point
int nafs = ...;
range AFS = 1 .. nafs; 
int fromNodeFS[AFS] = ...;
int toNodeFS[AFS] = ...;
int vModeFS[AFS] = ...;
float costFS[AFS] = ...;

// Arcs from Transshipment Point to Customer
int nasc = ...;
range ASC = 1 .. nasc;
int fromNodeSC[ASC] = ...;
int toNodeSC[ASC] = ...;
float distanceSC[ASC] = ...;

// Arcs from Factory to Customer
int nafc = ...;
range AFC = 1 .. nafc;
int fromNodeFC[AFC] = ...;
int toNodeFC[AFC] = ...;
float distanceFC[AFC] = ...;

// Decision Variables

dvar float+ x[AFS][P]; // Flow transported from factory I to transshipment point J with transport mode T during period P
dvar float+ y[AFC][P]; // Flow transported from factory I to customer J using trucks during period P
dvar float+ z[ASC][P]; // Flow transported from transshipment point I to customer J using trucks during period P
dvar int+ n[AFC][P];   // Number of trucks needed to transport goods from factory I to customer J during period P
dvar int+ m[ASC][P];   // Number of trucks needed to transport goods from transshipment point I to customer J during period PMag 

// Objective

minimize
  sum (a in AFS, p in P) (costFS[a] * x[a][p]) + 
  sum (a in ASC, p in P) (fixed * m[a][p] + distanceSC[a] * km * z[a][p]) + 
  sum (a in AFC, p in P) (fixed * n[a][p] + distanceFC[a] * km * y[a][p]) +
  sum (a in AFS, p in P) handlingCost[toNodeFS[a]] * x[a][p];

// Constraints

subject to {
  
  forall (a in AFC, p in P)
    y[a][p] <= n[a][p] * cap; // Maximum Capacity Trucks from Factory to Customers
  
  forall (a in ASC, p in P)
    z[a][p] <= m[a][p] * cap;  // Maximum Capacity Trucks from Transshipment Point to Customers
  
  forall (p in P, f in F)
    sum (a in AFS : fromNodeFS[a] == f) x[a][p] + sum (a in AFC : fromNodeFC[a] == f) y[a][p] <= production[f];
  
  forall (p in P, c in C)
    sum (a in ASC : toNodeSC[a] == c) z[a][p] + sum (a in AFC : toNodeFC[a] == c) y[a][p] == demand[p][c];
  
  forall (p in P, s in S)
    sum (a in ASC : fromNodeSC[a] == s) z[a][p] == sum (a in AFS : toNodeFS[a] == s) x[a][p];

};

// Print Solution

execute printSolution1 {
  writeln ("");
  writeln ("The flows from factory to transshipment point:");
  for (var p in P)
  	for (var a in AFS)
  		if (x [a][p] > 0)
  			writeln ( "Period: ", p," | from factory " , fromNodeFS [a] , " to transshipment point " , toNodeFS [a] , ": " , x [a][p], " | with transport mode ", vModeFS[a]);
};

execute printSolution2 {
  writeln (""); 
  writeln ("The flows from transshipment point to customer using trucks:");
  for (var p in P)
  	for (var a in ASC)
  		if (z [a][p] > 0)
  	  		writeln ( "Period: ", p," | from transshipment point " , fromNodeSC [a] , " to customer " , toNodeSC [a] , ": " ,  z[a][p]);
};

execute printSolution3 {
  writeln ("");
  writeln ("The flows from factory directly to customer using trucks:");
  for (var p in P)
  	for (var a in AFC)
  		if (y [a][p] > 0)
  	  		writeln ( "Period: ", p," | from factory " , fromNodeFC [a] , " to costumer " , toNodeFC [a] , ": " , y [a][p] );
};

