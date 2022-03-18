// Sets and Parameters

int nf = ...;
range F = 1 .. nf; // Factories

int ns = ...;
range S = 1 .. ns; // Transshipment Points

int nc = ...;
range C = 1  .. nc; // Customers

int np = ...;
range P = 1 .. np; // Periods

int nb = ...;
range B = 1..nb; // Number of Batches

float km = ...; // Costs Truck per KM per Ton
float cap = ...; // Maximum Capacity Truck
float fixed = ...; // Fixed Costs Truck
int minimum = ...; // Minimum Flow for Discount
float discount = ...; // Applicable Discount

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

// Arcs from Factory to Transshipment Point using Barges
int nab = ...;
range AB = 1..nab;
int fromNodeB[AB] = ...;
int toNodeB[AB] = ...;
int costB[AB] = ...;

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

float initialInventory[C] = ...; //Initial Inventory Level
int inventoryCap[C] = ...; // Inventory Capacity

// BigM Constraint
int bigM;
execute calculateBx {
  bigM = 0;
  for (var f in F)
  	if (production[f] > bigM)
  		bigM = production[f];
  }

// Decision Variables

dvar float+ x[AFS][P];    // Flow transported from factory I to transshipment point J with transport mode T during period P
dvar float+ y[AFC][P];    // Flow transported from factory I to customer J using trucks during period P
dvar float+ z[ASC][P];    // Flow transported from transshipment point I to customer J using trucks during period P
dvar float+ v[AB][P][B];  // Flow transported from factory I to transshipment point J with using Barges during period P
dvar int+ n[AFC][P];      // Number of trucks needed to transport goods from factory I to customer J during period P
dvar int+ m[ASC][P];      // Number of trucks needed to transport goods from transshipment point I to customer J during period PMag
dvar float+ i[C][P];      // Inventory level of customer C at the end of period P 
dvar boolean k[AB][P][B]; // Binary variable equal to 1 if discount is applied on arc AB in period P for batch B

// Objective

minimize
  sum (a in AFS, p in P) (costFS[a] * x[a][p]) + // Costs Flow from Factory to Transshipment Point Using All But Barges
  sum (a in AB, p in P) (costB[a] * v[a][p][1] + (1 - discount) * costB[a] * v[a][p][2]) + // Costs Flow from Factory to Transshipment Point Using Barges
  sum (a in ASC, p in P) (fixed * m[a][p] + distanceSC[a] * km * z[a][p]) + // Cost Trucks from Transshipment Point to Customers
  sum (a in AFC, p in P) (fixed * n[a][p] + distanceFC[a] * km * y[a][p]) + // Cost Trucks from Factory to Customer
  sum (a in ASC, p in P) handlingCost[fromNodeSC[a]] * z[a][p]; // Handling Costs Transshipment Point

// Constraints

subject to {
  
  // Maximum Capacity Trucks from Factory to Customers
  forall (a in AFC, p in P)
    y[a][p] <= n[a][p] * cap; 
  
  // Maximum Capacity Trucks from Transshipment Point to Customers
  forall (a in ASC, p in P)
    z[a][p] <= m[a][p] * cap;  
  
  // Poduction Cpacity Factory
  forall (p in P, f in F)
    sum (a in AFS : fromNodeFS[a] == f) x[a][p] + sum (a in AB, b in B : fromNodeB[a] == f) v[a][p][b] + sum (a in AFC : fromNodeFC[a] == f) y[a][p] <= production[f];
  
  // Inflow == Outflow of Transshipment Point
  forall (p in P, s in S)
    sum (a in ASC : fromNodeSC[a] == s) z[a][p] == sum (a in AFS : toNodeFS[a] == s) x[a][p] + sum (a in AB, b in B : toNodeB[a] == s) v[a][p][b];
  
  // Inventory Level First Period  
  forall (c in C)
    sum (a in ASC : toNodeSC[a] == c) z[a][1] + sum (a in AFC : toNodeFC[a] == c) y[a][1] + initialInventory[c] - demand[1][c] == i[c][1];
  
  // Update Inventory Level for Every Period  
  forall (p in P, c in C : p != 1)
    sum (a in ASC : toNodeSC[a] == c) z[a][p] + sum (a in AFC : toNodeFC[a] == c) y[a][p] + i[c][p-1] - demand[p][c] == i[c][p];
  
  // Inventory Level May Not Exceed Inventory Capacity  
  forall (p in P, c in C)
    i[c][p] <= inventoryCap[c];
  
  // Barge Related Constraints    
  forall (a in AB, p in P){
    v[a][p][1] <= minimum * k[a][p][1];
    minimum * k[a][p][2] <= v[a][p][2];
    v[a][p][2] <= bigM * k[a][p][2];
    sum(b in B) k[a][p][b] <= 1;
  } 
     
};

// Print Flows from Factory to Transshipment Point Using All But Barges 
execute printSolution1 {
  writeln (" ");
  writeln ("The flows from factory to transshipment point using all but barges");
  for (var p in P)
  	for (var a in AFS)
  		if (x [a][p] > 0)
  			writeln ("Period: ", p , ", from factory " , fromNodeFS[a] , " to transshipment point " , toNodeFS[a] , " : " , x[a][p] , " with transport mode ", vModeFS[a]);
}

// Print Flows from Factory to Transshipment Point Using All But Barges 
execute printSolution2 {
  writeln (" ");
  writeln ("The flow from factory to transshipment point with barge");
  for (var p in P)
  	for (var a in AB)
  		for (var b in B)
  			if (v[a][p][b] > 0)
  				writeln ("Period: ", p,", from factory " , fromNodeB[a] , " to transshipment point " , toNodeB[a] , " : " , v[a][p][b]);
} 

// Print Flows from Transshipment Point to Customer
execute printSolution3 {
  writeln (" ");
  writeln ("The flows from transshipment point to customer");
  for (var p in P)
  	for (var a in ASC)
  		if (z [a][p] > 0)
  	  		writeln ("Period: ", p,", from transshipment point " , fromNodeSC[a] , " to customer " , toNodeSC[a] , " : " ,  z[a][p]);
}

// Print Flows from Factory to Customer
execute printSolution4 {
  writeln (" ");
  writeln ("The flows from factory directly to customer");
  for (var p in P)
  	for (var a in AFC)
  		if (y [a][p] > 0)
  	  		writeln ("From" , fromNodeFC[a] , "to" , toNodeFC [a] , " : " , y[a][p]);
  	  	if (y [a][p] <= 0)
  	  		writeln ("None");
}

// Print Inventory at End of period at Customer Location
execute printSolution5 {
  writeln (" ");
  writeln ("The inventory at the end of a period at the customer location");
  	for (var c in C) {
  	    writeln (" ");
  		writeln ("Inventory of customer ", c);
  		for (var p in P)
  		writeln ("\t Period ", p, ": ", i[c][p]);
    }  		
}

