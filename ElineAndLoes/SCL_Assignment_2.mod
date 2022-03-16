/*********************************************
 * OPL 20.1.0.0 Model
 * Author: eline
 * Creation Date: 5 mrt. 2021 at 12:22:26
 *********************************************/
execute{cplex.tilim=180;}

int np = ...;
range Periods = 1..np;
{string} Factories = ...;
{string} Destinations = ...;	// I.e. Customers
{string} TransPts = ...;
{string} Warehouses = ...;

float vc = ...;		// variable cost per km per ton
float FC = ...;		// fixed cost per truck
float trCap = ...;	// transport capacity truck

int f[Factories] = ...;					 // production capacity factories
float h[TransPts] = ...;				 // handling costs transshipment points
float d[Periods][Destinations] = ...;	 // demand customers
int c[Destinations][Factories] = ...;	 // distance customers to factories
float s[Destinations][TransPts] = ...;	 // distance customers to transshipment points

float blt[TransPts][Factories] = ...;	// block train costs per ton
float swt[TransPts][Factories] = ...;	// single wagon train costs per ton
float sss[TransPts][Factories] = ...;	// short sea shipping costs per ton
float bar[TransPts][Factories] = ...;	// barge costs per ton

//variables for question 1:
float IIL[Warehouses] = ...;	// initial inventory level of the warehouses
float IC[Warehouses] = ...;		// inventory capacity of the warehouses

dvar float+ x[Factories][Destinations][Periods];		// Tonnes driven directly from factory i to warehouse at destination j in each period p
dvar float+ v_blt[Factories][TransPts][Periods];		// Tonnes from factory i to transshipment point t via blt in each period p
dvar float+ v_swt[Factories][TransPts][Periods];		// Tonnes from factory i to transshipment point t via swt in each period p
dvar float+ v_sss[Factories][TransPts][Periods];		// Tonnes from factory i to transshipment point t via swt in each period p
dvar float+ v_bar[Factories][TransPts][Periods];		// Tonnes from factory i to transshipment point t via bar in each period p
dvar float+ z[TransPts][Destinations][Periods];			// Tonnes driven indirectly from transshipment point t to warehouse at destination j in each period p
dvar int+ trucksF[Factories][Destinations][Periods];	// Trucks sent from factory i to destination j in period p
dvar int+ trucksT[TransPts][Destinations][Periods];		// Trucks sent from transpt t to destination j in period p

//extra variables for question 2:
dvar float+ WD[Warehouses][Destinations][Periods];		// Tonnes used from warehouse w at destination j in period p
dvar float+ IL[Periods][Warehouses]; 					// Inventory level at the end of period p for warehouse w

minimize sum(i in Factories, j in Destinations, p in Periods) (c[j][i]*vc*x[i][j][p])

		+ sum(i in Factories, t in TransPts, p in Periods) 
		(blt[t][i]*v_blt[i][t][p] + swt[t][i]*v_swt[i][t][p] + sss[t][i]*v_sss[i][t][p] + bar[t][i]*v_bar[i][t][p])
		
		+ sum(t in TransPts, j in Destinations, p in Periods) (s[j][t]*vc*z[t][j][p] + h[t] * z[t][j][p])
		
		+ sum(p in Periods, i in Factories, j in Destinations) trucksF[i][j][p] * FC
		+ sum(p in Periods, t in TransPts, j in Destinations) trucksT[t][j][p] * FC;
		//Additional costs for question 2:
		//+ sum(i in Factories, w in Warehouses, p in Periods) (c[w][i]*vc*FW[i][w][p])
		//+ sum(t in TransPts, w in Warehouses, p in Periods) (s[w][t]*vc*z[t][w][p] + h[t] * TW[t][w][p])
		//+ sum(p in Periods, i in Factories, w in Warehouses) trucksFW[i][w][p] * FC
		//+ sum(p in Periods, t in TransPts, w in Warehouses) trucksTW[t][w][p] * FC;
		

subject to {
  // Number of trucks needed
  forall (p in Periods)
    forall(i in Factories)
      forall(j in Destinations)
        trucksF[i][j][p] >= x[i][j][p]/trCap;
  
  forall (p in Periods)
    forall(t in TransPts)
      forall(j in Destinations)
        trucksT[t][j][p] >= z[t][j][p]/trCap;
  
  /*forall (p in Periods)
    forall(i in Factories)
      forall(w in Warehouses)
        trucksFW[i][w][p] >= FW[i][w][p]/trCap;
  
  forall (p in Periods)
    forall(t in TransPts)
      forall(w in Warehouses)
        trucksTW[t][w][p] >= TW[t][w][p]/trCap;*/
        
  // Everyting going out of the factory in a period must not exceed the capacity
  forall (p in Periods)
    forall (i in Factories)
      sum(j in Destinations) (x[i][j][p]) 
      + sum(t in TransPts) (v_blt[i][t][p] + v_swt[i][t][p] + v_sss[i][t][p] + v_bar[i][t][p]) // + sum(w in Warehouses) (x[i][w][p])
      <= f[i];
  
  // Meet all demand for every destination for every period
  forall (p in Periods)
    forall (j in Destinations)
      /* sum(i in Factories) x[i][j][p] + sum(i in TransPts) z[i][j][p] */ sum(w in Warehouses: w == j) WD[w][j][p] >= d[p][j];
      
  // Just to reduce the search space for warehouses supplying customers
  forall(p in Periods)
    forall(j in Destinations)
      forall(w in Warehouses: w != j)
        WD[w][j][p] == 0;
      
  // Flow in = Flow out for every transshipment point in every period
  forall(t in TransPts)
    forall(p in Periods)
    	sum(i in Factories) (v_blt[i][t][p] + v_swt[i][t][p] + v_sss[i][t][p] + v_bar[i][t][p])
    	== sum(j in Destinations) z[t][j][p]; // + sum(w in Warehouses) TW[t][w][p]
    	
  // Change the value of the inventory level, so that it can be used in further calculations (separate cases for p=1 and p>1)
  forall(w in Warehouses)
    IL[1][w] == IIL[w] + sum(i in Factories) (x[i][w][1])
    + sum(t in TransPts) (z[t][w][1]) 
    - sum(j in Destinations: j == w) (WD[w][j][1]);
    
  forall(p in Periods: p > 1)
    forall(w in Warehouses)
      IL[p][w] == IL[p-1][w] + sum(i in Factories) (x[i][w][p])
      + sum(t in TransPts) (z[t][w][p]) 
      - sum(j in Destinations: j == w) (WD[w][j][p]);
      
  // The inventory level of the warehouse must not exceed the capacity
  forall(p in Periods)
    forall(w in Warehouses)
      IL[p][w] <= IC[w];
}


// Print Statements

execute {
  for ( p = 1 ; p <= np ; p++ ) {
    writeln("PERIOD ", p);
    writeln("--------");
    
    // Factory Production
    for ( i in Factories ) {
      var produced = 0;
      for ( t in TransPts) {
        produced += v_blt[i][t][p]+v_swt[i][t][p]+v_sss[i][t][p]+v_bar[i][t][p];
      }
	  for( j in Destinations ) {
		produced += x[i][j][p];
      }
      writeln("Produced by ", i, ": ", produced);
    }
    
    // Transportation to transshipment points
    writeln("");
    writeln("-- Transportation to transshipment points --");
    writeln("");
    for (t in TransPts) {
      var total_received = 0;
      for (i in Factories) {
      	total_received += v_blt[i][t][p]+v_swt[i][t][p]+v_sss[i][t][p]+v_bar[i][t][p];
      }
      if (total_received > 0) {
        writeln("Transported to ", t, " from:")
        for ( i in Factories ) {
          var received = v_blt[i][t][p]+v_swt[i][t][p]+v_sss[i][t][p]+v_bar[i][t][p];
          if (received > 0) {
            writeln(i," = ", received);
          }                 		
      	}
      	writeln("")
      }
    }
  	
  	// Arrived at warehouses
  	var trucks = 0;
  	writeln("-- Warehouse management --");
  	writeln("");
  	for( w in Warehouses ) {
  	  var stored = 0;
  	  for ( t in TransPts) {
        stored += z[t][w][p];
      }    
	  for( i in Factories) {
		stored += x[i][w][p];
      }
      if ( stored > 0 ) {
        writeln("Arrived at warehouse ", w, " from:");
        for ( i in Factories ) {
          trucks += trucksF[i][w][p];
          if( x[i][w][p] > 0 ) {
            writeln(i,  " = ", x[i][w][p], " (+)");
          }
        }          
        for ( t in TransPts ) {
          trucks += trucksT[t][w][p];
          if ( z[t][w][p] > 0 ) {
          	writeln(t, " = ", z[t][w][p], " (+)");
          } 
        }
        writeln("Used by facility = ", d[p][w], " (-)")
        writeln("Stock level = ", IL[p][w])
        writeln("");
      }
  	}
  	
  	writeln("Trucks used this period:");
  	writeln(trucks);
  	writeln("");
  }  	
} 