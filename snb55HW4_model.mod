# Multi-level/period model with subs

#Here are the updates I will be making to the HW3 Key
#Set/Param Modifications:
# I will create two new sets RAW, ENDPROD
#All PROD go in MATERERIAL
#BOM will be modified
#prod_stock_pen will get absored into mat_stoc_pen
#appropriate set indices will be alterted (usually from PROD to MATERIAL)
#Variable,OF and Constraint Mods:
#Prod_stock var is absorbed into Mat_stock -> removed from OF and removed as a constraint
#Ship, Mat_stock, Shortfall now all index over MATERIAL instead of PROD
#New mofified Material Balance constraint
#New Raw Material Balance constraint (no make)
#Cumulative Bound Constraint and Shortfall constraints idexed over MATERIAL rather than PROD 

set RAW; 										#set of raw materials
set CAPACITY ;									#set of capacities
set PROD;         								#set of products
set ENDPROD within PROD;						#set of end procucts
set MATERIAL = RAW union PROD;					#set of materials
set RESOURCE = MATERIAL union CAPACITY;					#master set of all
set BOM within {PROD, RESOURCE diff ENDPROD};	 		#set of BOM pairs				
set SUB_TRIPLES within {PROD, RESOURCE,RESOURCE}; 		# Set of  PROD,PRIME, SUB triples
set SUB_PAIRS within BOM = setof {(p,r,j) in SUB_TRIPLES} (p,r);# set of BOM pairs that have subs
set TIME ordered;
							# time periods t0,t1,t2,,,tT
param baseprice {MATERIAL} default 0;	#modified to be material as was almost everything that was previously PROD
param p_disc;							# discount rate on prices. called epsilonn in model
param alpha >=0; #small weight;
param usage {BOM};    				  	# usage rate of RESOURCE in PROD 
param sub_usage {SUB_TRIPLES};			# usage rate in PROD for prime RESOURCE of sub RESOURCE  
param penalty {SUB_TRIPLES} ;
param supply {RESOURCE,TIME} default 0;       	# supply of RESOURCE in period
param demand {MATERIAL,TIME} default 0;    			# demand for MATERIAL in period			
param demand_lb{MATERIAL,TIME} default 0;
param scrap_pen {RESOURCE} default alpha;       		 # scrap cost of RESOURCE 
param mat_stoc_pen{MATERIAL} default alpha;			# carrying cost of MATERIAL in time; prod_stoc_pen absorbed
param BigM := 10* sum {m in MATERIAL, t in TIME} baseprice[m]*demand[m,t];  		#large enough number

param price {m in MATERIAL, t in TIME}=		# scaled price of MATERIAL in period
					 baseprice[m]* (1-p_disc)**(ord(t,TIME)-1);  

var Make { PROD, TIME } >= 0, integer;  # amount of p in PROD produced
var Scrap{ RESOURCE,  TIME } >=0;		# scrapped RESOURCE
var Mat_stock{ MATERIAL, TIME} >=0;		 # stocked MATERIAL
var Shortfall{MATERIAL,  TIME}>=0; 					# amount less than lower_bd	
var Ship { MATERIAL, TIME} >=0, integer;	# material shipped in period t  -- includes for late demand 	
var Sub {SUB_TRIPLES,  TIME} >=0;				# sub variables, excludes self sub. 
var Selfsub{SUB_PAIRS,  TIME}>=0;				# self sub vaiables (prime used)

maximize revenue: 
 # scaled revenue
 	sum {m in MATERIAL,t in TIME } (price[m,t] * Ship[m,t])   #sale of material
 #little steering penalties 
				- sum {r in RESOURCE, t in TIME} (scrap_pen[r] * Scrap[r,t]) #scrap penalty	
				- .01* alpha *sum {m in MATERIAL, t in TIME} (Mat_stock[m,t]) 	#stock holding penalty
				- alpha* sum {(p,i,r) in SUB_TRIPLES,t in TIME } ( penalty[p,i,r]*Sub[p,i,r,t])#substitution penalty
	#Big bound penalties		
				-BigM *sum{m in MATERIAL, t in TIME} Shortfall [m,t]; #lowerbound shortfall

subject to Same_make {(p,r) in SUB_PAIRS, t in TIME }:	
		Make[p,t] = Selfsub[p,r,t] + sum {(p,r,q) in SUB_TRIPLES} Sub[p,r,q,t];		#tracking methods of making prod				
													
subject to AvailC {r in CAPACITY, t in TIME }: 						# capacity availability constraint
       sum {(p,r) in BOM: (p,r) not in SUB_PAIRS } (Make[p,t]*usage[p,r])   			 	# used as self, no sub possible 
	 + sum { (p,r) in BOM: (p,r) in SUB_PAIRS }  (Selfsub[p,r,t]*usage [p,r]) 			   #i has subs, used as prime
	 + sum {(p,j) in SUB_PAIRS: (p,j,r) in SUB_TRIPLES} (Sub[p,j,r,t] *sub_usage[p,j,r])    # i used as sub 
	 + Scrap[r,t] #has no Ship or Make
	 = supply[r,t];  
	 							
subject to AvailP {p in PROD, t in TIME}: 						# material balance   constraint
	sum {(x,p) in BOM: (x,p) not in SUB_PAIRS } (Make[x,t]*usage[x,p])  	 			# used as self, no sub possible 
	 + sum { (x,p) in BOM:(x,p) in SUB_PAIRS }  (Selfsub[x,p,t]*usage [x,p]) 			#i has subs, used as prime
	 + sum {(x,j) in SUB_PAIRS: (x,j,p) in SUB_TRIPLES} (Sub[x,j,p,t] *sub_usage[x,j,p]) # i used as sub 
	 + Mat_stock[p,t] + Scrap[p,t] + Ship[p,t]
	 = supply[p,t] + Make[p,t]
	 	+ if ord(t, TIME) >1 then Mat_stock [p, prev(t, TIME)] else 0; #handles t=1 case
#Note for all ENDPROD, usage = 0 so is included in the above

subject to AvailW {w in RAW, t in TIME}: #Raw Material Availability Constraint 		# raw material balance constraint
	sum {(p,w) in BOM: (p,w) not in SUB_PAIRS } (Make[p,t]*usage[p,w])  	 			# used as self, no sub possible 
	 + sum { (p,w) in BOM:(p,w) in SUB_PAIRS }  (Selfsub[p,w,t]*usage [p,w]) 			#i has subs, used as prime
	 + sum {(p,j) in SUB_PAIRS: (p,j,w) in SUB_TRIPLES} (Sub[p,j,w,t] *sub_usage[p,j,w]) # i used as sub 
	 + Mat_stock[w,t] + Scrap[w,t] +Ship[w,t] 
	 = supply[w,t] #has no make
	 	+ if ord(t, TIME) >1 then Mat_stock [w, prev(t, TIME)] else 0; #handles t=1 case

subject to C_Ship {m in MATERIAL,t in TIME }:   # cumulative bound constraint
	sum {s in TIME: ord(s,TIME)<=ord(t,TIME)} Ship[m,s] 
		<= sum {s in TIME: ord(s, TIME )<=ord(t,TIME)} demand[m,s];#cannot ship more than the total amount of demand accumulated

subject to Short {m in MATERIAL, t in TIME}:    #Shortfall constraint, tracker slack var Shortfall
	Shortfall[m,t]+ sum {s in TIME: ord(s) <= ord (t)} 	 Ship[m,s]
							>= demand_lb [m,t];	 # deviation from ship lower_bd

;



