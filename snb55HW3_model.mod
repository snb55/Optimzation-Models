# model for SPSLRAM with SUBS and TIME

set PROD;         								#set of products
set RESOURCE;  									#set of resources
set BOM within {PROD,RESOURCE};	        		#set of BOM pairs
set CAPACITY within {RESOURCE};                            #resources that cannot carry over periods
set MATERIAL within {RESOURCE};                           #resources that can carry over periods
			
set SUB_TRIPLES within {PROD, RESOURCE,RESOURCE}; 		# Set of  PROD,PRIME, SUB triples
set SUB_PAIRS within BOM = setof {(p,r,j) in SUB_TRIPLES} (p,r);# set of BOM pairs that have subs
set TIME ordered;                                                #set of time periods

param usage {BOM};    						  	# usage rate of RESOURCE in PROD 
param sub_usage {SUB_TRIPLES};					# usage rate in PROD for prime RESOURCE of sub RESOURCE  
param supply {RESOURCE,TIME} >= 0, default 0;        			# supply of RESOURCE
param demand {PROD,TIME} >=0;    				 	# demand for PROD
param price {PROD} >= 0;  						# price of PROD
param scrap_pen {RESOURCE} default 0;        			 	# scrap cost of RESOURCE
param lower_bd{PROD,TIME} default 0;                
param BigM := 10* sum {p in PROD, t in TIME} demand[p,t]*price[p];  		#large enough number
param alpha := .1* min{p in PROD} price[p];                  #small enough number
param epsilon := .1*(min{p in PROD, t in TIME} demand[p,t])/(max{x in PROD, y in TIME} demand[x,y]); #value to disincentive late deliveries
param decayed_price {p in PROD,t in TIME} default price[p]*(1-epsilon)^(ord(t)-1);  #price decayed over time do incentivize early delivery
param material_carry_cost {MATERIAL, TIME} default 0;         #carry cost of material j from period t to t+1
param prod_carry_cost {PROD, TIME} default 0;                        #carry cost of material j from period t to t+1
param material_cap{MATERIAL, TIME} >= 0, default 2*(sum{r in MATERIAL, t in TIME}supply[r,t]);        #bound on period transfer of material
param prod_cap{PROD, TIME} >= 0, default 2*(sum{p in PROD, t in TIME}demand[p,t]);          #bound on product carried between periods
var Make {p in PROD,t in TIME} >= 0, integer;  # amount of p in PROD produced
var Scrap{RESOURCE,TIME} >=0;						# unused RESOURCE
var Shortfall{PROD,TIME}>=0; 						# amount less than lower_bd
var Sub{SUB_TRIPLES,TIME} >=0;						# subs made
var Selfsub{SUB_PAIRS,TIME}>=0;                                             # prods made without sub
var Material_carried {r in MATERIAL, t in TIME}>=0,  <=material_cap[r,t];   # amount of material carried from period t to period t+1
var Prod_carried{p in PROD, t in TIME} >=0, <=prod_cap[p,t];                 #amount of product carried from period t to period t+1
var Prod_delivered {p in PROD, t in TIME} >=lower_bd[p,t];				#amount of product delivered


maximize revenue: sum{t in TIME}( sum {p in PROD} (price[p] * Prod_delivered [p,t])      #selling revenue
				- sum {r in RESOURCE} (scrap_pen[r] *Scrap[r,t])	          #scrap cost
				- BigM* sum{p in PROD} Shortfall[p,t]                                      #demand soft constraint
		        - alpha* sum {(p,r,s) in SUB_TRIPLES} (Sub[p,r,s,t])                # small penalty for subs
				-  sum {r in MATERIAL} (material_carry_cost[r,t]*Material_carried[r,t])     #material holding cost
				-  sum {p in PROD} (prod_carry_cost[p,t]*Prod_carried[p,t])                  #product holding cost	
				);


#Constraints

subject to Same_make {(p,r) in SUB_PAIRS, t in TIME}:	# use something for each BOM item that has subs
Make[p,t] = Selfsub[p,r,t] + sum {(p,r,q) in SUB_TRIPLES} Sub[p,r,q,t];						
#Resource Contraints													
subject to Capacity_Avail {r in CAPACITY, t in TIME}: 
	sum {(p,r) in BOM: (p,r) not in SUB_PAIRS } (Make[p,t]*usage[p,r])   				# used as self, no sub possible 
	 + sum { (p,r) in BOM : (p,r) in SUB_PAIRS }  (Selfsub[p,r,t]*usage [p,r]) 			# i has subs, used as prime
	 + sum { (p,j,r) in SUB_TRIPLES} (Sub[p,j,r,t] *sub_usage[p,j,r]) # j used as sub      # i has sub, used as sub
	 + Scrap[r,t]                                            #scrap
	 = supply[r,t]; 										 #resource availability constraint

subject to Material_Avail {r in MATERIAL, t in TIME : ord(t) >=2 }:  #NEW SET?
	sum {(p,r) in BOM: (p,r) not in SUB_PAIRS } (Make[p,t]*usage[p,r])   				# used as self, no sub possible 
	 + sum { (p,r) in BOM : (p,r) in SUB_PAIRS }  (Selfsub[p,r,t]*usage [p,r]) 			# i has subs, used as prime
	 + sum { (p,j,r) in SUB_TRIPLES} (Sub[p,j,r,t] *sub_usage[p,j,r]) # j used as sub      # i has sub, used as sub
	 + Scrap[r,t]                                                                      #scrap
	 + Material_carried[r,t]
	 = supply[r,t] + Material_carried[r, prev(t)]; 										 #resource availability constraint
		
subject to Material_Intial_Avail {r in MATERIAL}: 
	sum {(p,r) in BOM: (p,r) not in SUB_PAIRS } (Make[p,first(TIME)]*usage[p,r])   		# used as self, no sub possible 
	 + sum { (p,r) in BOM : (p,r) in SUB_PAIRS }  (Selfsub[p,r,first(TIME)]*usage [p,r]) # i has subs, used as prime
	 + sum { (p,j,r) in SUB_TRIPLES} (Sub[p,j,r,first(TIME)] *sub_usage[p,j,r])         # j used as sub i has sub, used as sub
	 + Scrap[r,first(TIME)]
	 + Material_carried[r,first(TIME)]                                                                                                                         #scrap
	 = supply[r,first(TIME)];
	 
#Product Inventory Counting Constraints
subject to Product_Intial_Avail {p in PROD}:
	Make[p,first(TIME)] - Prod_delivered[p,first(TIME)]=Prod_carried[p,first(TIME)];
	
subject to Product_Avail {p in PROD, t in TIME : ord(t) >=2}:
	Prod_carried[p,prev(t)]+Make[p,t] - Prod_delivered[p,t]=Prod_carried[p,t];	 

#Demand Delivery Constraint
subject to Period_Demand {p in PROD, t in TIME}:
	sum { s in TIME : ord(s)<= ord(t)} Prod_delivered[p,t] <= sum { s in TIME : ord(s)<= ord(t)} demand[p,t]; #demand upper limit			                                       #resource availability constraint

#Slack Variable for lowerbound feasibility with large penalty
subject to Short {p in PROD, t in TIME}:
 sum{s in TIME: ord(s)<=ord(t)}(Make[p,s])-sum{x in TIME: ord(x)<ord(t)}(Prod_delivered[p,x])+Shortfall[p,t]>= lower_bd[p,t];# slack from lower_bd