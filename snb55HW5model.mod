# model for MLMPRAM with Procurement.
#
# We will will be adding procurement to the model where we will optimize the ordering of materials for net profit
# New parameters: Order Quantity, Starting Cash, Resource Price will be added, Min Order (Quantity)
# New Variables: Wallet(cash available at time t), and Order (amount of order of resource J) will be added
# The objective function is now changed to represent profit rather than revenue, and there will be adjustments to resource
# balance constraints and the addition of cash flow constraints.
# THIS MODEL ALSO ALLOWS FOR THE PURCHASE OF PRODUCTS/SUBASSMEBLIES
# Will incentivitize favorable money cycles by adding small resource storage penalties
#
# MODEL ASSUMPTIONS:
# Money is earned at the end and used in the beggining. 
# Resources bought in a period can be used for manufacturing during that period
 
		
set MATERIAL;											#set of materials
set CAPACITY ;											#set of capacities
set RESOURCE = MATERIAL union CAPACITY;	
set BOM within {MATERIAL,RESOURCE};	 					#set of BOM pairs 
set PROD within MATERIAL = setof {(p,r) in BOM} p;    	#set of products
set RAW within MATERIAL= MATERIAL diff PROD;			#set of raw material	     						
set SUB_TRIPLES within {PROD, RESOURCE,RESOURCE} default{}; 		# Set of  PROD,PRIME, SUB triples
set SUB_PAIRS within BOM = setof {(p,r,j) in SUB_TRIPLES} (p,r);# set of BOM pairs that have subs
set TIME ordered;	# time periods 

param baseprice {MATERIAL} default 0;	
param p_disc;								# discount rate on prices 
param usage {BOM};    				  		# usage rate of RESOURCE in PROD 
param sub_usage {SUB_TRIPLES};				# usage rate in PROD for prime RESOURCE of sub RESOURCE  
param penalty {SUB_TRIPLES};
param supply {RESOURCE,TIME} default 0;       # supply of RESOURCE in period
param demand {MATERIAL,TIME} default 0;    	# demand for MATERIAL in period				

param price {m in MATERIAL, t in TIME} =		# price of PROD in period
					 baseprice[m]* (1-p_disc)**(ord(t,TIME)-1);    
					 
param cumulative_demand{r in MATERIAL, t in TIME} 
					:=sum{s in TIME: ord(s)<+ord(t)} demand[r,s];
param demand_lb{m in MATERIAL,t in TIME} default 0 # lower bound on cumulative shipment through t
					<= cumulative_demand [m,t] ;	#check that it makes sense	
param BigM := 10* sum {r in MATERIAL} baseprice[r]*cumulative_demand[r, last(TIME)] ;
param alpha := .05 * min {(p,q) in {MATERIAL,MATERIAL}: baseprice [p]>baseprice[q]} 
					(baseprice [p]-baseprice[q]);

param stock_pen {MATERIAL} default .03*alpha;   # carrying cost of MATERIAL
param scrap_pen {RESOURCE} default .05* alpha; 
param sub_pen {PROD} default .02* alpha; 
param make_pen {PROD} default .2* alpha;  # added to avoid making product to avoid stock cost of its BOM
# usually list sets first, but this set is derived from the demand parameter
# so it must be defined after he parameter is defined.
set HAS_DEMAND :=setof{r in MATERIAL:cumulative_demand[r,last(TIME)]>0} r; # Materials that have demand
#NEW PROCUREMENT PARAMETERS:
param start_cash default 0; #cash available at the start of period 1
param resource_price {RESOURCE} default 0; #price of one order of a resource
param order_quantity {RESOURCE} default 0; #amount of resource received per order
param min_order {RESOURCE} default 0; #minimum order amount

var Make {PROD, TIME } >= 0, integer;  	# amount of p in PROD produced
var Scrap{RESOURCE diff PROD, TIME } >=0, integer;	# scrapped RESOURCE (not allowed or products)
var Stock{ MATERIAL, TIME} >=0; 			# stocked MATERIAL
var Ship  {HAS_DEMAND,TIME} >=0, integer;	# MATERIAL shipped in period t  -- includes for late demand 	
var Sub {SUB_TRIPLES,TIME} >=0;				# sub variables, excludes self sub. 
var Selfsub{SUB_PAIRS,TIME}>=0;				# self sub vaiables (prime used)
var Shortfall{HAS_DEMAND,TIME}>=0; 			#shortage relative to LB on shipment
var Backlog{ HAS_DEMAND,TIME}>=0; 			#shortage relative to demand 
var TotRev; 								#for reporting
# PROCUREMENT VARIABLES
var Order{RESOURCE,TIME} >=0 integer; #amount of or orders for resource during a period
#subject to MinOrder {r in RESOURCE, t in TIME}: DO THIS LATER
    #Order[r, t] >= min_order[r] else 0;
var Wallet{TIME}>=0; #amount of cash available for the purchase of resoures			

maximize Profit: sum {p in HAS_DEMAND,t in TIME } (price[p,t] * Ship[p,t])			 # total revenue, 
				- sum {r in RESOURCE diff PROD, t in TIME} (scrap_pen[r] * Scrap[r,t])	
				- sum {r in MATERIAL, t in TIME} (stock_pen[r]* Stock[r,t])					
				- sum {(p,i,r) in SUB_TRIPLES,t in TIME } (penalty[p,i,r] * Sub[p,i,r,t]) 	#small penalty for subs
				- sum {p in PROD, t in TIME} (make_pen[p]*Make[p,t])
				- sum {r in RESOURCE, t in TIME} (resource_price[r]*Order[r,t] )						
				-BigM *sum{p in HAS_DEMAND, t in TIME} Shortfall [p,t] ;				# big penalty for shortfall

subject to Same_make {(p,r) in SUB_PAIRS, t in TIME }:	#accounting for substitution
		Make[p,t] = Selfsub[p,r,t]  + sum {(p,r,q) in SUB_TRIPLES} Sub[p,r,q,t];
																		 
# could have multiple versions of this constraint.  
# 	the if then logic makes sure the constraint matches the type of resource and time period					
subject to Avail {r in RESOURCE, t in TIME}: 												#Resource balance 
	sum {p in PROD: (p,r) in BOM and (p,r) not in SUB_PAIRS } (Make[p,t]*usage[p,r])   	# used as self, no sub possible 
	 + sum {p in PROD :(p,r) in BOM and (p,r) in SUB_PAIRS }  (Selfsub[p,r,t]*usage [p,r]) # has subs, used as prime
	 + sum {(p,j) in SUB_PAIRS: (p,j,r) in SUB_TRIPLES} (Sub[p,j,r,t] *sub_usage[p,j,r]) # used as sub 
	 + (if r in MATERIAL then Stock[r,t] else 0)										#stock if material 
	 + (if r in RESOURCE diff PROD then Scrap[r,t] else 0)
	 + (if r in HAS_DEMAND then Ship[r,t] else 0)				  				  		#ship if material 
	 = supply[r,t]
	 + (if ord(t)>1 and r in MATERIAL then Stock [r, prev(t, TIME)] else 0 )  		 #only if not first period
	 + (if r in PROD then Make [r, t] else 0) #only for products
	 + order_quantity[r]*Order[r,t];														

#cumulative shipment <= cumulative demand. Only needed for materials that have demand
subject to C_Ship {p in HAS_DEMAND,t in TIME }: # cumulative shipment does not exceed cummulative demand
	Backlog [p,t]= sum {s in TIME: ord(s, TIME )<=ord(t,TIME)} demand[p,s] 
					- sum {s in TIME: ord(s,TIME)<=ord(t,TIME)} Ship[p,s]  ;# also computes Backlog
# computing violation of demand lower bound.  
# note that only one of the two defining inequalities is needed, because of the penalty in the objective
subject to Short {p in HAS_DEMAND, t in TIME}:    #Shortfall constraint
	sum {s in TIME: ord(s) <= ord (t)} 	 Ship[p,s]+Shortfall[p,t]>= demand_lb [p,t]; # deviation from lower_bd


# to prevent unnecessary building of product which can occur to avoid holding and scrapping costs of resources 	
subject to EndStock {p in PROD}:  								
 Stock[p, last(TIME) ] <= sum {t in TIME}supply[p,t];  			#  could model this with penalty instead			

# for reporting					
subject to ComputeRevenue: TotRev= (sum {p in HAS_DEMAND,t in TIME } baseprice[p] * Ship[p,t]);

#NEW PROCUREMENT CONSTRAINTS:

#Total Cash Counting
subject to CashAvail {t in TIME}:
    Wallet[t] = (if ord(t) = 1 then start_cash else Wallet[prev(t)])  # accounts for first time period starting cash
              + sum {i in HAS_DEMAND} baseprice[i] * Ship[i, t]
              - (if ord(t) > 1 then sum {j in RESOURCE} resource_price[j] * Order[j, t] else 0); 
              #accounts for ordering more resources
         
#Spending Limits
subject to SpendLimit {t in TIME}: sum {j in RESOURCE} resource_price[j]*Order[j,t] <=
(if ord(t) = 1 then start_cash else Wallet[prev(t)]); #accounts for first time period and others 


#Minimum Order Quantity Constraint
subject to MinOrderConstraint {r in RESOURCE, t in TIME}: 
    if Order[r, t] < min_order[r] then
        Order[r, t] = 0;
							