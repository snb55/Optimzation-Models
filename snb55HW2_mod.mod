# model for SPSLRAM with Substitutes

set PROD;         								#set of products
set RESOURCE;  									#set of resources
set BOM within {PROD,RESOURCE};        			#set of BOM pairs	
set SUBS within {PROD,RESOURCE,RESOURCE};		#set of substitutions indexed as : (product, resource, substitute)
set HAS_SUBS := setof {(p,r,s) in SUBS}(p,r);	#subset of SUBS with just the product and it's preferred resource

param usage {BOM};    						  	# usage rate of RESOURCE in PROD 

param demand {PROD} >=0;    				 	# demand for PROD
param price {PROD} >= 0; 						# price of PROD
param lower_bd{PROD} >=0; 						# target lower bound 

param scrap_pen {RESOURCE};        			 	# scrap cost of RESOURCE
param supply {RESOURCE} >= 0;        			# supply of RESOURCE

param sub_usage {SUBS} >=0;						# usage rate of substitute RESOURCE in PROD
param sub_pen {SUBS} >=0;						# penalty weight for substitution use

param bigM := 10* sum {p in PROD} price[p];  	# number to maintain feasibility yet discourage lower bound violations
param alpha := 2;								# number to slightly penlize use of substitution when inferior

var Make {p in PROD}  integer >= lower_bd[p], <= demand[p]; # amount of p in PROD produced
var Scrap {RESOURCE} >=0;									# unused RESOURCE
var Shortfall {PROD}>=0;									# amount of p needed to reach lower demand
var Make_W_Subs {SUBS} integer >=0; 						# amount of p made using substitution
var Make_WO_Subs {HAS_SUBS} integer >=0;					# amount of p made without substitution when a substitution is available

maximize revenue: sum {p in PROD} (price[p] * Make [p]) 							# revenue sum
				- sum {r in RESOURCE} (scrap_pen[r] *Scrap[r])						# subtract an scrapping costs
				- bigM* sum{p in PROD} Shortfall[p]									# penalize for missing lower demand
				- alpha* sum {(p,r,s) in SUBS} (sub_pen[p,r,s]*Make_W_Subs[p,r,s]);	# penalize use of substitutes
													
subject to Avail {r in RESOURCE}:  											# resource availability constraint
				sum {(p,r) in BOM diff HAS_SUBS} (usage[p,r]*Make[p])		# products made that have no subs			
			+   sum {(p,r) in HAS_SUBS} (usage[p,r]*Make_WO_Subs[p,r]) 		# products made that have subs but are not used	
			+ 	sum {(p,r,s) in SUBS} (sub_usage[p,r,s]*Make_W_Subs[p,r,s]) # products made that have subs and are used 				 
			+ Scrap[r] 														# amount scrapped
			= supply[r]; 													# must all sum up to original supply

subject to Total {(p,r) in HAS_SUBS}: 										# everything gets made somehow
				Make_WO_Subs[p,r] 											# product p made without substitution
			+	sum {(p,r,s) in SUBS} Make_W_Subs[p,r,s] 					# products made with substitution
			= Make[p];														# must equal number of total product p made for sale
						 
subject to Short {p in PROD}:
				Make[p]+Shortfall[p]>= lower_bd[p]; 						# deviation from lower demand
				
;





