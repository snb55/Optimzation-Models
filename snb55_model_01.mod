# Sets							
set	PROD;	#set of products					
set	RESC;	# rescourses available					
set	BOR	within {PROD,RESC};		#bill of resources			
							
# Parameters							
#Product Paramaters							
param	sell_p	{PROD}	>0;			#selling price per product	
param	quota	{PROD}	>=0;			#minimum amount needed for production	
param	demand	{j in PROD}	>=	quota[j];		#maximum demand for a single product	
param	big_M;					#penalty for soft-constraint violation	
#Resource Parameters							
param	supply	{RESC}	>=0;			#supply of resource	
param	scrap_cost	{RESC}	;			#cost per unit of getting rid resource (negative if can be sold)	
#B.O.R. Parameters							
param	usage	{BOR}	>=0	default 0;		#amount of resource i needed for product j	
							
#Variables							
var	Make {j in PROD} integer >= quota[j], <=demand[j];		#amount of each product made
var	Lor	{j in RESC}	>=0, <=supply[j];				#units of resource left
var	Quota_R	{j in PROD}	>=0,	<=quota[j];			#units of lower bound demand remaining
							
#Objective: Maximizing Profit							
maximize Profit:							
	sum{j in PROD} 	sell_p[j]*	Make[j]-		#money from selling products		
	sum{j in RESC} 	scrap_cost[j]*	Lor[j]-		#money gained or lost from scrapping extra resources		
	big_M*sum{j in PROD}Quota_R[j];				#penalty for violating soft constraints		
							
# Constrants: Physics							
subject to Availibility{j in RESC}:							
	sum{(i,j) in BOR} 	Make[i]*usage[i,j]+	Lor[j] = supply[j];	#availibility constraint		
subject to Quota{j in PROD}:							
	Make[j]+Quota_R[j]	>=quota[j];					
