from z3 import *
import utils

TRUCK_CAPACITY = 260

STEPS = 30

NUM_LOCATIONS = 5
LOCATIONS = ["S", "A", "B", "C", "D"]

LOC = {}
for idx, location in enumerate(LOCATIONS):
	LOC[location] = idx


StoA = 15
StoC = 15
AtoC = 12
AtoB = 17
BtoC = 10
BtoD = 20
CtoD = 20

CAPACITY = { "A": 120, "B": 160 , "C": 100, "D": 160}
# indices	  0     1    2    3    4    5       6           7
ALL_VARS = ["POS", "S", "A", "B", "C", "D", "INTRUCK", "DELIVERED"]

# POS represents the current location of the truck
# 0 -> S
# 1 -> A
# 2 -> B
# 3 -> C
# 4 -> D

TYPEOF = {}
for idx, variable in enumerate(ALL_VARS):
	TYPEOF[variable] = idx

truckStatus = [[Int('%02d%s' % (i,(list(TYPEOF.keys())[list(TYPEOF.values()).index(j)]))) 
				for j in range(len(ALL_VARS))] 
				for i in range(STEPS)]

s = Solver()

# Set starting location for the truck
# The truck is at 'S' initially
s.add(truckStatus[0][TYPEOF['POS']] == 0)

# Set starting values at stage 0 for all cities
s.add(
		And(
			truckStatus[0][TYPEOF['A']] == 80,
			truckStatus[0][TYPEOF['B']] == 80,
			truckStatus[0][TYPEOF['C']] == 80,
			truckStatus[0][TYPEOF['D']] == 80		
			)

	)

# Truck is fully loaded at S initially
s.add(truckStatus[0][TYPEOF['INTRUCK']] == TRUCK_CAPACITY)

# Truck need not unload anything at S
s.add(truckStatus[0][TYPEOF['DELIVERED']] == 0)

# Set limits for variables at any given step
for i in range(STEPS):
	s.add(
			And(
				truckStatus[i][TYPEOF['A']] <= CAPACITY['A'],
				truckStatus[i][TYPEOF['B']] <= CAPACITY['B'],
				truckStatus[i][TYPEOF['C']] <= CAPACITY['C'],
				truckStatus[i][TYPEOF['D']] <= CAPACITY['D'],
				truckStatus[i][TYPEOF['POS']] >= 0,
				truckStatus[i][TYPEOF['POS']] < NUM_LOCATIONS,
				truckStatus[i][TYPEOF['INTRUCK']] >= 0,
				truckStatus[i][TYPEOF['INTRUCK']] <= TRUCK_CAPACITY,
				truckStatus[i][TYPEOF['DELIVERED']] >= 0
				)
		)

# When the truck is in S
for i in range(STEPS-1):
	s.add(
			Implies(
				# Truck is at position S 
				truckStatus[i][TYPEOF['POS']] == LOC['S'],
				# This implies
				And(
					# Nothing is delivered at S
					truckStatus[i][TYPEOF['DELIVERED']] == 0,
					# The truck can go to A or C from here
					Or(
						#Truck goes to A
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['A'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - StoA,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - StoA,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - StoA,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - StoA,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							),
						# Truck goes to C
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['C'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - StoC,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - StoC,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - StoC,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - StoC,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							)

						)

					)
			)
		)

# When the truck is in A
for i in range(STEPS-1):
	s.add(
			Implies(
				# Truck is at position A
				truckStatus[i][TYPEOF['POS']] == LOC['A'],
				# This implies
				And(
					# Stuff was delivered at A
					truckStatus[i][TYPEOF['DELIVERED']] <= CAPACITY['A'] - truckStatus[i][TYPEOF['A']],
					# THe truck can go to S, C or B from here
					Or(
						# Truck goes to S
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['S'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - StoA + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - StoA,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - StoA,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - StoA,
							truckStatus[i+1][TYPEOF['INTRUCK']] >= truckStatus[i][TYPEOF['INTRUCK']]
							),
						# Truck goes to C
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['C'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - AtoC + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - AtoC,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - AtoC,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - AtoC,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							),
						# Truck goes to B
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['B'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - AtoB + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - AtoB,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - AtoB,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - AtoB,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							)

						)


					)
				)
		)

# When the truck is in C
for i in range(STEPS-1):
	s.add(
			Implies(
				# Truck is at position C
				truckStatus[i][TYPEOF['POS']] == LOC['C'],
				# This implies
				And(
					# Stuff was delivered at C
					truckStatus[i][TYPEOF['DELIVERED']] <= CAPACITY['C'] - truckStatus[i][TYPEOF['C']],
					# THe truck can go to S, A or B from here
					Or(
						# Truck goes to S
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['S'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - StoC,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - StoC,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - StoC + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - StoC,
							truckStatus[i+1][TYPEOF['INTRUCK']] >= truckStatus[i][TYPEOF['INTRUCK']]
							),
						# Truck goes to A
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['A'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - AtoC,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - AtoC,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - AtoC + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - AtoC,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							),
						# Truck goes to B
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['B'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - BtoC,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - BtoC,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - BtoC + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - BtoC,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							)

						)


					)
				)
		)

# When the truck is in B
for i in range(STEPS-1):
	s.add(
			Implies(
				# Truck is at position B
				truckStatus[i][TYPEOF['POS']] == LOC['B'],
				# This implies
				And(
					# Stuff was delivered at B
					truckStatus[i][TYPEOF['DELIVERED']] <= CAPACITY['B'] - truckStatus[i][TYPEOF['B']],
					# THe truck can go to A, C or D from here
					Or(
						# Truck goes to A
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['A'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - AtoB,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - AtoB + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - AtoB,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - AtoB,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							),
						# Truck goes to C
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['C'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - BtoC,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - BtoC + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - BtoC,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - BtoC,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							),
						# Truck goes to D
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['D'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - BtoD,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - BtoD + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - BtoD,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - BtoD,
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							)

						)


					)
				)
		)

# When the truck is in D
for i in range(STEPS-1):
	s.add(
			Implies(
				# Truck is at position D
				truckStatus[i][TYPEOF['POS']] == LOC['D'],
				# This implies
				And(
					# Stuff was delivered at D
					truckStatus[i][TYPEOF['DELIVERED']] <= CAPACITY['D'] - truckStatus[i][TYPEOF['D']],
					# THe truck can go to B or C from here
					Or(
						# Truck goes to B
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['B'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - BtoD,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - BtoD,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - BtoD,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - BtoD + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							),
						# Truck goes to C
						And(
							truckStatus[i+1][TYPEOF['POS']] == LOC['C'],
							truckStatus[i+1][TYPEOF['A']] == truckStatus[i][TYPEOF['A']] - CtoD,
							truckStatus[i+1][TYPEOF['B']] == truckStatus[i][TYPEOF['B']] - CtoD,
							truckStatus[i+1][TYPEOF['C']] == truckStatus[i][TYPEOF['C']] - CtoD,
							truckStatus[i+1][TYPEOF['D']] == truckStatus[i][TYPEOF['D']] - CtoD + truckStatus[i][TYPEOF['DELIVERED']],
							truckStatus[i+1][TYPEOF['INTRUCK']] == truckStatus[i][TYPEOF['INTRUCK']] - truckStatus[i+1][TYPEOF['DELIVERED']]
							)

						)


					)
				)
		)

# None of the cities run out of food
for i in range(STEPS):
	s.add(
			And(
				truckStatus[i][TYPEOF['A']] > 0,
				truckStatus[i][TYPEOF['B']] > 0,
				truckStatus[i][TYPEOF['C']] > 0,
				truckStatus[i][TYPEOF['D']] > 0
				)
		)

if s.check() == sat:

	print(utils.sorted_model(s))
	utils.z3_to_smt2(s, "ass2-q1-a")

else:	
	print("Failed to solve")