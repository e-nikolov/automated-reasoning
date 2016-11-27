from z3 import *


TRUCKS = 8

SLOTS = 8
CAPACITY = 8000
ITEM_TYPES = 5

NUZZLES = 4
NUZZLE_WEIGHT = 700

PRITTLES = 22 # variable
PRITTLE_WEIGHT = 400

SKIPPLES = 8
SKIPPLE_WEIGHT = 1000

CROTTLES = 10
CROTTLE_WEIGHT = 2500

DUPPLES = 20
DUPPLE_WEIGHT = 200

items =   ['Nuzzle', 'Prittle', 'Skipple', 'Crottle', 'Dupple']
weight = [NUZZLE_WEIGHT, PRITTLE_WEIGHT, SKIPPLE_WEIGHT, CROTTLE_WEIGHT, DUPPLE_WEIGHT]

# print('truck%s%sCount' % (0, items[1]))
truckItem = [[ Int('truck%s%sCount' % (i, items[j])) for j in range(ITEM_TYPES) ] for i in range(TRUCKS)]

# print(truckItem)
s = Solver()
s.add()


for i in range (TRUCKS):
	for j in range (ITEM_TYPES):
		s.add(truckItem[i][j] >= 0)
	
	# The number of items on a truck is less than its number of available slots
	s.add(truckItem[i][0] + truckItem[i][1] + truckItem[i][2] + truckItem[i][3] + truckItem[i][4] <= SLOTS)

	# The combined weight of all items on a truck is less than its capacity
	# Can this be done more elegantly? Perhaps with some kind of weighted sum?
	s.add(truckItem[i][0] * weight[0] + truckItem[i][1] * weight[1] + truckItem[i][2] * weight[2] + truckItem[i][3] * weight[3] + truckItem[i][4] * weight[4] <= CAPACITY)
	
# The combined number for all trucks of delivered items of each type must be equal to the requirement 
s.add(truckItem[0][0] + truckItem[1][0] + truckItem[2][0] + truckItem[3][0] +
	  truckItem[4][0] + truckItem[5][0] + truckItem[6][0] + truckItem[7][0] == NUZZLES)

s.maximize(truckItem[0][1] + truckItem[1][1] + truckItem[2][1] + truckItem[3][1] + 
	       truckItem[4][1] + truckItem[5][1] + truckItem[6][1] + truckItem[7][1])

s.add(truckItem[0][2] + truckItem[1][2] + truckItem[2][2] + truckItem[3][2] + 
	  truckItem[4][2] + truckItem[5][2] + truckItem[6][2] + truckItem[7][2] == SKIPPLES)

s.add(truckItem[0][3] + truckItem[1][3] + truckItem[2][3] + truckItem[3][3] + 
	  truckItem[4][3] + truckItem[5][3] + truckItem[6][3] + truckItem[7][3] == CROTTLES)

s.add(truckItem[0][4] + truckItem[1][4] + truckItem[2][4] + truckItem[3][4] + 
	  truckItem[4][4] + truckItem[5][4] + truckItem[6][4] + truckItem[7][4] == DUPPLES)

# print(s.check())

if s.check() == sat:
	print(s.model())
else:
	print("Failed to solve")
# print(s.to_smt2())