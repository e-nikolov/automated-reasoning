from z3 import *
import utils


TRUCKS = 8
SLOTS = 8
CAPACITY = 8000

ITEM_TYPES = 5

NUZZLES = 4
NUZZLE_WEIGHT = 700

PRITTLES = 22 # variable, so far 22 is the maximum satisfiable
PRITTLE_WEIGHT = 400

SKIPPLES = 8
SKIPPLE_WEIGHT = 1000

CROTTLES = 10
CROTTLE_WEIGHT = 2500

DUPPLES = 20
DUPPLE_WEIGHT = 200

ITEMS  = ['Nuzzle', 'Prittle', 'Skipple', 'Crottle', 'Dupple']
WEIGHT = [NUZZLE_WEIGHT, PRITTLE_WEIGHT, SKIPPLE_WEIGHT, CROTTLE_WEIGHT, DUPPLE_WEIGHT]
DEMAND = [NUZZLES, PRITTLES, SKIPPLES, CROTTLES, DUPPLES]

TYPEOF = {}
for idx, item in enumerate(ITEMS):
	TYPEOF[item] = idx

# print(DEMAND)

# print('truck%s%sCount' % (0, items[1]))
truckItem = [[ Int('%s%s' % (ITEMS[j][0], i)) for j in range(ITEM_TYPES) ] for i in range(TRUCKS)]

# print(truckItem)
s = Solver()

for i in range (TRUCKS):
	# All trucks have at least 0 of each item type
	s.add([truckItem[i][j] >= 0  for j in range (ITEM_TYPES)])

	# The number of items on a truck is less than its number of available slots
	s.add(Sum(truckItem[i]) <= SLOTS)

	# The combined weight of all items on a truck is less than its capacity
	s.add(Sum([
		truckItem[i][j] * WEIGHT[j] for j in range(ITEM_TYPES)
	]) <= CAPACITY)

# The combined number of items delivered by all trucks per item type must be equal to the demand 
for j in range(ITEM_TYPES):
	s.add(
		Sum(
			[ truckItem[i][j] for i in range(TRUCKS) ]
		) == DEMAND[j]
	)

# Only the first 3 trucks can store skipples
for i in range(3, TRUCKS):
	s.add(
		truckItem[i][TYPEOF['Skipple']] == 0
	)

# At most 1 nuzzle per truck
for i in range(TRUCKS):
	s.add(
		truckItem[i][TYPEOF['Nuzzle']] <= 1
	)

# print(s.check())

if s.check() == sat:
	print(s.model())
	utils.z3_to_smt2(s, "ass1-q1")

else:
	print("Failed to solve")
# print(s.to_smt2())
