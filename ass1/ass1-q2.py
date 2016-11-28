from z3 import *
import utils


CHIP_WIDTH = 30
CHIP_HEIGHT = 30
COMPONENT_DIM = [(4,3), (4,3), (4,5), (4,6), (5,20), (6,9), (6,10),
					(6,11), (7,8), (7,12), (10,10), (10,20)]

<<<<<<< HEAD
RESULT_PARAMS = ['X','Y','Width','Height','Rotation']
=======
RESULT_PARAMS = ['X', 'Y', 'Width', 'Height']
>>>>>>> 503e5a8773f718003ee7a9ab89c14a149c631d37
PARAM = {}

for idx, par in enumerate(RESULT_PARAMS):
	PARAM[par] = idx


CHIP_POS = [[Real('comp%s%s' % (i, RESULT_PARAMS[j])) for j in range(len(RESULT_PARAMS))]
			 for i in range(len(COMPONENT_DIM))]

# print(CHIP_POS)

s = Solver()
<<<<<<< HEAD

# All components fit on the chip
for i in range(len(COMPONENT_DIM)):
	s.add(CHIP_POS[i][0] >= 0)
	s.add(CHIP_POS[i][1] >= 0)
	
	s.add(
			Or(
				# Without rotation
				And(
					CHIP_POS[i][0] <= (CHIP_WIDTH - COMPONENT_DIM[i][0]), 
					CHIP_POS[i][1] <= (CHIP_WIDTH - COMPONENT_DIM[i][1]),
					CHIP_POS[i][4] == 0
					),
				# With rotation
				And(
					CHIP_POS[i][0] <= (CHIP_WIDTH - COMPONENT_DIM[i][1]),
					CHIP_POS[i][1] <= (CHIP_WIDTH - COMPONENT_DIM[i][0]),
					CHIP_POS[i][4] == 1
					)
			)
		)
	
# No Overlap
for i in range(len(COMPONENT_DIM)):
	for j in range(len(COMPONENT_DIM)):
		if not (i==j):
			s.add(
					Or(
						And(
							Or(
								CHIP_POS[i][0] <= (CHIP_POS[j][0] - COMPONENT_DIM[i][0]), #left w/o rotation
								CHIP_POS[j][0] <= (CHIP_POS[i][0] - COMPONENT_DIM[j][0]), #right
								CHIP_POS[i][1] <= (CHIP_POS[j][1] - COMPONENT_DIM[i][1]), #below
								CHIP_POS[j][1] <= (CHIP_POS[i][1] - COMPONENT_DIM[j][1]), #above
							),
							CHIP_POS[i][4] == 0
						),
						And(
							Or(
								CHIP_POS[i][0] <= (CHIP_POS[j][0] - COMPONENT_DIM[i][1]), #left with rotation
								CHIP_POS[j][0] <= (CHIP_POS[i][0] - COMPONENT_DIM[j][1]), #right
								CHIP_POS[i][1] <= (CHIP_POS[j][1] - COMPONENT_DIM[i][0]), #below
								CHIP_POS[j][1] <= (CHIP_POS[i][1] - COMPONENT_DIM[j][0]), #above
							),
							CHIP_POS[i][4] == 1
						)
						)

				)

if s.check() == sat:
	print(s.model())
	utils.z3_to_smt2(s, "ass1-q2")

else:
	print("Failed to solve")
=======
>>>>>>> 503e5a8773f718003ee7a9ab89c14a149c631d37
