from z3 import *
import utils


CHIP_WIDTH = 30
CHIP_HEIGHT = 30
COMPONENT_DIM = [(3, 4), (3, 4), (4, 5), (4, 6), (5, 20), (6, 9), (6, 10),
					(6, 11), (7, 8), (7, 12), (10, 10), (10, 20)]

RESULT_PARAMS = ['X','Y','Rotation']

PARAM = {}

for idx, par in enumerate(RESULT_PARAMS):
	PARAM[par] = idx

POWER_COMPONENTS = 2
POWER_COMPONENTS_DISTANCE = 17

CHIP_POS = [[Real('comp%02d%s' % (i, RESULT_PARAMS[j])) for j in range(len(RESULT_PARAMS))]
			 for i in range(len(COMPONENT_DIM))]

# print(CHIP_POS)

s = Solver()


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
					CHIP_POS[i][2] == 0
					),
				# With rotation
				And(
					CHIP_POS[i][0] <= (CHIP_WIDTH - COMPONENT_DIM[i][1]),
					CHIP_POS[i][1] <= (CHIP_WIDTH - COMPONENT_DIM[i][0]),
					CHIP_POS[i][2] == 1
					)
			)
		)

# What about the second component being rotated?	
# No Overlap
for i in range(len(COMPONENT_DIM)):
	for j in range(i + 1, len(COMPONENT_DIM)):
		s.add(
				Or(
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - COMPONENT_DIM[i][0]), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - COMPONENT_DIM[j][0]), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - COMPONENT_DIM[i][1]), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - COMPONENT_DIM[j][1]), #above
						),
						And(CHIP_POS[i][2] == 0, CHIP_POS[j][2] == 0)
					),
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - COMPONENT_DIM[i][1]), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - COMPONENT_DIM[j][0]), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - COMPONENT_DIM[i][0]), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - COMPONENT_DIM[j][1]), #above
						),
						And(CHIP_POS[i][2] == 1, CHIP_POS[j][2] == 0)
					),
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - COMPONENT_DIM[i][0]), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - COMPONENT_DIM[j][1]), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - COMPONENT_DIM[i][1]), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - COMPONENT_DIM[j][0]), #above
						),
						And(CHIP_POS[i][2] == 0, CHIP_POS[j][2] == 1)
					),
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - COMPONENT_DIM[i][1]), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - COMPONENT_DIM[j][1]), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - COMPONENT_DIM[i][0]), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - COMPONENT_DIM[j][0]), #above
						),
						And(CHIP_POS[i][2] == 1, CHIP_POS[j][2] == 1)
					)
				)
			)

# Touching a power component
for i in range(POWER_COMPONENTS, len(COMPONENT_DIM)):
	s.add(
			Or(
				[
					Or(
						And(
							And(
								CHIP_POS[i][0] <= (CHIP_POS[j][0] + COMPONENT_DIM[j][0]), #left w/o rotation
								CHIP_POS[j][0] <= (CHIP_POS[i][0] + COMPONENT_DIM[i][0]), #right
								CHIP_POS[i][1] <= (CHIP_POS[j][1] + COMPONENT_DIM[j][1]), #below
								CHIP_POS[j][1] <= (CHIP_POS[i][1] + COMPONENT_DIM[i][1]), #above
							),
							And(CHIP_POS[i][2] == 0, CHIP_POS[j][2] == 0)
						),
						And(
							And(
								CHIP_POS[i][0] <= (CHIP_POS[j][0] + COMPONENT_DIM[j][0]), #left w/o rotation
								CHIP_POS[j][0] <= (CHIP_POS[i][0] + COMPONENT_DIM[i][1]), #right
								CHIP_POS[i][1] <= (CHIP_POS[j][1] + COMPONENT_DIM[j][1]), #below
								CHIP_POS[j][1] <= (CHIP_POS[i][1] + COMPONENT_DIM[i][0]), #above
							),
							And(CHIP_POS[i][2] == 1, CHIP_POS[j][2] == 0)
						),
						And(
							And(
								CHIP_POS[i][0] <= (CHIP_POS[j][0] + COMPONENT_DIM[j][1]), #left w/o rotation
								CHIP_POS[j][0] <= (CHIP_POS[i][0] + COMPONENT_DIM[i][0]), #right
								CHIP_POS[i][1] <= (CHIP_POS[j][1] + COMPONENT_DIM[j][0]), #below
								CHIP_POS[j][1] <= (CHIP_POS[i][1] + COMPONENT_DIM[i][1]), #above
							),
							And(CHIP_POS[i][2] == 0, CHIP_POS[j][2] == 1)
						),
						And(
							And(
								CHIP_POS[i][0] <= (CHIP_POS[j][0] + COMPONENT_DIM[j][1]), #left w/o rotation
								CHIP_POS[j][0] <= (CHIP_POS[i][0] + COMPONENT_DIM[i][1]), #right
								CHIP_POS[i][1] <= (CHIP_POS[j][1] + COMPONENT_DIM[j][0]), #below
								CHIP_POS[j][1] <= (CHIP_POS[i][1] + COMPONENT_DIM[i][0]), #above
							),
							And(CHIP_POS[i][2] == 1, CHIP_POS[j][2] == 1)
						)
					) for j in range(POWER_COMPONENTS)
				]
			)

		)

# Centres of power components are at a minimum distance
for i in range(POWER_COMPONENTS):
	for j in range(POWER_COMPONENTS):
		if not i == j:
			s.add(
				Or(
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][0])/2.), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][0])/2.), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][1])/2.), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][1])/2.), #above
						),
						And(CHIP_POS[i][2] == 0, CHIP_POS[j][2] == 0)
					),
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][1])/2.), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][1])/2.), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][0])/2.), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][0])/2.), #above
						),
						And(CHIP_POS[i][2] == 1, CHIP_POS[j][2] == 0)
					),
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][0])/2.), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][0])/2.), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][1])/2.), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][1])/2.), #above
						),
						And(CHIP_POS[i][2] == 0, CHIP_POS[j][2] == 1)
					),
					And(
						Or(
							CHIP_POS[i][0] <= (CHIP_POS[j][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][1])/2.), #left w/o rotation
							CHIP_POS[j][0] <= (CHIP_POS[i][0] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][1] - COMPONENT_DIM[i][1])/2.), #right
							CHIP_POS[i][1] <= (CHIP_POS[j][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][0])/2.), #below
							CHIP_POS[j][1] <= (CHIP_POS[i][1] - POWER_COMPONENTS_DISTANCE - abs(COMPONENT_DIM[j][0] - COMPONENT_DIM[i][0])/2.), #above
						),
						And(CHIP_POS[i][2] == 1, CHIP_POS[j][2] == 1)
					)
				)
			)

if s.check() == sat:

	print(utils.sorted_model(s))
	utils.draw_chip_design(CHIP_WIDTH, CHIP_HEIGHT, COMPONENT_DIM, s)
	utils.z3_to_smt2(s, "ass1-q2")

else:	
	print("Failed to solve")

