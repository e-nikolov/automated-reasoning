from z3 import *
import utils


CHIP_WIDTH = 30
CHIP_HEIGHT = 30
COMPONENT_DIM = [(3, 4), (3, 4), (4, 5), (4, 6), (5, 20), (6, 9), (6, 10),
					(6, 11), (7, 8), (7, 12), (10, 10), (10, 20)]

RESULT_PARAMS = ['Height', 'Width', 'X', 'Y']

PARAM = {}

for idx, par in enumerate(RESULT_PARAMS):
	PARAM[par] = idx

POWER_COMPONENTS = 2
POWER_COMPONENTS_DISTANCE = 17

CHIP_POS = [[Real('comp%02d%s' % (i, RESULT_PARAMS[j])) for j in range(len(RESULT_PARAMS))]
			 for i in range(len(COMPONENT_DIM))]

# print(CHIP_POS)

s = Solver()

# All rotations

for i in range(len(COMPONENT_DIM)):
	s.add(
		Or(
			And(
				CHIP_POS[i][PARAM['Width']]  == COMPONENT_DIM[i][PARAM['Width']],
				CHIP_POS[i][PARAM['Height']] == COMPONENT_DIM[i][PARAM['Height']]
			),
			And(
				CHIP_POS[i][PARAM['Width']]  == COMPONENT_DIM[i][PARAM['Height']],
				CHIP_POS[i][PARAM['Height']] == COMPONENT_DIM[i][PARAM['Width']]
			)
		)
	)


# All components fit on the chip
for i in range(len(COMPONENT_DIM)):
	s.add(CHIP_POS[i][PARAM['X']] >= 0)
	s.add(CHIP_POS[i][PARAM['Y']] >= 0)
	
	s.add(
		And(
			CHIP_POS[i][PARAM['X']] + CHIP_POS[i][PARAM['Width']] <= CHIP_WIDTH, 
			CHIP_POS[i][PARAM['Y']] + CHIP_POS[i][PARAM['Height']] <= CHIP_HEIGHT
		)
	)
	
# No Overlap
for i in range(len(COMPONENT_DIM)):
	for j in range(i + 1, len(COMPONENT_DIM)):
		s.add(
			Or(

				CHIP_POS[j][PARAM['X']] + CHIP_POS[j][PARAM['Width']] 	<= CHIP_POS[i][PARAM['X']], # right
				CHIP_POS[j][PARAM['Y']] + CHIP_POS[j][PARAM['Height']] 	<= CHIP_POS[i][PARAM['Y']],  #above

				CHIP_POS[i][PARAM['X']] + CHIP_POS[i][PARAM['Width']]	<= CHIP_POS[j][PARAM['X']], # left
				CHIP_POS[i][PARAM['Y']] + CHIP_POS[i][PARAM['Height']] 	<= CHIP_POS[j][PARAM['Y']], #below
			)
		)

# Touching a power component
for i in range(POWER_COMPONENTS, len(COMPONENT_DIM)):
 	s.add(
		Or(
			[
				And(

					 CHIP_POS[j][PARAM['X']] + CHIP_POS[j][PARAM['Width']]  >= CHIP_POS[i][PARAM['X']], # left
					 CHIP_POS[j][PARAM['Y']] + CHIP_POS[j][PARAM['Height']] >= CHIP_POS[i][PARAM['Y']],  #below

					 CHIP_POS[i][PARAM['X']] + CHIP_POS[i][PARAM['Width']]  >= CHIP_POS[j][PARAM['X']], #right
					 CHIP_POS[i][PARAM['Y']] + CHIP_POS[i][PARAM['Height']] >= CHIP_POS[j][PARAM['Y']], #above
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
					utils.abs(2 * CHIP_POS[j][PARAM['X']] + CHIP_POS[j][PARAM['Width']]  - (2 * CHIP_POS[i][PARAM['X']] + CHIP_POS[i][PARAM['Width']]  )) >= 2 * POWER_COMPONENTS_DISTANCE, # left
					utils.abs(2 * CHIP_POS[j][PARAM['Y']] + CHIP_POS[j][PARAM['Height']] - (2 * CHIP_POS[i][PARAM['Y']] + CHIP_POS[i][PARAM['Height']] )) >= 2 * POWER_COMPONENTS_DISTANCE, # below

					utils.abs(2 * CHIP_POS[i][PARAM['X']] + CHIP_POS[i][PARAM['Width']]  - (2 * CHIP_POS[j][PARAM['X']] + CHIP_POS[j][PARAM['Width']]  )) >= 2 * POWER_COMPONENTS_DISTANCE, # right
					utils.abs(2 * CHIP_POS[i][PARAM['Y']] + CHIP_POS[i][PARAM['Height']] - (2 * CHIP_POS[j][PARAM['Y']] + CHIP_POS[j][PARAM['Height']] )) >= 2 * POWER_COMPONENTS_DISTANCE, # above
				)
			)

if s.check() == sat:

	print(utils.sorted_model(s))
	utils.draw_chip_design(CHIP_WIDTH, CHIP_HEIGHT, COMPONENT_DIM, POWER_COMPONENTS, s, PARAM)
	utils.z3_to_smt2(s, "ass1-q2")

else:	
	print("Failed to solve")

