from z3 import *
import utils


CHIP_WIDTH = 30
CHIP_HEIGHT = 30
COMPONENT_DIM = [(4,3),(4,3),(4,5),(4,6),(5,20),(6,9),(6,10),
					(6,11),(7,8),(7,12),(10,10),(10,20)]

RESULT_PARAMS = ['X','Y','Width','Height']
PARAM = {}

for idx, par in enumerate(RESULT_PARAMS):
	PARAM[par] = idx


CHIP_POS = [[Real('comp%s%s' % (i,RESULT_PARAMS[j])) for j in range(len(RESULT_PARAMS))]
			 for i in range(len(COMPONENT_DIM))]

# print(CHIP_POS)

s = Solver()