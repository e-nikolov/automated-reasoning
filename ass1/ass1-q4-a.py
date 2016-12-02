from z3 import *
import utils



NUM_VARS = 8
N = 8

VARS = [[Int('a[%02d][%03d]' % (j,i)) for i in range(0,N)] for j in range(0,NUM_VARS)]

s = Solver()

# set the initial values
for i in range(0,NUM_VARS):
	s.add(VARS[i][0] == (i+1))

# a1 and a8 are always constant
for i in range(1,N):
	s.add(VARS[0][i] == 1)
	s.add(VARS[NUM_VARS-1][i] == NUM_VARS)

# define the transition steps
for i in range(1,N):
	s.add(
			Or( 
				And(
					VARS[1][i] == VARS[0][i-1] + VARS[2][i-1],
					VARS[2][i] == VARS[2][i-1],
					VARS[3][i] == VARS[3][i-1],
					VARS[4][i] == VARS[4][i-1],
					VARS[5][i] == VARS[5][i-1],
					VARS[6][i] == VARS[6][i-1],
					),
				And(
					VARS[1][i] == VARS[1][i-1],
					VARS[2][i] == VARS[1][i-1] + VARS[3][i-1],
					VARS[3][i] == VARS[3][i-1],
					VARS[4][i] == VARS[4][i-1],
					VARS[5][i] == VARS[5][i-1],
					VARS[6][i] == VARS[6][i-1],
					),
				And(
					VARS[1][i] == VARS[1][i-1],
					VARS[2][i] == VARS[2][i-1],
					VARS[3][i] == VARS[2][i-1] + VARS[4][i-1],
					VARS[4][i] == VARS[4][i-1],
					VARS[5][i] == VARS[5][i-1],
					VARS[6][i] == VARS[6][i-1],
					),
				And(
					VARS[1][i] == VARS[1][i-1],
					VARS[2][i] == VARS[2][i-1],
					VARS[3][i] == VARS[3][i-1],
					VARS[4][i] == VARS[3][i-1] + VARS[5][i-1],
					VARS[5][i] == VARS[5][i-1],
					VARS[6][i] == VARS[6][i-1],
					),
				And(
					VARS[1][i] == VARS[1][i-1],
					VARS[2][i] == VARS[2][i-1],
					VARS[3][i] == VARS[3][i-1],
					VARS[4][i] == VARS[4][i-1],
					VARS[5][i] == VARS[4][i-1] + VARS[6][i-1],
					VARS[6][i] == VARS[6][i-1],
					),
				And(
					VARS[1][i] == VARS[1][i-1],
					VARS[2][i] == VARS[2][i-1],
					VARS[3][i] == VARS[3][i-1],
					VARS[4][i] == VARS[4][i-1],
					VARS[5][i] == VARS[5][i-1],
					VARS[6][i] == VARS[5][i-1] + VARS[7][i-1],
					)
			)
		)



# define the stop criteria a3 = a7

s.add(VARS[2][N-1] == VARS[6][N-1])




if s.check() == sat:

	print(utils.sorted_model(s))
	utils.z3_to_smt2(s, "ass1-q4-a")

else:	
	print("Failed to solve")