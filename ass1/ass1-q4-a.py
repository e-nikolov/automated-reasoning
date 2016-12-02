from z3 import *
import utils


# STEPS = 8 # Vary this to find the minimum for 

# a
STEPS = 8

# b
# STEPS = 18

NUM_VARS = 8

a = [[Int('Step %02d for a%d = ' % (step, var)) for step in range(0, STEPS)] for var in range(1, NUM_VARS+1)]

s = Solver()

# set the initial values
for i in range(0, NUM_VARS):
	s.add(a[i][0] == (i+1))

# a1 and a8 are always constant
for i in range(1, STEPS):
	s.add(a[0][i] == 1)
	s.add(a[NUM_VARS-1][i] == NUM_VARS)

# define the transition steps
for step in range(1, STEPS):
	step_constraints = []
	
	for chosen_var in range(1, NUM_VARS-1):

		var_constraints = []

		for i in range(1, NUM_VARS-1):
			if i == chosen_var:
				var_constraints.append(a[chosen_var][step] == a[chosen_var-1][step-1] + a[chosen_var+1][step-1])
			else:
				var_constraints.append(a[i][step] == a[i][step-1])

		step_constraints.append(And(var_constraints))

	s.add(
		Or(step_constraints)
	)


# define the stop criteria a3 = a7

# a
s.add(a[2][STEPS-1] == a[6][STEPS-1])

# b
# s.add(a[2][STEPS-1] == a[4][STEPS-1])

if s.check() == sat:
	step = 0
	for var, var_str in utils.sorted_model(s):
		print(var, var_str)
		step = step + 1

		if step % NUM_VARS == 0:
			print()

	utils.z3_to_smt2(s, "ass1-q4-a")

else:	
	print("Failed to solve")