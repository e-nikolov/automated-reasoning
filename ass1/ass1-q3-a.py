from z3 import *
import utils


TIME = 59 # Aim is to minimize this variable

JOBS = 12
RUN_TIME_ADDER = 5
JOB_TIMES = [i+1+RUN_TIME_ADDER for i in range(JOBS)]

SCHEDULE = [Int('J%02d' % (i+1)) for i in range(JOBS)]


s = Solver()

# All jobs start at positive time (i.e) time >= 0
for job in range(JOBS):
	s.add(SCHEDULE[job] >= 0)

# Job 3 starts after 1 and 2
s.add(And(
			SCHEDULE[2] >= SCHEDULE[0] + JOB_TIMES[0],
			SCHEDULE[2] >= SCHEDULE[1] + JOB_TIMES[1]
		)
	)

# Job 5 starts after 3 and 4
s.add(And(
			SCHEDULE[4] >= SCHEDULE[2] + JOB_TIMES[2],
			SCHEDULE[4] >= SCHEDULE[3] + JOB_TIMES[3]
		)
	)

# Job 7 starts after 3, 4 and 6
s.add(And(
			SCHEDULE[6] >= SCHEDULE[2] + JOB_TIMES[2],
			SCHEDULE[6] >= SCHEDULE[3] + JOB_TIMES[3],
			SCHEDULE[6] >= SCHEDULE[5] + JOB_TIMES[5]
		)
	)

# Job 8 may not start earlier than 5
s.add(SCHEDULE[7] >= SCHEDULE[4])

# Job 9 starts after 5 and 8
s.add(And(
			SCHEDULE[8] >= SCHEDULE[4] + JOB_TIMES[4],
			SCHEDULE[8] >= SCHEDULE[7] + JOB_TIMES[7]
		)
	)

# Job 11 starts after 10
s.add(SCHEDULE[10] >= SCHEDULE[9] + JOB_TIMES[9])

# Job 12 starts after 9 and 11
s.add(And(
			SCHEDULE[11] >= SCHEDULE[8] + JOB_TIMES[8],
			SCHEDULE[11] >= SCHEDULE[10] + JOB_TIMES[10]
		)
	)

# Jobs 5,7 and 10 mutually exclusive
for i in [4, 6, 9]:
	for j in [4, 6, 9]:
		if not (i==j):
			s.add(
					Or(
						(SCHEDULE[i] <= SCHEDULE[j] - JOB_TIMES[i]),
						(SCHEDULE[i] >= SCHEDULE[j] + JOB_TIMES[j])
						)
					)

# Total time restriction
for i in range(JOBS):
	s.add( SCHEDULE[i] <= TIME - JOB_TIMES[i])

if s.check() == sat:

	print(utils.sorted_model(s))
	utils.z3_to_smt2(s, "ass1-q3-a")
	utils.draw_schedule(JOBS, TIME, JOB_TIMES, s)

else:	
	print("Failed to solve")