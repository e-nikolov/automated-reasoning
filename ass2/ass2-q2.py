

# (0_a_1 == 1 and ((1_a_0 == 1 and 0_accepting == 1) or (1_a_2 == 1 and 2_accepting == 1))) or 
# (0_a_2 == 1 and ((2_a_0 == 1 and 0_accepting == 1) or (2_a_1 == 1 and 1_accepting == 1)))


from z3 import *
import utils

STATES = 3
ALPHABET = ['a', 'b']

IDX = {}
for idx, char in enumerate(ALPHABET):
	IDX[char] = idx


LANGUAGE = ['aa', 'bb', 'aba', 'baa', 'abab', 'babb', 'bbba']

nfa = [[[Bool('nfa[%s][%d][%d]' % (c, i, j)) for i in range(STATES)] for j in range(STATES)] for c in ALPHABET] 

s = Solver()

for word in LANGUAGE:
	states = [0]
	
	for c in word:
		for state in states:
			s.add(Or([(nfa[IDX[c][state][i]] == True) for i in range(STATES)]))

