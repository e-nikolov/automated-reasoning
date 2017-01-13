from functools import *

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
MAX_DEPTH = reduce(lambda acc, x: len(x) if len(x) > acc else acc, LANGUAGE, 0)

print("Depth: ", MAX_DEPTH)

nfa = [[[Bool('nfa[%s][%d][%d]' % (c, i, j)) for i in range(STATES)] for j in range(STATES)] for c in ALPHABET] 
acc = [Bool('acc[%d]' % (i)) for i in range(STATES)]

s = Solver()


def rec(state, s):
    print(s)

    if idx == MAX_DEPTH:
        if(s in LANGUAGE):


        return And(preds)

    rec(idx + 1, s + 'a')
    rec(idx + 1, s + 'b')

    [nfa[s[-1]][state][next_state] for next_state in range(STATES)]



for word in LANGUAGE:
	states = [0]
	
	for c in word:
		for state in states:
			s.add(Or([(nfa[IDX[c][state][i]] == True) for i in range(STATES)]))


print("asserted constraints...")
for c in s.assertions():
    print(c)
print()
print()

if s.check() == sat:
    for item in utils.sorted_model(s):
        print(item)

    utils.z3_to_smt2(s, "ass1-q1")

else:
    print("Failed to solve")
