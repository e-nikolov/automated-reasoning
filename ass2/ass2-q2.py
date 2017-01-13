from functools import *

from z3 import *
import utils

ALPHABET = ["a", "b"]

s = ""

STATES = 7
LANGUAGE = ['aa', 'bb', 'aba', 'baa', 'abab', 'babb', 'bbba']

MAX_DEPTH = reduce(lambda acc, x: len(x) if len(x) > acc else acc, LANGUAGE, 0)

nfa = {c: [[Bool('nfa[%s][%d][%d]' % (c, i, j)) for j in range(STATES)] for i in range(STATES)] for c in ALPHABET}
acc = [Bool('acc[%d]' % (i)) for i in range(STATES)]

s = Solver()

def constraints(idx, preds, word):
    if idx == len(word):
        # print(preds)
        p = []
        x = 0
        for i, pred in enumerate(preds):
            p += [nfa[word[i]][x][pred]]
            x = pred

        p += [acc[x]]

        # print(p)
        if word in LANGUAGE:
            return And(p)
        else:
            return Not(And(p))

    p = []

    for i in range(STATES):
        p += [constraints(idx + 1, preds + [i], word)]

    # print(word)
    # print(p)
    if word in LANGUAGE:
        return Or(p)
    else:
        return And(p)

def words(idx, word):

    p = constraints(0, [], word)

    if len(word) > 0:
        if word in LANGUAGE:
            print("ACC")
        else:
            print("NCC")

    # print(p)
    print(word)
    s.add(p)

    if idx == MAX_DEPTH:
        # print(word)
        return

    words(idx + 1, word + 'a')
    words(idx + 1, word + 'b')

words(0, "")

# print("asserted constraints...")
# for c in s.assertions():
    # print(c)
print()
print()

if s.check() == sat:
    for item in utils.sorted_model(s):
        print(item)

    utils.z3_to_smt2(s, "ass1-q1")

else:
    print("Failed to solve")
