from z3 import *

nuzzles = Int('nuzzles')
y = Int('y')
s = Solver()
s.add(nuzzles + y > 5, nuzzles > 1, y > 1)
print(s.check())
print(s.model())
# print(s.to_smt2())