from z3 import *
import utils

ACTORS = 6

CHARACTERS = {}
CHARACTERS["John"] = "Male"
CHARACTERS["Alex"] = "Male"
CHARACTERS["Father"] = "Male"
CHARACTERS["Young Man"] = "Young male"
CHARACTERS["Stacy"] = "Female"
CHARACTERS["Mother"] = "Female"
CHARACTERS["Grandma"] = "Female"
CHARACTERS["Woman #1"] = "Female"
CHARACTERS["Lawyer"] = "Female"

LEADING_CHARACTERS = {"Stacy"}

MAX_CHARACTERS = 2

SCENES = {}

SCENES = [
		{"name": "Act I Opening", "chars": ["Father", "Mother", "Grandma"]},
		{"name": "Theatre Lobby", "chars": ["Stacy", "John"]},
		{"name": "An Audition", "chars": ["Woman #1", "Alex", "John", "Lawyer", "Stacy"]},
		{"name": "Stacy's Apartment", "chars": ["Stacy", "Young Man"]}
	]

TYPES = []

for char in CHARACTERS:
	t = CHARACTERS[char]

	if t not in TYPES:
		TYPES.append(t)

CharType = Datatype('CharType')

for t in TYPES:
	CharType.declare(t)

CharType, ts = EnumSort('CharType', TYPES)

types = {}

for char in CHARACTERS:
	for t in ts:
		if(str(CHARACTERS[char]) == str(t)):
			types[char] = t

actorOf = {char: Int('actorOf[%s]' % (char)) for char in CHARACTERS}

typeOf = {actor: Const('typeOf[%d]' % (actor), CharType) for actor in range(ACTORS)}

# print(actorOf)
s = Solver()

# All characters are played by an actor with ID between 0 and the number of actors
for char in CHARACTERS:
	s.add(actorOf[char] >= 0, actorOf[char] < ACTORS)

# An actor cannot play more than a max number of characters
for i in range(ACTORS):
	s.add(Sum([If(actorOf[char] == i, 1, 0) for char in CHARACTERS]) <= MAX_CHARACTERS)

# Leading characters are played by the actors in the begining of the list.
for idx, lc in enumerate(LEADING_CHARACTERS):
	s.add(actorOf[lc] == idx)

	# Actors that play a leading character can't play other characters
	for char in CHARACTERS:
		if(char != lc):
			s.add(actorOf[lc] != actorOf[char])

# Actor cannot play two different characters in the same scene
s.add(Distinct([actorOf[char] for char in SCENES[0]["chars"]]))

for idx, scene in enumerate(SCENES[1:], 1):
	s.add(Distinct([actorOf[char] for char in set(SCENES[idx]["chars"] + SCENES[idx-1]["chars"])]))

for char in CHARACTERS:
	for actor in range(ACTORS):
		s.add(Implies(actorOf[char] == actor, typeOf[actor] == types[char]))

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
# print(s.to_smt2())
