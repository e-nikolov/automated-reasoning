from z3 import *
import utils

ACTORS = 12

CHARACTERS = {
		"Actor": "Male",
		"Alex": "Male",	
		"Alfreda": "Female",	
		"Fat Man": "Male",	
		"Father": "Male",	
		"Grandma": "Female",	
		"Husband": "Male",	
		"Jack Holdman": "Male",	
		"John": "Male",	
		"M. Sweetwater": "Female",	
		"Man #1": "Male",	
		"Man #2": "Male",
		"Mother": "Female",	
		"New Actor": "Male",	
		"New Actress": "Female",	
		"Office Worker": "Female",	
		"Older Man": "Male",	
		"Stacy": "Female",	
		"Thom": "Young Male",	
		"Wife": "Female",	
		"Woman #1": "Female",	
		"Woman #2": "Female",	
		"Woman w/Glasses": "Female",	
		"Young Man": "Young Male"
	}


LEADING_CHARACTERS = {"Stacy", "Alex", "John"}

MAX_CHARACTERS = 3

SCENES = {}

SCENES = [
	{"name": "Act I Opening", "chars": ["Father","Mother","Grandma","Woman w/Glasses","Young Man"]},
	{"name": "Theatre Lobby", "chars": ["Stacy","John"]},
	{"name": "An Audition", "chars": ["Woman #1","Woman #2","John"]},
	{"name": "John's Apartment", "chars": ["John"]},
	{"name": "Another Audition #1", "chars": ["Fat Man","John"]},
	{"name": "Another Audition #2", "chars": ["John","Older Man"]},
	{"name": "A Theatre Lobby", "chars": ["Alex","John"]},
	{"name": "An Upscale Restaurant", "chars": ["John","Husband","Wife","Man #1","Man #2"]},
	{"name": "Studio Office", "chars": ["Office Worker","John","Actor"]},
	{"name": "Scene Study", "chars": ["Jack Holdman","New Actress","John"]},
	{"name": "Acting Studio", "chars": ["Alex","John"]},
	{"name": "Another Scene Study", "chars": ["M. Sweetwater","New Actor","John"]},
	{"name": "City Street", "chars": ["Stacy","John"]},
	{"name": "Theatre Lobby", "chars": ["Alex","John","Stacy"]},
	{"name": "Heartbeat Theatre", "chars": ["John","Alfreda","Thom"]}
]

ch = []

for scene in SCENES:
	scene

	ch = list(set(ch + scene["chars"]))

print(ch)


TYPES = []

for char in CHARACTERS:
	t = CHARACTERS[char]

	if t not in TYPES:
		TYPES.append(t)

CharType = Datatype("CharType")

for t in TYPES:
	CharType.declare(t)

CharType, ts = EnumSort("CharType", TYPES)

types = {}

for char in CHARACTERS:
	for t in ts:
		if(str(CHARACTERS[char]) == str(t)):
			types[char] = t

actorOf = {char: Int("actorOf[%s]" % (char)) for char in CHARACTERS}

typeOf = {actor: Const("typeOf[%d]" % (actor), CharType) for actor in range(ACTORS)}

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

	# Actors that play a leading character can"t play other characters
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
