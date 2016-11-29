import sys, os
from z3 import *
from pprint import *

FOLDER_NAME = "smt2"
LOGIC_STR = "(set-logic %s)"
MODEL_STR = "(get-model)"

# No use now, maybe some other helper function will use constructor
__InitSuccess = True

def z3_to_smt2(solver, filename, logic="QF_UFLIA"):

    if not __InitSuccess:
        sys.exit("Helpers Init error")

    # Create the smt files in a folder called FOLDER_NAME
    if not os.path.exists(FOLDER_NAME):
        os.makedirs(FOLDER_NAME)
    os.chdir(FOLDER_NAME)

    output_file_name = filename + ".smt2"
    output_file = open(output_file_name, 'w')
    
    output_file_content  = str(solver.to_smt2())
    index = output_file_content.find('\n')
    output_file_content = output_file_content[:index+1] + LOGIC_STR % logic + \
                          output_file_content[index:] + \
                          MODEL_STR + "\n"

    output_file.write(output_file_content)

def sorted_model(solver):
    model = solver.model()

    for var_str, var in sorted([(str(var), var) for var in model]):
        print(var, model[var])

