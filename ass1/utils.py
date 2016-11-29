import sys, os
from z3 import *
from pprint import *
import matplotlib.pyplot as plt

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

    sorted_list = []
    for var_str, var in sorted([(str(var), var) for var in model]):
        print(var, model[var])
        sorted_list.append((var, str(model[var])))
    return sorted_list

def draw_chip_design(CHIP_WIDTH,CHIP_HEIGHT,COMPONENT_DIM,solver):

    sorted_l = sorted_model(solver)
    plt.axis([0,CHIP_WIDTH,0,CHIP_HEIGHT])

    sorted_list = []

    for i in range(0,len(sorted_l),3):
        sorted_list.append((int(sorted_l[i][1]),
                            int(sorted_l[i+1][1]),
                            int(sorted_l[i+2][1])))


    for i in range(len(COMPONENT_DIM)):
        x = sorted_list[i][1]
        y = sorted_list[i][2]
        
        if sorted_list[i][0] == 0:
            w = COMPONENT_DIM[i][0]
            h = COMPONENT_DIM[i][1]
            
        else:
            w = COMPONENT_DIM[i][1]
            h = COMPONENT_DIM[i][0]

        plt.plot([x,x+w,x+w,x,x],[y,y,y+h,y+h,y])
        plt.text(x+(w/2),y+(h/2),str(i))

    plt.show()