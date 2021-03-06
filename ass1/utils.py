import sys, os
from z3 import *
from pprint import *
import matplotlib.pyplot as plt
from fractions import Fraction

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
        sorted_list.append((var, str(model[var])))
    return sorted_list

def draw_chip_design(CHIP_WIDTH, CHIP_HEIGHT, COMPONENT_DIM, POWER_COMPONENTS, solver, param):

    sorted_l = sorted_model(solver)
    plt.axis([0,CHIP_WIDTH,0,CHIP_HEIGHT])

    sorted_list = []

    for i in range(0, len(sorted_l), 4):
        sorted_list.append(
            (
                float(sum(Fraction(s) for s in sorted_l[i][1].split())),
                float(sum(Fraction(s) for s in sorted_l[i+1][1].split())),
                float(sum(Fraction(s) for s in sorted_l[i+2][1].split())),
                float(sum(Fraction(s) for s in sorted_l[i+3][1].split()))
            )
        )

    for i in range(len(COMPONENT_DIM)):
        x = sorted_list[i][param['X']]
        y = sorted_list[i][param['Y']]
        
        w = sorted_list[i][param['Width']]
        h = sorted_list[i][param['Height']]

        plt.plot([x,x+w,x+w,x,x],[y,y,y+h,y+h,y])
        
        if(i<POWER_COMPONENTS):
            plt.text(x+(w/2),y+(h/2),("P_"+str(i+1)))
        else:
            plt.text(x+(w/2),y+(h/2),("C_"+str(i+1-POWER_COMPONENTS)))
    plt.show()


def draw_schedule(JOBS, TIME, JOB_TIMES, solver):

    sorted_l = sorted_model(solver)
    plt.axis([0,TIME+5,0,(JOBS+1)*2])

    sorted_list = []
    for i in range(JOBS):
        sorted_list.append(float(sum(Fraction(s) for s in sorted_l[i][1].split())))
        x = sorted_list[i]
        y = i*2
        w = JOB_TIMES[i]
        h = 1.5
        plt.plot([x,x+w,x+w,x,x],[y,y,y+h,y+h,y])
        plt.text(x+(w/2),y+(h/2),("J_"+str(i+1)))

    plt.show()

def abs(x):
    return If(x >= 0,x,-x)





