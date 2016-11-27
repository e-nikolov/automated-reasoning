import sys, os


FOLDER_NAME = "smt2"
LOGIC_STR = "(set-logic QF_UFLRA)"
MODEL_STR = "(get-model)"
class helpers():

	def __init__(self):
		
		# No use now, maybe some other helper function will use constructor
		self.__InitSuccess = True

	def z3_to_smt2(self, smt2_string, filename):

		if not self.__InitSuccess:
			sys.exit("Helpers Init error")

		# Create the smt files in a folder called FOLDER_NAME
		if not os.path.exists(FOLDER_NAME):
			os.makedirs(FOLDER_NAME)
		os.chdir(FOLDER_NAME)

		output_file_name = filename + ".smt2"
		output_file = open( output_file_name, 'w')
		output_file_content  = str(smt2_string)
		index = output_file_content.find('\n')
		output_file_content = output_file_content[:index+1] + LOGIC_STR + \
							 "\n" + output_file_content[index:] + \
							 MODEL_STR + "\n"

		output_file.write(output_file_content)






