from datetime import datetime
import subprocess
import re
import os
from os import listdir
from os.path import isfile, join

# set the working directory for prolog.
working_directory = 'C:/Users/edmun/Downloads/xue/code/'
# input the folder where the faulty theories to repair are.
def main(cat):
    i = 1
    yLineH =[]
    yLineNoh =[]
    diff1 =[]
    diff2 = []
    evaluationFiles = working_directory+cat
    TheoryFiles = sorted([f for f in listdir(evaluationFiles) if isfile(join(evaluationFiles, f))])
    print(TheoryFiles)
    while i < len(TheoryFiles):
        Theory = TheoryFiles[i]
        print(Theory)
    
        proc =subprocess.run(["swipl", "-l", cat+Theory, "-g", "abc", "-g", "halt"], 
                             timeout=None, cwd = working_directory, stdout=subprocess.PIPE)
        i+=1
    print('finished')
