#!/usr/bin/env python
# coding: utf-8

# In[1]:


from datetime import datetime
import subprocess
import re
import os
from os import listdir
from os.path import isfile, join

# set the working directory for prolog.
working_directory = '/Users/lixue/GoogleDrive/01PHD/01program/eclipse-workspace/ABC_Clean/src/'
# set the path of the faulty theories to repair.
evaluationFiles = working_directory+'aaai'
TheoryFiles = sorted([f for f in listdir(evaluationFiles) if isfile(join(evaluationFiles, f))])
print(TheoryFiles)

def main():
    i = 1
    yLineH =[]
    yLineNoh =[]
    diff1 =[]
    diff2 = []
    while i < len(TheoryFiles):
        Theory = TheoryFiles[i]
        print(Theory)
    
        proc =subprocess.run(["swipl", "-l", "aaai/"+Theory, "-g", "abc", "-g", "halt"], 
                             timeout=None, cwd = working_directory, stdout=subprocess.PIPE)
        i+=1
    print('finished')






