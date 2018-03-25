#!/bin/bash

# Prepare StdLib

cp java/src/* bin/
cd bin && rm -rf *.class && javac -Xdiags:verbose -cp AeminiumRuntime.jar {A,J,F,R}.java && cd ..

for FILE in $(tree -fi examples | grep -v automatic | grep .ae); 
do
   python3 -m aeon $FILE && cd bin && javac -Xdiags:verbose -cp .:AeminiumRuntime.jar E.java && cd ..
   
   if [[ $? -ne 0 ]]; then
      echo "FAILED $FILE"
      break
   else
      printf "."
   fi
done
echo
