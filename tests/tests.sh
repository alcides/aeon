#!/bin/bash

# Prepare StdLib

cp java/src/* bin/
cd bin && rm -rf *.class && javac -Xdiags:verbose -cp AeminiumRuntime.jar {A,J,F,R}.java && cd ..

for FILE in $(tree -fi examples/tests | grep .ae); 
do
	if [[ $FILE == *.aen ]]; then
	   { python3 -m aeon $FILE && cd bin && javac -Xdiags:verbose -cp .:AeminiumRuntime.jar E.java && cd ..; } > /dev/null &> /dev/null
		if [[ $? -ne 0 ]]; then
			printf "."
		else
	      echo "ACCEPTED WRONG: $FILE"
	      break
		fi
	else
	   { python3 -m aeon $FILE && cd bin && javac -Xdiags:verbose -cp .:AeminiumRuntime.jar E.java && cd ..; }
		if [[ $? -ne 0 ]]; then
			echo "FAILED $FILE"
			break
		else
			printf "."		
		fi
	fi
done
echo
