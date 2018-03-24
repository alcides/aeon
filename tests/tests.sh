#!/bin/bash

for FILE in $(tree -fi examples | grep .ae); 
do
   ./ae $FILE
   if [ -neq $@ 0 ]; then
      echo "FAILED $FILE"
      break
   fi
done
