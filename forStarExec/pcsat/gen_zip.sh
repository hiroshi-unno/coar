#! /bin/bash

cp -f ../../_build/default/main.exe ./bin
cp -f -r ../../config ./bin
rm pcsat.zip
zip pcsat -r bin starexec_description.txt
