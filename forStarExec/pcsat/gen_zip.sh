#! /bin/bash

cp -f `which hoice` ./bin
cp `ldd bin/hoice | grep -v "linux-vdso\|ld-linux-x86-64" | cut -f 3 --delim " "` ./bin
cp -f `which z3` ./bin
cp `ldd bin/z3 | grep -v "linux-vdso\|ld-linux-x86-64" | cut -f 3 --delim " "` ./bin
cp -f ../../_build/default/main.exe ./bin
cp `ldd bin/main.exe | grep -v "linux-vdso\|ld-linux-x86-64" | cut -f 3 --delim " "` ./bin
cp -f -r ../../config ./bin
rm pcsat.zip
zip pcsat -r bin starexec_description.txt
