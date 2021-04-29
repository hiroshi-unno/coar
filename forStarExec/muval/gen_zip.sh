#! /bin/bash

cp -f `which clang` ./bin
cp `ldd bin/clang | grep -v "linux-vdso\|ld-linux-x86-64" | cut -f 3 --delim " "` ./bin
cp -f ~/llvm2kittel/build/llvm2kittel ./bin
cp `ldd bin/llvm2kittel | grep -v "linux-vdso\|ld-linux-x86-64" | cut -f 3 --delim " "` ./bin
cp -f ../../_build/default/main.exe ./bin
cp `ldd bin/main.exe | grep -v "linux-vdso\|ld-linux-x86-64" | cut -f 3 --delim " "` ./bin
cp -f -r ../../config ./bin
rm muval.zip
zip muval -r bin starexec_description.txt
