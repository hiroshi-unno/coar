#!/bin/bash

cd `dirname $0`; cd ..
echo -e "DoubleSquareNI_hFT:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/DoubleSquareNI_hFT.clp
echo -e "\n\nDoubleSquareNI_hTF:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/DoubleSquareNI_hTF.clp
echo -e "\n\nDoubleSquareNI_hFF:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/DoubleSquareNI_hFF.clp
echo -e "\n\nDoubleSquareNI_hTT:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/DoubleSquareNI_hTT.clp
#echo -e "\n\nCotermIntro:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb.json -p pcsp benchmarks/pfwnCSP/cav2021rel/CotermIntro.clp
echo -e "\n\nCotermIntro1:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb.json -p pcsp benchmarks/pfwnCSP/cav2021rel/CotermIntro1.clp
echo -e "\n\nCotermIntro2:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb.json -p pcsp benchmarks/pfwnCSP/cav2021rel/CotermIntro2.clp
#echo -e "\n\nTS_GNI_hFT:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TS_GNI_hFT.clp
echo -e "\n\nTS_GNI_hFT_hint:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TS_GNI_hFT_hint.clp
echo -e "\n\nTS_GNI_hTF:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TS_GNI_hTF.clp
echo -e "\n\nTS_GNI_hFF:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TS_GNI_hFF.clp
#echo -e "\n\nTS_GNI_hTT:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TS_GNI_hTT.clp
echo -e "\n\nTS_GNI_hTT_hint:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TS_GNI_hTT_hint.clp
echo -e "\n\nHalfSquareNI:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/HalfSquareNI.clp
echo -e "\n\nArrayInsert:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop4.json -p pcsp benchmarks/pfwnCSP/cav2021rel/ArrayInsert.clp
#echo -e "\n\nSquareSum:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop3.json -p pcsp benchmarks/pfwnCSP/cav2021rel/SquareSum.clp
echo -e "\n\nSquareSum_hint:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop3.json -p pcsp benchmarks/pfwnCSP/cav2021rel/SquareSum_hint.clp
echo -e "\n\nSimpleTS_GNI1:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb.json -p pcsp benchmarks/pfwnCSP/cav2021rel/SimpleTS_GNI1.clp
echo -e "\n\nSimpleTS_GNI2:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb.json -p pcsp benchmarks/pfwnCSP/cav2021rel/SimpleTS_GNI2.clp
echo -e "\n\nInfBranchTS_GNI:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb.json -p pcsp benchmarks/pfwnCSP/cav2021rel/InfBranchTS_GNI.clp
#echo -e "\n\nTI_GNI_hFT:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TI_GNI_hFT.clp
echo -e "\n\nTI_GNI_hFT_hint:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TI_GNI_hFT_hint.clp
echo -e "\n\nTI_GNI_hTF:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TI_GNI_hTF.clp
echo -e "\n\nTI_GNI_hFF:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TI_GNI_hFF.clp
#echo -e "\n\nTI_GNI_hTT:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TI_GNI_hTT.clp
echo -e "\n\nTI_GNI_hTT_hint:"; time timeout 1200 _build/default/main.exe -c config/solver/pcsat_tb_hyperprop2.json -p pcsp benchmarks/pfwnCSP/cav2021rel/TI_GNI_hTT_hint.clp
