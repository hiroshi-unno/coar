SCRIPT_DIR=$(cd $(dirname $0); pwd)

# FuncTion Termination Verification Benchmarks
## TB
timeout=300 options='-c ./config/solver/pcsat_tb.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/pcsp_lia/termination/*.clp | LC_ALL=C sort
## DT
timeout=300 options='-c ./config/solver/pcsat_dt.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/pcsp_lia/termination/*.clp | LC_ALL=C sort

# SyGuS-Comp Invariant Synthesis Track 2018
## TB
timeout=300 options='-c ./config/solver/pcsat_tb.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2018/Inv_Track/*.sl | LC_ALL=C sort
## DT
timeout=300 options='-c ./config/solver/pcsat_dt.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2018/Inv_Track/*.sl | LC_ALL=C sort

# CHC-COMP2019 (LIA-nonlin)
## TB
timeout=300 options='-c ./config/solver/pcsat_tb.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp19/lia-nonlin/*.smt2 | LC_ALL=C sort
## DT
timeout=300 options='-c ./config/solver/pcsat_dt.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp19/lia-nonlin/*.smt2 | LC_ALL=C sort

# SyGuS-Comp Invariant Synthesis Track 2017
## TB
timeout=300 options='-c ./config/solver/pcsat_tb.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2017/Inv_Track/*.sl | LC_ALL=C sort
## DT
timeout=300 options='-c ./config/solver/pcsat_dt.json -p sygus' $SCRIPT_DIR/run_bench.sh benchmarks/sygus-comp/comp/2017/Inv_Track/*.sl | LC_ALL=C sort

# CHC-COMP2018 (LIA)
## TB
timeout=300 options='-c ./config/solver/pcsat_tb.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp18/lia/*.smt2 | LC_ALL=C sort
## DT
timeout=300 options='-c ./config/solver/pcsat_dt.json -p pcsp' $SCRIPT_DIR/run_bench.sh benchmarks/chc-comp18/lia/*.smt2 | LC_ALL=C sort
