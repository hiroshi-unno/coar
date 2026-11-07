# The run of this corpus at MuVal's default configuration (since 2026-10-31 the old fixed
# configurations this script compared all run the default, so they are one run).
echo "call muval (default configuration):"
./script/term20cint/muval_1200.sh >./termcomp20cint_muval_1200_$1.csv
