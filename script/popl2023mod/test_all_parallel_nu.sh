# The run of this corpus at MuVal's default configuration (since 2026-10-31 the old fixed
# configurations this script compared all run the default, so they are one run).
echo "call muval (default configuration):"
./script/popl2023mod/muval_600.sh >./popl2023mod_muval_600_$1.csv
