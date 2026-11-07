# OptPCSat at its code defaults, one run per side condition (since 2026-10-31 the
# solver variants this script compared all run the defaults, so each side condition is one run).
echo "call optpcsat_nc:"
./script/popl2023opt/optpcsat_nc_600.sh >./popl2023opt_optpcsat_nc_600_$1.csv
