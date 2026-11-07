set terminal pdfcairo enhanced size 12cm,12cm
set output 'LIA_mucyc_qsat_deepest_own_projected_repeatedly_vs_mucyc_qsat_deepest_own.pdf'
set datafile separator ","
set size square
# TO is the run's time limit in seconds, the mark every timeout is drawn at;
# the plotting driver passes it as gnuplot -e "TO=<seconds>". Default 300.
if (!exists("TO")) TO = 300
set xr[0.2:TO*305.0/300]
set yr[0.2:TO*305.0/300]
set border back
set xlabel font "Times New Roman,25"
set ylabel font "Times New Roman,25"
set xtics font ", 20"
set ytics font ", 20"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'MuCyc (Progress)'
set ylabel 'MuCyc (Non-Progress)'
plot x lc rgb "black" notitle, \
'LIA_mucyc_qsat_deepest_own_projected_repeatedly_vs_mucyc_qsat_deepest_own.csv' \
u (strcol(2) eq "timeout" ? (TO) : (strcol(2) eq "sat" ? $3 : 1/0)) : \
  (strcol(5) eq "timeout" ? (TO) : (strcol(5) eq "sat" ? $6 : 1/0)) \
  notitle pt 7 lc rgb "blue", \
'' \
u (strcol(2) eq "timeout" ? (strcol(5) eq "timeout" ? 1/0 : TO) : (strcol(2) eq "unsat" ? $3 : 1/0)) : \
  (strcol(5) eq "timeout" ? (TO) : (strcol(5) eq "unsat" ? $6 : 1/0)) \
  notitle pt 6 lc rgb "red"
