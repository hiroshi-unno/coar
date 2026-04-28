set terminal pdfcairo enhanced size 12cm,12cm
set output 'LRA_mucyc_vs_z3.pdf'
set datafile separator ","
set size square
set xr[0.2:305]
set yr[0.2:305]
set border back
set xlabel font "Times New Roman,25"
set ylabel font "Times New Roman,25"
set xtics font ", 20"
set ytics font ", 20"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'MuCyc (Progress)'
set ylabel 'Z3 4.15.2'
plot x lc rgb "black" notitle, \
'< paste LRA_mucyc.csv LRA_z3.csv' \
u (strcol(2) eq "timeout" ? (300) : (strcol(2) eq "sat" ? $3 : 1/0)) : \
  (strcol(5) eq "timeout" ? (300) : (strcol(5) eq "sat" ? $6 : 1/0)) \
  notitle pt 7 lc rgb "blue", \
'' \
u (strcol(2) eq "timeout" ? (strcol(5) eq "timeout" ? 1/0 : 300) : (strcol(2) eq "unsat" ? $3 : 1/0)) : \
  (strcol(5) eq "timeout" ? (300) : (strcol(5) eq "unsat" ? $6 : 1/0)) \
  notitle pt 6 lc rgb "red"
