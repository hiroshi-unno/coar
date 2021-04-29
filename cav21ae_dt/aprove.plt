set terminal postscript eps enhanced color
set output 'aprove.eps'
set datafile separator ","
set size square
set xr[0.2:305]
set yr[0.2:305]
set border back
set xlabel font "Helvetica,30"
set ylabel font "Helvetica,30"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'AProve'
set ylabel 'MuVal'
plot x lc rgb "black" notitle, 'term-comp20.csv' u (strcol(7) eq "MAYBE")?(300):($2):"muval_dt_eager_nu_parallel_from_c" notitle pt 7 lc rgb "red"
