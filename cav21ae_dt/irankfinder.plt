set size square
set terminal postscript eps enhanced color
set output 'irankfinder.eps'
set datafile separator ","
set xr[0.2:305]
set yr[0.2:305]
# set border 3
set border back
set xlabel font "Helvetica,30"
set ylabel font "Helvetica,30"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'irankfinder v1.3.2'
set ylabel 'MuVal'
plot x lc rgb "black" notitle, 'term-comp20.csv' u 3:"muval_dt_eager_nu_parallel_from_c" notitle pt 7 lc rgb "red"
