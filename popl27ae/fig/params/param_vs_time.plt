# Solving time of MuValPPM (SCC & AD) against one benchmark parameter, a strip plot.
# rankcount.sh passes, with gnuplot -e: CSV (results/params/<corpus>.csv), OUT (the pdf), COL (the
# parameter's column: 4 alternation depth, 5 nontrivial SCCs, 6 ranking functions), XLABEL, and TO,
# the run's time limit in seconds, at which every timeout is drawn (default 300).  With LOGX=1 the x axis
# is logarithmic and a value of 0 is drawn at the tick labelled 0.
if (!exists("TO")) TO = 300
if (!exists("LOGX")) LOGX = 0
set terminal pdfcairo enhanced size 12cm,12cm
set output OUT
set datafile separator ","
set size square
set yr[0.1:TO*305.0/300]
set border back
set xlabel font "Times New Roman,24"
set ylabel font "Times New Roman,24"
set xtics font ", 18"
set ytics font ", 18"
set xtics nomirror
set ytics nomirror
set logscale y 10
set xlabel XLABEL
Z = 0.6
if (LOGX) {
  set logscale x 10
  set xtics add ("0" Z)
  set xr[0.45:*]
} else {
  set offsets 0.5, 0.5, 0, 0
}
set ylabel 'MuValPPM (s)'
# a point is spread sideways around its value so that equal values stay readable: within +-0.3 on a
# linear axis, by a factor within exp(+-0.15) on a logarithmic one
J = 0.3
jit(x) = LOGX ? (x == 0 ? Z : x) * exp(0.15 * (2 * rand(0) - 1)) : x + J * (2 * rand(0) - 1)
x0 = rand(1)
# columns: name, verdict, time (a timeout at TO), AD, nontrivial SCCs, ranking functions
plot CSV u (strcol(2) eq "valid" && strcol(COL) ne "" ? jit(column(COL)) : 1/0):3 with points notitle pt 7 ps 0.5 lc rgb "blue", \
     CSV u (strcol(2) eq "invalid" && strcol(COL) ne "" ? jit(column(COL)) : 1/0):3 with points notitle pt 6 ps 0.5 lc rgb "red", \
     CSV u (strcol(2) eq "timeout" && strcol(COL) ne "" ? jit(column(COL)) : 1/0):(TO) with points notitle pt 2 ps 0.5 lc rgb "black"
