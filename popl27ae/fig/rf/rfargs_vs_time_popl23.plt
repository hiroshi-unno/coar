set terminal pdfcairo enhanced size 12cm,12cm
set output 'results/fig/rfargs_vs_time_popl23.pdf'
set datafile separator ","
set size square
# TO is the run's time limit in seconds, the mark every timeout is drawn at;
# rankcount.sh passes it as gnuplot -e "TO=<seconds>". Default 300.
if (!exists("TO")) TO = 300
set yr[0.1:TO*305.0/300]
set border back
set xlabel font "Times New Roman,24"
set ylabel font "Times New Roman,24"
set xtics font ", 18"
set ytics font ", 18"
set xtics nomirror
set ytics nomirror
set logscale xy 10
# a count of 0 has no place on a log axis: it is drawn at Z, labelled 0
Z = 0.6
set xtics add ("0" Z)
set xr[0.5:2000]
set xlabel '#arguments of ranking functions'
set ylabel 'MuValPPM (s)'
# columns: name, verdict, time, primal and dual ranking functions, primal and dual arguments (6, 7).
# valid is the primal's answer (blue, its argument count), invalid the dual's (red, its argument count);
# a timeout is drawn once per side at TO.
plot 'results/rankcount/popl2023mod.csv' u (strcol(2) eq "valid" || strcol(2) eq "timeout" ? ($6 == 0 ? Z : $6) : 1/0) : \
                        (strcol(2) eq "timeout" ? (TO) : (strcol(2) eq "valid" ? $3 : 1/0)) \
                        with points notitle pt 7 lc rgb "blue", \
     'results/rankcount/popl2023mod.csv' u (strcol(2) eq "invalid" || strcol(2) eq "timeout" ? ($7 == 0 ? Z : $7) : 1/0) : \
                        (strcol(2) eq "timeout" ? (TO) : (strcol(2) eq "invalid" ? $3 : 1/0)) \
                        with points notitle pt 6 lc rgb "red"
