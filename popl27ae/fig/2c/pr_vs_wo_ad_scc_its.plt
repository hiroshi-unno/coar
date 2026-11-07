set terminal pdfcairo enhanced size 12cm,12cm
set output 'results/fig/fig_2c_pr_vs_wo_ad_scc_its.pdf'
set datafile separator ","
set size square
# TO is the run's time limit in seconds, the mark every timeout is drawn at;
# the plotting driver passes it as gnuplot -e "TO=<seconds>". Default 300.
if (!exists("TO")) TO = 300
set xr[0.2:TO*305.0/300]
set yr[0.2:TO*305.0/300]
set border back
set xlabel font "Times New Roman,24"
set ylabel font "Times New Roman,24"
set xtics font ", 18"
set ytics font ", 18"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'MuValPPM'
set ylabel 'MuValPPM - AD - SCC'
plot x lc rgb "black" notitle, \
'results/comparison/pr_vs_wo_ad_scc_its.csv' u (strcol(2) eq "timeout" ? (TO) : (strcol(2) eq "valid" ? $3 : 1/0)) : \
                        (strcol(5) eq "timeout" ? (TO) : (strcol(5) eq "valid" ? $6 : 1/0)) \
                        with points notitle pt 7 lc rgb "blue", \
'results/comparison/pr_vs_wo_ad_scc_its.csv' u (strcol(2) eq "timeout" ? (strcol(5) eq "timeout" ? 1/0 : TO) : (strcol(2) eq "invalid" ? $3 : 1/0)) : \
                        (strcol(5) eq "timeout" ? (TO) : (strcol(5) eq "invalid" ? $6 : 1/0)) \
                        with points notitle pt 6 lc rgb "red"
