set terminal pdfcairo enhanced size 12cm,12cm
set output 'results/fig/fig_1a_pr_vs_dwf_popl23.pdf'
set datafile separator ","
set size square
set xr[0.2:305]
set yr[0.2:305]
set border back
set xlabel font "Times New Roman,24"
set ylabel font "Times New Roman,24"
set xtics font ", 18"
set ytics font ", 18"
set xtics nomirror
set ytics nomirror
set logscale xy 10
set xlabel 'MuValPPM (this paper)'
set ylabel 'MuStrat (POPL 25)'
plot x lc rgb "black" notitle, \
'results/comparison/pr_vs_dwf_popl23.csv' u (strcol(2) eq "timeout" ? (300) : (strcol(2) eq "valid" ? $3 : 1/0)) : \
                        (strcol(5) eq "timeout" ? (300) : (strcol(5) eq "valid" ? $6 : 1/0)) \
                        notitle pt 7 lc rgb "blue", \
'results/comparison/pr_vs_dwf_popl23.csv' u (strcol(2) eq "timeout" ? (strcol(5) eq "timeout" ? 1/0 : 300) : (strcol(2) eq "invalid" ? $3 : 1/0)) : \
                        (strcol(5) eq "timeout" ? (300) : (strcol(5) eq "valid" ? $6 : 1/0)) \
                        notitle pt 6 lc rgb "red"
