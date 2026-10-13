set terminal pdfcairo enhanced size 12cm,12cm
set output 'results/fig/fig_2b_pr_vs_wo_ad_its.pdf'
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
set xlabel 'MuValPPM'
set ylabel 'MuValPPM - AD'
plot x lc rgb "black" notitle, \
'results/comparison/pr_vs_wo_ad_its.csv' u (strcol(2) eq "timeout" ? (300) : (strcol(2) eq "YES" ? $3 : 1/0)) : \
                        (strcol(5) eq "timeout" ? (300) : (strcol(5) eq "YES" ? $6 : 1/0)) \
                        notitle pt 7 lc rgb "blue", \
'results/comparison/pr_vs_wo_ad_its.csv' u (strcol(2) eq "timeout" ? (strcol(5) eq "timeout" ? 1/0 : 300) : (strcol(2) eq "NO" ? $3 : 1/0)) : \
                        (strcol(5) eq "timeout" ? (300) : (strcol(5) eq "NO" ? $6 : 1/0)) \
                        notitle pt 6 lc rgb "red"
