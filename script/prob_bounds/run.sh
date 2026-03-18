pldi26_benchmarks=(
  "./benchmarks/QFL/ert_coin_flip_lb.qhes"
  "./benchmarks/QFL/ert_coin_flip_ub.qhes"
  "./benchmarks/QFL/ert_random_walk_lb.qhes"
  "./benchmarks/QFL/ert_random_walk_ub.qhes"
  "./benchmarks/QFL/ert_random_walk_2nd_lb.qhes"
  "./benchmarks/QFL/ert_random_walk_2nd_ub.qhes"
  "./benchmarks/QFL/feng23_ex30_lb.qhes"
  "./benchmarks/QFL/feng23_ex30_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig6_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig6_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig7_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig7_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig8_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig8_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig20_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig20_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig21_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig21_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig24_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig24_ub.qhes"
  "./benchmarks/QFL/hark19_ex7_lb.qhes"
  "./benchmarks/QFL/hark19_ex7_ub.qhes"
  "./benchmarks/QFL/hark19_ex49_lb.qhes"
  "./benchmarks/QFL/hark19_ex49_ub.qhes"
  "./benchmarks/QFL/olmedo18_intro_cwp1_lb.qhes"
  "./benchmarks/QFL/olmedo18_intro_cwp1_ub.qhes"
  "./benchmarks/QFL/olmedo18_intro_cwp2_lb.qhes"
  "./benchmarks/QFL/olmedo18_intro_cwp2_ub.qhes"
  "./benchmarks/QFL/feng23_ex19_lb_approx.qhes"
  "./benchmarks/QFL/feng23_ex19_ub.qhes"
  "./benchmarks/QFL/chatterjee22_fig14_lb_hint.qhes"
  "./benchmarks/QFL/chatterjee22_fig18_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig22_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig23_lb.qhes"
  "./benchmarks/QFL/hark19_ex53_lb_approx.qhes"
)

special_cases0=(
  "./benchmarks/QFL/hark19_ex7_ub.qhes"
  "./benchmarks/QFL/feng23_ex19_ub.qhes"
)

special_cases1=(
  "./benchmarks/QFL/hark19_ex7_lb.qhes"
  "./benchmarks/QFL/hark19_ex53_lb_approx.qhes"
  "./benchmarks/QFL/feng23_ex19_lb_approx.qhes"
)

special_cases2=(
  "./benchmarks/QFL/chatterjee22_fig18_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig22_lb.qhes"
  "./benchmarks/QFL/chatterjee22_fig24_lb.qhes"
)

special_cases3=(
  "./benchmarks/QFL/chatterjee22_fig14_lb_hint.qhes"
  "./benchmarks/QFL/chatterjee22_fig24_ub.qhes"
)

for file in "${pldi26_benchmarks[@]}"; do
    echo ""
    echo "$file"

    if [[ " ${special_cases0[@]} " =~ " ${file} " ]]; then # C3
        echo "Config C3"
        config="./config/solver/muval_quant_polyqent_deg1_1_cond_eps.json"
    elif [[ " ${special_cases1[@]} " =~ " ${file} " ]]; then # C2
        echo "Config C2"
        config="./config/solver/muval_quant_polyqent_deg1_cond_eps.json"
    elif [[ " ${special_cases2[@]} " =~ " ${file} " ]]; then # C1
        echo "Config C1"
        config="./config/solver/muval_quant_polyqent_deg1_eps.json"
    elif [[ " ${special_cases3[@]} " =~ " ${file} " ]]; then # B
        echo "Config B"
        config="./config/solver/muval_quant_polyqent_deg1.json"
    else # A
        echo "Config A"
        config="./config/solver/muval_quant_polyqent_deg3.json"
    fi

    time timeout 180 ./_build/default/main.exe -c "$config" -p qfl "$file"
done
