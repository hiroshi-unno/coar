# Ablation configurations

Each configuration here is a base configuration with one or more optimisations removed, for the
ablation studies of the papers. A name reads `<base>_no_<what is removed>`; when the base is a
paper's configuration the paper name is used (`muval_ppm_popl27_no_scc`). Run them from the
repository root like any other solver configuration, for example

```bash
./_build/default/main.exe -c ./config/solver/ablation/muval_ppm_popl27_no_scc.json -p muclp <input>
```

Nested configuration files are named relative to the repository root (`./config/...`), so a file
here reads the same nested files it would read from `config/solver/`.

Rules:

- An ablation configuration states the switch it removes and whatever its base pins; every other
  field follows CoAR's defaults, so it moves with its base when a default changes.
- Ablation configurations are not A/B candidates and are never measured against the default to
  decide a default: they show what an optimisation contributes.
- `dbg_X.json` is the traced copy of `X.json` (tracing and self-checks on, nothing else changed).

| configuration | base | removes |
| --- | --- | --- |
| `muval_ppm_popl27_no_scc` | `muval_ppm_popl27` | SCC-wise parity relations (`use_scc`) |
| `muval_ppm_popl27_no_ad` | `muval_ppm_popl27` | priority reassignment by alternation depth (`alternation_depth`) |
| `muval_ppm_popl27_no_scc_ad` | `muval_ppm_popl27` | both of the above |
| `muval_ppm_no_erasure` | `muval_ppm` | quantifier erasure (the optimizer `enable_woerq.json`) |
| `muval_ppm_no_ad_erasure` | `muval_ppm` | alternation depth and quantifier erasure |
| `muval_ppm_no_scc_ad_erasure` | `muval_ppm` | SCC, alternation depth and quantifier erasure |
| `muval_no_cycle_restriction` | `muval` | ranks every least-fixpoint predicate, not only those on a cycle (`restrict_ranking_to_cycles` off; the WF reduction's counterpart of PPM's SCC restriction) |
| `muval_no_erasure` | `muval` | quantifier erasure |
| `muval_no_cycle_restriction_erasure` | `muval` | both of the above |
| `muval_no_optimizer` | `muval` | the muCLP optimizer (`disable.json`) |
