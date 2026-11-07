# Solver configurations

Each file here is a solver entry point, selected with `-c` and run from the repository root (nested
configuration files are named relative to it). How a name reads:

- **No suffix** (`muval.json`, `muval_ppm.json`, `mustrat.json`, `pcsat.json`): the engine at CoAR's
  defaults. The file states only what differs from the code's defaults and follows them as they move.
- **The default** (no `-c`): `portfolio_muval_ppm_mustrat_muval_ppm.json` (`muval_ppm` for 10 s, then `mustrat`
  for 60 s, then `muval_ppm`) for `muclp` and `pltsterm` (the classes it was measured on), `muval.json` for the others (`main.ml`'s `default_config_file`).
- **`_popl27`** (`muval_ppm_popl27.json`, `muval_popl27.json`, `mustrat_popl27.json`): pinned for the
  POPL 2027 paper's runs. The file writes the paper's method explicitly (for `muval_ppm_popl27`,
  SCC-wise parity relations and alternation-depth priorities) and pins off any step that could decide
  an answer without that method, such as the ground-query solve before the reduction. Internal search
  defaults (how templates grow, the PCSat chain) still follow the code.
- **`ablation/<base>_no_<feature>`**: an ablation arm, the base with an optimisation removed. Ablation
  arms follow the defaults and are never A/B'd; `ablation/README.md` lists each with its base.
- **Any other feature suffix**: a pinned feature set, or a component chain (`_tb_ar`, `_fixpoint`,
  ...), or an experiment arm of a past measurement. A name does not spell a default: `tbq_ar` is
  PCSat's default chain, so `pcsat_<feature>` is the default with that feature (`pcsat_nocell_mod2`),
  and `pcsat_tbq_*` without `_ar` is the non-default scalar-template chain. `_yesno` is MuVal's
  yes/no output with no iteration count (`muval_yesno`). MuVal's and MuStrat's inner PCSat defaults are
  `pcsat_muval` and `pcsat_mustrat`.
- **`mucyc_qsat_<return>[_entry_model]`**: MuCyc's QSMT search with the backtracking named by the level a
  lemma returns to (`backtrack_strategy`: `chronological`, `deepest_own`, `deepest_own_projected`,
  `deepest_own_projected_repeatedly`, `deepest_any`) and, with `_entry_model`, resuming with the model
  that level was entered with (`frames.model_after_lemma = Entry_model`). Each states its return even
  when it is the default, since the CAV 2026 artifact compares two of them
  (`mucyc_qsat_deepest_own_projected_repeatedly` against `mucyc_qsat_deepest_own`).
- **Pinned competition configurations** (the Athena configurations the competition wrappers under
  `script/svcomp/` and `script/termcomp/` write, and the `config/llvmfront/*.json` files they name)
  state every field of the integer reading, defaults included, so that a change of CoAR's defaults
  reaches no competition run; like the `_popl27` files they are an exception to "a file states only
  what differs" (DECISIONS.md, 2026-11-03).
- **`portfolio_<engine>_<engine>...`**: a sequential portfolio (`["Portfolio", {"stages": [...]}]`): the
  named entry configurations run one after another, each in a forked copy with its own `time_limit_s`
  (none: to the end of the run), and the first definite answer (`valid`, `invalid`, `sat`, `unsat`,
  `YES`, `NO`) is printed. `portfolio_muval_ppm_mustrat_muval_ppm` (the default
  since 2026-11-06) runs `muval_ppm` for 10 s, then `mustrat` for 60 s, then `muval_ppm`;
  `portfolio_mustrat_muval_ppm` (the default from 2026-11-05 to 2026-11-06, kept for the record) runs `mustrat`
  for 60 s, then `muval_ppm`. Neither is a paper row.
- **`dbg_` prefix**: the traced copy of the file without the prefix (tracing and the self-checks on,
  nothing else changed).
