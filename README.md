# This Repository (fixed version)

This folder is the development of the sibling folder `temporal-planning-certification/` (the version
used for the paper's evaluation) with one correction made after the evaluation, described below.
Everything else is the same: see that folder's `README.md` for what the development contains, what
is verified and what is trusted, how to check the proofs and export the code, build the certifier
and run it, and the third-party components and licences. All its instructions apply to this folder
unchanged, run from here instead; like that folder, this one includes the exported code and the
certifier built from it. The artifact's top-level `README.md` ("Two versions of the
formalisation") says how the two folders are built side by side.

## What changed

**The numeric interference guards.** The reduction used for the paper's evaluation added clock
guards to the action automata's edges only for snap actions that interfere propositionally; snap
actions that interfere only numerically (one writes a fluent the other reads or writes, conditions
(v)–(vii) of the paper's Definition 13) got no guard, unlike Definition 20 of the paper. This
version guards both, in the formal model and in the executable certifier: an action's start, end
and instant edges check the clocks of every snap action that interferes with it propositionally or
numerically. The paragraph "One weakness: …" of the other folder's README ("What is verified and
what is trusted") therefore no longer applies. The old guards were a sound under-approximation
(fewer guards only admit more runs, so an unreachable goal still means no valid plan exists), so no
result of the paper is invalidated; they could only leave some unsolvable instances uncertified.
The paper's evaluation results in `benchmarks/` were produced with the old binary; a rerun of
all 410 `ours` runs with this folder's binary (`benchmarks/results/results-ours-fixed.csv`, raw
output in `benchmarks/results/benchexec/ours-fixed/`) certifies the same 75 instances, with no
other change of outcome.

- Formal model: the interference relation is a parameter `mutex_effects` of the reduction
  (`tp_nta_reduction_defs`, `TA_Network/TP_NTA_Reduction_Defs.thy`); the propositional reduction
  instantiates it with `mutex_snap_action`, the numeric one with propositional-or-numeric
  interference (`numeric_tp_nta_reduction_defs'`, `Numeric_TA_Network/`). A valid plan separates
  interfering snap actions by `ε` (`eps_separated_happ_seq`, `TA_Network/NTA_Temp_Planning_Sem.thy`;
  numeric part `num_mutex_eps_separated`), which discharges the new assumption `mutex_effects_sep`
  of the correctness proof. `Index.thy`, Definitions 18 and 20, maps the changes to the paper.
- Executable certifier: `mutex_effects'`, `num_net_int_clocks'`, `start_edge_num'`, `edge_3_num'`
  and `instant_trans_edge_num'` (`Numeric_Ground_PDDL_Exec_Imp/`). `ML/Check_Unsolvability.ML` is
  re-exported from this version (+155/−3 lines against the other folder's; sha256
  `18db4c263533cba009e58953c0c9abb9ba19bb20b06bb363b2eb523489f6ff11`).
- Binary: `ML/out/plan_cert` is the certifier built from this version (sha256
  `f5367170292fb62c33111255473171e8b78ddb30d9878abfa8674a4b29da04de`; Isabelle2025-2 with the AFP
  release afp-2026-10-06, MLton 20241230, GCC 16.2.1). It is not the paper's binary (the other
  folder's `ML/out/plan_cert` = `benchmarks/tools/plan_cert`, sha256 `611b70924b60…`);
  `make -C ML build_certifier` reproduces it.
  Networks for problems without numeric interference are identical; for the others the new guards
  add clock constraints to the edges.
- Documentation: the export command is `isabelle build -d . -e Numeric_Ground_PDDL_Exec_Imp` (the
  other folder's README names `PDDL_TP_Reduction`, which does not export the numeric certifier).

The provenance tags (`provenance` commands, see the artifact's `PROVENANCE.md`) cover the changed
lines too: the fix was implemented by AI agents, so its lines are tagged `ai` and `ai_human`.
