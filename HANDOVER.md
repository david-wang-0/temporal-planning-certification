# HANDOVER — temporal-planning-certification

Living inventory + handover for this repository: per-session contents, the `sorry` inventory,
environment/gotchas, and the ordered next-steps list. Design docs:
[ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md),
[ARCHITECTURE_grounding.md](ARCHITECTURE_grounding.md); plans:
[GROUNDING_PLAN.md](GROUNDING_PLAN.md), [NUMERIC_PLAN.md](NUMERIC_PLAN.md). The ROOT files are
authoritative. Last updated 2026-06-19.

## Session handover — 2026-06-19

Two threads this session; both landed as repo docs / build config — **no proofs changed, and the build
was not re-verified** (per `CLAUDE.md`, no batch build).

1. **Numeric refactor fully specified in [NUMERIC_PLAN.md](NUMERIC_PLAN.md) (§A–§D, §C, §7).** Decisions:
   the abstract `Temporal_Plans` layer stays opaque — a *fresh* `('n,'r) nexp` / `('n,'r) comp` plus snap
   fields `upds` / `n_pre` / `n_inv` (sets read conjunctively); PDDL `numeric_expression` maps in at the
   `Ground_PDDL` boundary. Munta `exp.binop` / `bexp` express every operator and comparison — the limiter
   is bounded `int` vs `rat`, not the operators. Static variable bounds = untrusted interval-compute +
   verified `wf_bounds` check (cases a/b/c, incl. object/static-fluent caps) + one Layer-A invariant; a
   **time-rescaling** stage (§D) handles non-integer durations. Coverage checked against the real Gigante
   artifact (`~/Downloads/AAAI2022/expeval/benchmarks/`; survey copied to
   [gigante_benchmarks_conditions_effects.md](gigante_benchmarks_conditions_effects.md)).

2. **`ROOT`/`ROOTS` restructured into a 4-layer chain + assistant config added.** The abstract layer is
   now three sessions: externals-only **heap** `Temporal_Planning_Base` (Munta cert checker + List-Index +
   temporal semantics) ← utility `Temporal_Planning_Common` (`Utils`, `ListMisc`, `Sequences`) ←
   `Temporal_Planning_Semantics` (`Temporal_Plans` + `Temporal_Plans_{Instances,Lemmas,Code}` via closure)
   ← `TP_NTA_Reduction` ← … . New `ROOTS` registers `lib/temporal-pddl-semantics`. Added **gitignored**
   `CLAUDE.md` (project Isabelle rules + "flag cleanup opportunities" standing preference) and
   `CLAUDE.local.md` (`@~/.claude/isabelle.md`). Deleted 25 stale `*.thy~` backups.

**Heap builds green (2026-06-19):** `Temporal_Planning_Base` builds clean (use `isabelle build -b -d .
Temporal_Planning_Base` so the image **persists** for `-l` loading — a plain build without `-b` does not
save it; jEdit otherwise rebuilds a transient image at startup) —
confirming the previously-unverified point that parenting on `Munta_Certificate_Checker` resolves the
abstract layer's old `Munta_Model_Checker` imports. Two restructures landed this session: (i) fixed a ROOT
bug (the externals-only session had no `in` clause, colliding on dir `.` with `PDDL_TP_Reduction_Index`);
(ii) the old single `Temporal_Planning_Abstract` session was **split** (via the `isabelle-refactor` skill)
into `Temporal_Planning_Common` (utility) + `Temporal_Planning_Semantics`, with files renamed
content-aware (`Base.thy`→`Utils.thy`, `Temporal_Plans_Theory.thy`→`Temporal_Plans_Lemmas.thy`) and the
externals heap renamed `Temporal_Planning_Common`→`Temporal_Planning_Base`.

**P2 Layer-A progress (branch `numeric-conditions-effects`, all PIDE-verified green in
`Temporal_Plans.thy`, 2612 cmds / 0 errors):**
- §A.1 numeric syntax: `('n,'r) nexp` (NConst/NVar/NAdd/NSub/NMul/NDiv), `cmp_op`, `('n,'r) comp`
  (the `comp` type does **not** clash with `Fun.comp` — separate namespaces).
- §A.2 numeric semantics (additive, standalone): `nexp_fluents`, `eval_nexp` (partial,
  `'r::linordered_field`, fail-closed on undefined read / div-by-zero), `cmp_op_rel`,
  `sat_comp`/`sat_comps` (+ I/D/E rules), and numeric effects `upds_functional` / `upds_no_self_read` /
  `upds_wf` (+ I/D rules) and `apply_upds` (pre-state reads, `THE` over a functional lhs) with
  `apply_upds_in`/`apply_upds_notin`.
- §A.2 state + locale: `type_synonym ('p,'n,'r) num_state = "'p set × ('n ⇀ 'r)"` (props =
  `fst`, kept as a projection); and **`locale numeric_action_defs = action_defs (+ for-clause) + fixes
  n_pre n_inv upds`** — an **additive** sublocale (the existing `action_defs` hierarchy is untouched, so
  everything stays green). Inside it: `n_pre_imp`/`upds_imp` (snap→annotated lift via `app_snap`, +
  simps), `snap_upds_wf`, `num_pre_holds`/`num_inv_holds` (+ I/D), `apply_num_eff` (+ simps). **Gotcha
  recorded:** a sublocale that adds `fixes` over the base's type vars must use the explicit
  `action_defs at_start … dels for …` parameter form, *not* the bare `action_defs +` form — the bare
  form fails to share `'snap_action`/`'action` and `app_snap` won't unify.
- §A.2 numeric interference + happening update (in `numeric_action_defs`): `comp_fluents`;
  `snap_writes`/`snap_reads`; **`num_mutex_snap_action`** (write/write + read/write, + refl, the numeric
  analog of `mutex_snap_action` — feeds the ε-separation, *not* an update-level guard); `snap_num_update`
  (one snap's effect on the valuation) and **`happening_num_update = fold snap_num_update`** — the happening
  numeric update as a **sequential fold** (+ Nil/Cons lemmas). **This replaced the earlier set-union
  `apply_num_effs`/`union_upds_functional`/`apply_num_effs_in` (deleted).**
  **AUTHORITATIVE RULE + corrections (checked against Formal-PDDL-Semantics 2026-06-19):**
  - **Within-snap** (your "no two conflicting assignments"): PDDL's `numeric_effects_non_intrf`
    (`Numeric_Update_Functions.thy:44`) — same-fluent effects must be **same type ∧ neither `Assign`**;
    two `Assign`s conflict, additive/scaling **accumulate**. PDDL collapses each snap to **one assignment
    per fluent** (`action_numeric_update_function_simplified`) = exactly the abstract `(f, nexp)`, so
    `upds_functional` holds by construction via the **combination normalization stage** (sibling to §D,
    reuse `combine_additive`/`combine_scaling`).
  - **Happening = sequential fold, not set-union.** PDDL `action_list_numeric_update_function =
    fold (∘) (map action_numeric_update_function A) id` (each reads the running state); Munta interleaved
    edges do the same. So **co-occurring additive writes accumulate** (`f+ea` then `+eb`) — **the earlier
    "fail-closed reject additive co-writes" caveat was WRONG** (an artifact of the set-union dedup). The
    obligation is order-independence of the fold under non-interference (PDDL
    `same_actions_then_happening_numeric_update_function_equal`).
  - **Non-interference is enforced by clocks** (ε-separation): mutex pairs forced ≥ε apart never co-occur,
    so happenings contain only commuting snaps.
  - **Munta cross-reads = Layer-B obligation, mostly a theorem.** Munta `is_upds`/`mk_upds` is a sequential
    `fold` (RHS read from running store) — confirmed in `Simple_Expressions.thy:82-87` /
    `…_Impl_Refine.thy:67-71`. So a cross-read (RHS reads a *different* update's LHS) is order-sensitive
    (own-LHS read is fine — `(f, f+e)`). Between distinct co-occurring actions this **can't** happen:
    `acts_non_intrf` gives `lvalues∩rvalues=∅` (FL03) ⇒ **no-cross-read is a theorem from PDDL
    non-interference**. Only residual: *within one snap* a combined `(f, …g…)` reading another written
    fluent `g` — topological emit, reject only cycles. The Layer-B no-self-read condition must exclude the
    own LHS: `nexp_fluents e ∩ (writes − {f}) = {}` (NOT `∩ writes`, which wrongly rejects `(counter,
    counter+1)`). `upds_no_self_read` as I first defined it is the wrong `∩ writes` form — fix when
    re-homing to Layer B. Gigante safe (RHS constants / static fluents).

- §A.2 order-independence (in `numeric_action_defs`, **PIDE-verified, complete**): `eval_nexp_cong` (eval
  depends only on read fluents); `snap_num_update_writes`/`_unwritten`/`snap_write_witness`;
  **`snap_num_update_commute`** (two non-interfering snaps' updates commute — the load-bearing lemma, full
  Isar case split); `happening_num_update_swap` (adjacent swap, list version). **Order-independence done via
  `Finite_Set.fold`:** `comp_fun_commute_on_snap_num_update` (functional + pairwise-non-interfering ⇒
  `comp_fun_commute_on S snap_num_update`); **`happening_num_update_set S v = Finite_Set.fold snap_num_update
  v S`** — the set-level happening numeric update, **order-independent by construction**; with computational
  laws `happening_num_update_set_empty` and `happening_num_update_set_insert` (insert recursion under the
  non-interference precondition). This is the abstract analog of PDDL's
  `same_actions_then_happening_numeric_update_function_equal`. Use `happening_num_update_set` (over the SET
  `happ_at`) in the numeric `valid_state_sequence`.

- §A.2 numeric plan locale + migration lemma (**PIDE-verified, complete**): in
  `numeric_action_defs`, helper facts `snap_writes_empty` / `snap_num_update_empty` (empty effects ⇒
  identity — needed because locale defs don't unfold by name in the merged locale). New locale
  **`numeric_temp_plan_defs = temp_plan_defs + numeric_action_defs`** (the merge, sharing `action_defs`
  params — the parallel hierarchy), with `active_actions` (over_all-active actions at a time) and
  **`num_valid_state_sequence`** over `num_state` (props via existing `apply_effects`/`invs_at`/`pre`,
  numerics via `happening_num_update_set` + `sat_comps` of `n_pre`/`n_inv`). `happening_num_update_set_id`
  (empty effects ⇒ identity happening update, finite-induction). **`num_valid_state_sequence_empty`
  = the MIGRATION LEMMA** (✅ **GO**): with `n_pre=n_inv=upds=∅` and finite happenings,
  `num_valid_state_sequence M ⟷ valid_state_sequence (fst∘M) ∧ (snd constant)`. So the numeric semantics
  is a **conservative generalization** of the propositional one — **collapse-by-promotion is viable**;
  no need to switch to fold-in.

- §A.2 numeric mutex + migration (**PIDE-verified**): `num_mutex_snap_action_empty` (empty effects ⇒
  no numeric interference, in `numeric_action_defs`); **`num_mutex_valid_plan`** (in
  `numeric_temp_plan_defs`) = `mutex_valid_plan ∧` the same ε-separation discipline for
  `num_mutex_snap_action` (incl. the `at_start a`/`at_end a` self-pair for `d=0`/`d<ε`); migration
  **`num_mutex_valid_plan_empty`** (✅ `upds=∅ ⟹ num_mutex_valid_plan ⟷ mutex_valid_plan`).

- Proof-hygiene cleanup (propositional `plan_validity_equivalence`, **PIDE-verified**): refactored
  `inj_mutex_def` — extracted the `ran`↔`dom` pair-transfer logic into named Isar lemmas
  `ran_pair_imp_dom_pair` / `dom_pair_imp_ran_pair` (using `inj_on_contraD`), added intro/elim/dest
  rules for the two bundles (`mutex_valid_plan_{alt,inj}{I,D1,D2,E}`), and re-proved `inj_mutex_def` via
  those rules in structured Isar. **Fixed a stuck `blast`** (the old one-shot `blast` on the iff of two
  8-variable conjunctions diverged; per-subgoal `rule` terminates instantly). Pattern for the rest of
  next-step 5: extract transfer/bundle lemmas, prove with `rule`/dest rules, avoid monster `blast`.

- §A.2 numeric `valid_plan` + migration (**PIDE-verified — the migration story is COMPLETE**):
  `numeric_temp_plan_defs` gained two fixes `num_init :: "'n ⇀ 'r"` / `num_goal :: "('n,'r) comp set"`;
  **`num_valid_plan`** mirrors `valid_plan` (numeric init `snd(M 0)=num_init`, numeric goal
  `sat_comps (snd(M len)) num_goal`, `num_mutex_valid_plan`). **`num_valid_plan_empty`** (✅): with
  `upds=n_pre=n_inv=∅`, `num_goal=∅`, and finite happenings, `num_valid_plan ⟷ valid_plan` — forward via
  the two component migrations, backward by the constant-valuation witness `M i = (M' i, num_init)`. So
  **all three levels** (state sequence / mutex / plan) migrate cleanly: the numeric semantics is a
  conservative generalization of the propositional one at every level.

**Layer-A is DONE** (all in `Temporal_Plans.thy`, green): numeric `valid_plan` (`num_valid_plan`,
with the two locale fixes `num_init :: "'n ⇀ 'r"` and `num_goal :: "('n,'r) comp set"`) and the
plan-level migration `num_valid_plan_empty` (`upds=n_pre=n_inv=∅ ∧ num_goal=∅ ⟹ num_valid_plan ⟷
valid_plan`). All three migration levels (state-sequence / mutex / plan) are proven — the numeric
semantics is a conservative generalization of the propositional one at every level.

**The collapse — COMPLETE end-to-end (2026-06-19), green through the 456 KB capstone.** An
empty-numeric problem now certifies via the *unchanged* propositional reduction:
`numeric_valid_temp_plan_imp_form_holds` (`TP_NTA_Reduction_Correctness.thy:8773`, verified in jEdit:
7420 cmds, 0 err) proves `(∃π. numeric_temp_plan_for_problem_list_impl_int' … π) ⟹ net.sem,a₀ ⊨
formula_spec` — i.e. plan-existence at the numeric twin discharges the existing capstone
`valid_temp_plan_imp_form_holds`. The pieces (all in `Temporal_Plans_Instances.thy`, 352 cmds, 0
err/0 warn, **no `sorry`**):

- `numeric_temp_plan_for_problem_list_defs` (set/rat) + `collapse_num_valid_plan` — empty numerics ⟹
  `num_valid_plan ⟷ valid_plan` (from `num_valid_plan_empty`).
- `numeric_temp_plan_for_problem_list_impl_int` and `…_impl_int'` (int/list — the layers the capstone
  `tp_nta_reduction_correctness`/`'` sit on) + a `num_rat_impl: numeric_temp_plan_for_problem_list_defs`
  sublocale threading numerics through the int→rat refinement (numeric data passed through unchanged —
  the refinement touches *time*, not the field `'r`). So `num_rat_impl.collapse_num_valid_plan` is
  available where the capstone's `valid_plan` lives.
- `numeric_temp_plan_for_problem_list_impl_int'_imp_prop` — the numeric-twin locale **predicate equals
  its propositional parent's** (the numeric fixes carry no `assumes`, so they are not part of the
  predicate; its arity stops at `π`), proven `by simp`. This is the bridge the capstone lemma uses.

**Key structural fact for Layer-B:** because the numeric fixes carry no `assumes`, the numeric locale
predicate *coincides* with the propositional one — the empty-numeric collapse is essentially free at
the predicate level; the real numeric content lives in the `num_rat_impl` sublocale's defs
(`num_valid_plan`, `collapse_num_valid_plan`). Real numerics (non-empty) will instead need the
reduction to actually *consume* `n_pre/upds` (Layer-B), where the predicate stops being trivial.

**Superseded plan — historical (the two twins + composition, now all done):**
- `numeric_temp_plan_for_problem_list_defs` = `temp_plan_for_problem_list_defs` (the set/rat
  plan-for-problem locale whose `set ∘ pre` sublocale IS the abstract `temp_plan_defs` the reduction's
  `valid_plan` lives in, via `rat_impl`) merged additively with `numeric_temp_plan_defs` + `fixes
  n_pre n_inv upds num_init num_goal`. Its lemma `collapse_num_valid_plan` proves `num_valid_plan ⟷
  valid_plan` (empty numerics) straight from `num_valid_plan_empty` — that it closes confirms the
  merge shares the `temp_plan_defs` base (else the conclusion's `valid_plan` would be a different
  constant).
- `numeric_temp_plan_for_problem_list_impl_int` = `temp_plan_for_problem_list_impl_int` (the int/list
  executable layer the capstone `tp_nta_reduction_correctness` is stated on) + the numeric fixes,
  with a `num_rat_impl: numeric_temp_plan_for_problem_list_defs` sublocale threading the numerics
  through the int→rat refinement (numeric data passed through unchanged — the refinement touches
  *time* only, not the field `'r`). So `num_rat_impl.collapse_num_valid_plan` gives
  `num_rat_impl.num_valid_plan ⟷ num_rat_impl.valid_plan`, and `num_rat_impl.valid_plan` **is**
  `rat_impl.valid_plan` (the capstone's `valid_plan`).

The collapse composition (numeric twins → capstone) is **done** (above); nothing left there.

**Do next — Layer-B proper** (the only remaining numeric work; needs P0 first for real numeric
*syntax*): numeric guards/updates in `TP_NTA_Reduction_Spec` (extend `all_vars_spec` with a bounded
int var per numeric fluent; `at_start`/`at_end` numeric conditions → `bexp` guards on the
start/end edges; `over_all` numeric → guard on the running location's transitions; numeric effects →
`(var,exp)` updates appended after the propositional ones), then extend the
`TP_NTA_Reduction_Correctness` bisimulation to relate the numeric valuation to the Munta var store.
Munta no-cross-read is a theorem from `acts_non_intrf`. Keep additive, stage behind `sorry`s, don't
re-encode props as 0/1 (§8). NB: with non-empty numerics the numeric locale predicate stops
coinciding with the propositional one (the reduction must actually consume `n_pre`/`upds`), so the
free empty-numeric collapse no longer applies — this is genuinely new proof, not twinning.

Restructure verification debt: `Temporal_Plans_Instances` and `TP_NTA_Reduction_Correctness` now
**PIDE-verified green** (✓, the latter 7420 cmds / 47 pre-existing warns / 0 err). Still unverified:
`Sequences`/`_Code` and the remaining `TA_Network` qualified imports (mechanically consistent).
Standing preference: flag cleanup opportunities as you go (`CLAUDE.md`).

## What this repo is

The published artifact for *"Formally Verified Certification of Unsolvability of Temporal Planning
Problems."* It reduces a **ground** temporal PDDL problem to a Munta timed-automata network and, from
an (untrusted) TChecker reachability certificate re-checked by the verified `muntac`, concludes the
problem is **unsolvable**. Two workstreams are now in flight (planned, not yet built): a verified
**datalog grounding** front-end (so lifted problems are accepted) and **numeric** conditions/effects.

## Sessions (per `ROOT`)

| Session | Dir | Parent(s) | Contents | Status |
| --- | --- | --- | --- | --- |
| `Temporal_Planning_Base` | `Temporal_Planning_Base/` (no local theories) | `Munta_Certificate_Checker` + `List-Index` + `Temporal_AI_Planning_Languages_Semantics` | **externals-only heap** (Munta + cert checker + List-Index + temporal PDDL semantics); build once, load in jEdit as the stable dev heap. P0 swaps the semantics import here | green |
| `Temporal_Planning_Common` | `Temporal_Planning_Common/` | `Temporal_Planning_Base` | `Utils`, `ListMisc`, `Sequences` — generic utility theories (lists, options, `is_integer` rationals, sorted lemmas, sequences) | green |
| `Temporal_Planning_Semantics` | `Temporal_Planning_Semantics/` | `Temporal_Planning_Common` | `Temporal_Plans`, `Temporal_Plans_{Instances,Lemmas,Code}` (latter three via closure) — abstract snap/happening semantics; `temp_planning_problem`, `temp_plan_defs` | green |
| `TP_NTA_Reduction` | `TA_Network/` | `Temporal_Planning_Semantics` | `NTA_Temp_Planning_Sem`, `TP_NTA_Reduction_{Spec,Model_Checking,Correctness}` (`tp_nta_reduction_correctness`, Thm 1 `valid_plan_imp_form_holds`) | green |
| `PDDL_TP_Reduction` | `Ground_PDDL_Exec_Imp/` | `TP_NTA_Reduction` | `Ground_PDDL_{Problem,Plan}_{Defs,Reduction}`, `Ground_PDDL_Problem_Code`, `Ground_PDDL_NTA_Reduction_{Correctness,Impl}`, `Check_Unsolvability`, `Unsolvability_Code_Compile`; exports `ML/Check_Unsolvability.ML` | green; numeric-free, positive-precondition |
| `PDDL_TP_Reduction_Index` | `.` | `PDDL_TP_Reduction` | `Index` (paper theorem/locale map) | green |

The five working sessions all sit on the `Temporal_Planning_Base` heap (transitively), so the heavy
Munta + semantics images are built once and reused. `ROOTS` registers the in-repo
`lib/temporal-pddl-semantics` so `isabelle build -d .` / `jedit -d .` discover the old semantics
without a separate `-d`.

Capstones: `Check_Unsolvability.check_and_cert_pddl_problem_okay`
(`Result Sat ⟹ ∄ tp. valid_ground_plan problem tp`), `make_certified_net_okay`, and Thm 1
`tp_nta_reduction_correctness.valid_plan_imp_form_holds`. The compiled certifier (`ML/`, `muntac`,
`tck-reach`) plans the `examples/ground/MatchCellar-impossible/*` instances; `run.sh` drives the
whole pipeline.

## `sorry` inventory

- **`Temporal_Planning_Semantics/Temporal_Plans_Instances.thy` — 1 `sorry`.** Flagged by the author as
  **not a real `sorry`** (do not prioritize). Note it *is* in the build: `TP_NTA_Reduction` imports
  `Temporal_Planning_Semantics.Temporal_Plans_Instances` (and `…_Lemmas`/`…_Code`), which pull these in
  via closure even though they are not listed in the `Temporal_Planning_Semantics` session `theories`.
- No other `sorry` in `Ground_PDDL_Exec_Imp/` or `TA_Network/`. (The stale `*.thy~` editor backups have
  been deleted.)

## Environment / gotchas

- **Isabelle 2025-2** (not 2025). `isabelle` on PATH is `~/bin/Isabelle2025-2/bin/isabelle`; user
  components in `~/.isabelle/Isabelle2025-2/etc/components`.
- **Dependencies are now standalone repos** under `~/work/` (de-submoduled from
  `verified-classical-sat-based-pddl-planner`, which is being dismantled): `~/work/Formal-PDDL-Semantics`
  (the new PDDL semantics; sessions `Classical_Planning`/`Continuous_Planning`/`Temporal_Planning`/…)
  and `~/work/Isabelle-PDDL-Grounding` (the classical grounder). Both are registered as Isabelle
  components; the old submodule paths are commented out as `(retired)`.
- This repo still carries its own submodules: `lib/temporal-pddl-semantics` (the **old**
  `Temporal_AI_Planning_Languages_Semantics`, to be retired by P0), `ML/lib/{mlunta,cmlib,parcom}`,
  `examples/pddl-instances`.
- Verify with the **`jedit-status`** skill against a running jEdit, not a batch build. Build the
  `Temporal_Planning_Base` heap once (the externals heap — Munta + cert checker + List-Index +
  temporal PDDL semantics) and launch `isabelle jedit -d . -l Temporal_Planning_Base` to avoid the
  long Munta/semantics startup.
- Write Isabelle symbols as ASCII escapes (`\<Rightarrow>`, `\<open>`); never raw Unicode.

## Ordered next steps

1. **P0 — re-point onto the new semantics** (shared prerequisite of both plans). Move
   `Ground_PDDL_Exec_Imp/*` and `TA_Network/*` off `Temporal_AI_Planning_Languages_Semantics` onto
   Formal-PDDL-Semantics `Temporal_Planning`; update `ROOT`; re-establish `check_ground_problem` and
   the codegen. Do it on its own branch, fully green, before anything else. (Triage the
   `Temporal_Plans_Instances` `sorry` while here.)
2. **Numeric Layers A → C** ([NUMERIC_PLAN.md](NUMERIC_PLAN.md)): extend the abstract state + snap
   numerics, then the ground-task shape (the grounder's output contract), then the NTA reduction +
   the big `TP_NTA_Reduction_Correctness` bisimulation. Run the §5 verification spikes first.
3. **Grounding front-end** ([GROUNDING_PLAN.md](GROUNDING_PLAN.md)): new `Ground_Temporal_PDDL/*`
   session — projection `π_C`, over-approximation lemma, re-expansion `χ`, plan-preservation, code
   export. Flip the grounder's numeric-free check to "ground numerics through" once Layer C lands.
4. Update this file's `sorry` inventory + status table as each lands; keep
   [ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md)'s stage table in sync.
5. **Proof hygiene — shorten the long apply-style proofs** (ongoing). `apply`-line counts:
   `TA_Network/TP_NTA_Reduction_Correctness.thy` **1609 / 8765** (~18%, the priority),
   `Ground_PDDL_Exec_Imp/Ground_PDDL_Plan_Defs.thy` 163, `…/Check_Unsolvability.thy` 123,
   `…/Ground_PDDL_NTA_Reduction_Impl.thy` 87, `Temporal_Planning_Semantics/Temporal_Plans.thy` 73. Replace
   long `apply` chains with structured Isar (`have … if … for …`, hoist subgoals into named lemmas)
   and minimise terminal methods with the **`try0-minimize`** skill (`isabelle-stuck-method` for any
   diverging step). `TP_NTA_Reduction_Correctness` is *also* the file the numeric Layer B extends, so
   do this opportunistically while touching it (a brittle apply-chain that breaks under the numeric
   state-relation change is best converted to Isar first), with a dedicated cleanup pass after P0.

## Documentation conventions

Mirror `~/work/Isabelle-PDDL-Grounding`: `ARCHITECTURE_pipeline`-style one-pager (ASCII pipeline +
stage table + trust story), `ARCHITECTURE_*`-style design notes for non-obvious layers, this
HANDOVER as the living inventory, and the per-stage three-file pattern (`X_Locales` / `X` /
`X_Semantics`) with `text \<open>…\<close>` headers and reuse callouts. See
[GROUNDING_PLAN.md §9](GROUNDING_PLAN.md).
