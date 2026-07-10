# Numeric executable plan — exporting a certified *numeric*-net unsolvability checker

Status: draft (2026-07-06). Companion to [NUMERIC_PLAN.md](NUMERIC_PLAN.md) (this is its executable
sequel — NUMERIC_PLAN half A/B built the *abstract* numeric net and proved it correct; this plan makes
that net *executable* and Munta-checkable). Design docs: [ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md),
[ARCHITECTURE_dependencies.md](ARCHITECTURE_dependencies.md). Line anchors are current as of the
2026-07-05 reorg; re-anchor if files move.

---

## 0. Where we are (the starting line)

- **Abstract numeric-net certificate — DONE, committed.**
  `num_valid_plan_imp_form_holds : num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula`
  (`TA_Network/TP_NTA_Reduction_Correctness_Numeric.thy:2784`) is proved **hypothesis-free** inside the
  locale `numeric_tp_nta_reduction_correctness` (from its sole plan assumption `num_valid`). Rungs 0/1
  of NUMERIC_PLAN §3b are closed; `num_net_impl` certifies the location-only `reach_formula`.
- **Ground_PDDL numeric lemmas exist — but over the PROPOSITIONAL net.**
  `num_valid_ground_plan_imp_form_holds` / `num_form_not_sat_imp_no_valid_ground_plan`
  (`Ground_PDDL_Exec_Imp/Ground_PDDL_NTA_Reduction_Correctness.thy:37,44`) certify over
  `abstr_model_checking.ref_model_checking.net_impl` — the **propositional** net — via the
  additive-tracking shortcut `numeric_valid_temp_plan_imp_form_holds`
  (`TA_Network/TP_NTA_Reduction_Correctness.thy:664`). They do **not** touch `num_net_impl`.
- **No executable numeric machinery at all.** There is no `num_make_network_impl`, no numeric
  `check_ground_problem`, no numeric `export_code`. The only live export
  (`Ground_PDDL_Exec_Imp/Check_Unsolvability.thy:1235`) is the **propositional** pipeline.

## 1. Why bother — the numeric net vs. the additive-tracking shortcut

The committed additive-tracking capstone certifies over the **propositional relaxation** of the
problem: it is *sound* but a *weak* certifier. A `Sat` (goal-unreachable) result on the propositional
net proves no numeric plan exists — but only for instances whose *propositional relaxation is itself
unreachable*. Exactly the interesting numeric instances — **numerically unsolvable but
propositionally reachable** (a resource/counter argument makes them unsolvable, dropping the numerics
makes the goal reachable) — get **no certificate** from it.

To certify those, you must export and check the **numeric** net `num_net_impl` (bounded-`int` fluent
variables, numeric guards/updates on the action edges). Its soundness is exactly
`num_valid_plan_imp_form_holds`. This plan turns that abstract theorem into a running, Munta-checked,
certificate-backed executable — the numeric twin of the propositional
`check_and_cert_pddl_problem_no_return`.

## 2. The propositional template to mirror (with anchors)

The propositional pipeline is the exact skeleton the numeric one copies. Ordered chain:

| # | constant | file:line | role |
|---|----------|-----------|------|
| 1 | `check_ground_problem` | `Ground_PDDL_NTA_Reduction_Impl.thy:595` | static admission check → `ground_ast_problem` context |
| 1 | locale `ground_ast_problem` | `Ground_PDDL_Problem_Defs.thy:785` | bundles the static side-conditions the abstract locale needs |
| 2 | `make_network_impl` | `Ground_PDDL_NTA_Reduction_Impl.thy:1427` | build concrete NTA: `net_automata'`/`net_bounds'`/`init_cfg'`/`reach_formula'` |
| 3 | `sublocale abstr_model_checking: tp_nta_reduction_model_checking'` | `Ground_PDDL_Problem_Reduction.thy:8` | interpret the abstract reduction at the ground problem |
| 3 | `*_refine` + `make_network_impl_return_iff` | `Ground_PDDL_NTA_Reduction_Impl.thy:1447` | executable net = abstract `net_impl` |
| 3 | `model_checking_problem_refine` | `Ground_PDDL_NTA_Reduction_Impl.thy:1400` | executable unreachable \<Longrightarrow> no valid plan |
| 4 | `form_not_sat_imp_no_valid_ground_plan` | `Ground_PDDL_NTA_Reduction_Correctness.thy:30` | Ground_PDDL soundness capstone |
| 5 | `make_certified_net` / `make_certified_net_okay` | `Check_Unsolvability.thy:1042,1054` | wrap the Munta certificate checker |
| 5 | `check_and_cert_pddl_problem[_no_return]` | `Check_Unsolvability.thy:1103,1193` | top-level entry point |
| 5 | `export_code` | `Check_Unsolvability.thy:1235` | code-gen to SML (`Eval`, module `Converter`) |

`reach_formula` is location-only (`formula.EX (sexp.loc 0 goal_loc)`) and is **reused verbatim** on
the numeric net. The Munta certificate checker (`Munta_Certificate_Checker`) is **fragment-agnostic**
— it checks *any* bounded-`int` timed-automata network — so it is reused **unchanged**; the numeric net
is just a bounded-`int` network with extra variables and guarded/updating edges.

## 3. The numeric build — ordered work packages

All new theories land in the existing session `PDDL_TP_Reduction` (`Ground_PDDL_Exec_Imp/`, on top of
`TP_NTA_Reduction`); register them in `ROOT` and re-`isabelle components -u .` before jEdit sees them.

### Locale architecture — the ladder (decided 2026-07-08, mirrors the grounder idiom)

The numeric admission locale is a **grounder-idiomatic ladder**, not a from-scratch sibling. A read of
the classical + temporal grounders (session `Grounding_Temporal_Common`) fixed the idiom: a
**numeric-inclusive well-formed base**, with each specialization an **orthogonal leaf adding one
bundled assumption** — `grounded_temporal_problem`, `positive_temporal_problem`, and the classical
branch's `numeric_free_problem = base + functions=[]`. So **numeric-freeness is a leaf, never baked
into the base.** Applied here:

```
ground_ast_problem_defs        -- DEFINES all data from P (props + numeric); fluent_lo/hi plug only
      |
ground_ast_problem_core        -- + wf_ast_temporal_problem + the 9 shared admission assumptions  (numeric-INCLUSIVE)
      |
   ___|________________________________________
   |                                            |
ground_ast_problem                  numeric_ground_ast_problem
  = core + no_functions               = core + numeric-fragment wf
  (classical leaf -- KEEPS its name,  (numeric leaf; fluent_lo/hi = WP-E plug)
   whole propositional pipeline
   below it is untouched)
```

**Status: Stages 1 & 2 DONE & green** — Stage 1 (`Ground_PDDL_Problem_Defs.thy`): `ground_ast_problem_core`
extracted; `ground_ast_problem` demoted to `core + no_functions`, name unchanged, so every downstream
`sublocale`/interpretation is intact. Stage 2 (`Ground_PDDL_Numeric_Problem_Defs.thy`, consolidated,
0 errors/sorries): the translation funs + `numeric_ground_ast_problem_defs` (data defined from P) + the
leaf `numeric_ground_ast_problem = numeric_ground_ast_problem_defs + ground_ast_problem_core + <numeric-fragment wf>`.
Remaining params: `fluent_to_var`/`const_to_int` (encoding maps) + `fluent_lo`/`fluent_hi` (WP-E plug).
Gotchas: qualify `numeric_effect_op.Assign` (clashes with `form.Assign` from Approximation); locale-local
consts need `@{text …}` not `@{const …}` in doc comments.

**Numeric data is DEFINED from P, not fixed as parameters** (the draft's 10 `fixes` were an explicit
stub). A `numeric_ground_ast_problem_defs` (mirror of `ground_ast_problem_defs`) defines
`nfluents`/`n_pre`/`n_inv`/`upds`/`num_init`/`num_goal` via a **FPS->project boundary translation** —
the numeric twin of `to_literals`/`to_predicate`:

- **Fluent identity `'n := func`** (the bare name-wrapper `Func name`), mirroring props'
  `'proposition := predicate` (`Pred name`) EXACTLY: `nfluents == map func (functions D)` vs
  `props_spec == map pred (predicates D)`; `fluent_of (PNE f _) = f` vs `to_predicate (Atom (predAtm x _)) = x`.
  The args-carrying `PNE`/`predAtm` are the *atom* level, not the identity level; grounded => args = [].
- **`num_comps` / `nexp_of_pddl` / `upd_of_ne`** (numeric twins of `to_literals`/`to_predicate`):
  `numericEqAtm->Ceq`, `numericLessAtm->Clt`, `numericLEAtm->Cle`, `numericGreaterAtm->Cgt`,
  `numericGEAtm->Cge`; `ConstantExpr->NConst`, `FunctionExpr->NVar`, `Add/Sub/Mul/Div` map across,
  transcendentals (`Sin/Cos/Exp/Pi`, `DurationExpr`) are outside the fragment (rejected by the
  `nexp_ok`/`comp_ok` admission checks); numeric-effect op folds into the RHS:
  `Increase f e -> (f, NAdd (NVar f) e)`, `Decrease->NSub`, `ScaleUp->NMul`, `ScaleDown->NDiv`, `Assign->e`.
  (Note: `to_literals` keeps ONLY `predAtm` literals, so `num_comps` is a separate fun keeping the 5
  numeric-atom kinds — same recursive shape over `\<^bold>\<and>`.)
- **No placeholder-lift needed:** the propositional snaps `at_start_spec`/`at_end_spec` are the *full*
  FPS snaps (`inst_snap_action_body_elements …`); `pre_spec`/`adds_spec` merely *project out* the
  numerics, so the snap still carries `numeric_effects` + numeric precondition atoms. `upds`/`n_pre`
  read them directly; on classical (`no_functions`) instances they are provably `[]` via the existing
  `wf_ground_action_numeric_effects_Nil` chain (`Ground_PDDL_Plan_Defs.thy`).
- Defining `const_to_int` (and, if the freshness proof lands, `fluent_to_var`) turns
  `const_to_int_of_int` (resp. `fluent_to_var_inj`/`fluent_vars_fresh`) from **assumptions into lemmas**.
- **Only plug left:** `fluent_lo`/`fluent_hi` (WP-E) — the reachability bounds, soundness-critical,
  not a structural accessor on `P`.

### WP-E (USER-OWNED design) — the boundedness plug  ⟵ *NEXT: now sequenced concretely, before WP-D*

**Status (2026-07-10): IN PROGRESS — backbone green, interval check drafted.** The soundness backbone is
proved: `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy` defines the plain-`int` certificate `num_bound_inv`
and the locale `numeric_tp_nta_reduction_bounds` (assumes `num_bound_inv` instead of `num_seq_in_bounds`),
and the **bridge `num_seq_in_bounds_derived` is GREEN**, so a `sublocale numeric_tp_nta_reduction_correctness`
re-derives everything from the certificate. The eval-decidable interval check `is_gbound_inv'` +
`is_gbound_inv' ⟹ num_bound_inv` is DRAFTED (3 sorries). Structure: `is_gbound_inv' ⟹ num_bound_inv ⟹
num_seq_in_bounds`. Two facts are now LOCKED and supersede parts of this section: **(i) HOL-IMP cannot be
imported into the reduction** (`option`-arity clash), so the interval check is inline `int` on the reduction
heap and the analysis stays a separate `Numeric_Bound_Inference = "HOL-IMP"` session (now in the main ROOT),
the box crossing as data; **(ii) `int` is forced** (Munta `Simple_Network_Impl`). Full current detail:
`../HANDOVER.md` (2026-07-10 status) + `Numeric_Bound_Inference/BOUND_INFERENCE_PLAN.md` §0'. The original
plug-interface framing below is retained for context. The abstract numeric locale assumes
`num_seq_in_bounds` (`TA_Network/TP_NTA_Reduction_Numeric_Model_Checking.thy:66`): along every valid
numeric state sequence, each fluent stays within `[fluent_lo f, fluent_hi f]`
(`TP_NTA_Reduction_Numeric_Defs.thy:39,40`). To *instantiate* the locale on a concrete problem this
must be **discharged**, and it is **soundness-critical**: bounds too tight \<Longrightarrow> the bounded-`int` net
cannot simulate a genuine plan \<Longrightarrow> the net can report `Sat` (unreachable) when a plan actually exists
\<Longrightarrow> **unsound** certificate. (`fluent_bounds_valid`, `fluent_lo f \<le> fluent_hi f`, is only the trivial
well-formedness half; the load-bearing half is *reachability ⊆ [lo,hi]*.)

- **Candidate mechanism:** the untracked `Numeric_Bound_Inference/` interval abstract-interpretation
  draft — infer sound over-approximating bounds `[lo,hi] \<supseteq> {reachable fluent values}`, so
  `num_seq_in_bounds` holds *by construction*; a problem with a genuinely unbounded fluent falls
  **outside** the certifiable fragment (report "out of scope", do not emit a bogus bound).
- **The interface the rest of the plan is built against** (so WP-A..D need not wait on the design):
  ```
  infer_fluent_bounds :: numeric_ground_problem \<Rightarrow> (fluent \<Rightarrow> int \<times> int) option
  lemma infer_fluent_bounds_sound:
    "infer_fluent_bounds P = Some b \<Longrightarrow> \<dots> \<Longrightarrow> num_seq_in_bounds"   (at fluent_lo/hi := fst/snd \<circ> b)
  ```
  WP-B consumes exactly this: `Some b` supplies `fluent_lo`/`fluent_hi` and discharges
  `num_seq_in_bounds`; `None` \<Longrightarrow> refuse the instance. **Everything downstream treats the plug as a black
  box**, so WP-A..D can be built and verified against a stubbed `infer_fluent_bounds` before the real
  interval analysis lands.

### WP-B (proof + exec) — numeric admission check + the numeric leaf

Realised as the ladder above (`numeric_ground_ast_problem_defs` DEFINES the data from `P`;
`numeric_ground_ast_problem = ground_ast_problem_core + numeric_ground_ast_problem_defs + <numeric-fragment wf>`).
The leaf's assumptions — now stated over the **DEFINED** data — are exactly the executable witnesses of the
`numeric_tp_nta_reduction[_correctness]` locale assumptions, minus the two non-static ones:

- **Faithfulness (discrete/exact fragment):** `nexp_ok`/`comp_ok` structure (exact `NDiv` only,
  `TP_NTA_Reduction_Numeric_Defs.thy:75,86`), `snap_upds_nexp_ok_{start,end}`,
  `snap_pre_comp_ok_{start,end}`, `snap_inv_comp_ok`, `num_goal_comp_ok`
  (`…Numeric_Model_Checking.thy:71`), `num_init_val_ok`. (`const_to_int_of_int` → **lemma** once
  `const_to_int` is defined.)
- **Well-formedness:** `upds_functional_{start,end}`, `upds_no_cross_read_{start,end}`,
  `snap_writes_nfluents_{start,end}`, `fluent_bounds_valid`. (`fluent_to_var_inj`/`fluent_vars_fresh`
  → **lemmas** if `fluent_to_var` is defined with a fresh scheme; else assumptions on the
  `fluent_to_var` param.) `upds_no_cross_read` is the side-condition making the **sequential** Munta
  update fold equal the **simultaneous** PDDL snap effect (`is_upds_num_upd`,
  `TP_NTA_Reduction_Numeric_Prelims.thy:365`) — necessary given the sequential update encoding, but
  mild: statically checkable, trivially true on additive/independent benchmark effects, and removable
  via fresh-temp-variable compilation if an instance ever needs intra-snap cross-reads.
- **Over_all restriction:** `n_inv_eq`, `n_inv_readonly`, `n_inv_init_sat`.
- **NOT discharged here:** `num_seq_in_bounds` (\<leftarrow> WP-E plug) and `num_valid` (the existential we
  contrapose — supplied by the `\<exists>\<pi>. numeric_plan_for_problem \<pi>` hypothesis at WP-A, exactly as the
  propositional `valid_ground_plan_imp_form_holds:13` does with `\<exists>tp. valid_ground_plan P tp`).

`check_numeric_ground_problem` (mirror of `check_ground_problem:595`) is the executable admission check
computing/verifying these on a concrete grounded numeric problem, and interpreting
`numeric_tp_nta_reduction_correctness` as a sublocale (given the WP-E plug). This is the numeric analog
of relaxing the `no_functions` restriction (`Ground_PDDL_Problem_Defs.thy`) that `check_ground_problem`
currently enforces — now expressed as swapping the `no_functions` leaf for the numeric-wf leaf off the
shared `ground_ast_problem_core`.
New file(s): `Ground_PDDL_Numeric_Problem_Defs.thy` (defs + leaf; `_Reduction` follows in WP-A/C).

### WP-A (proof) — Rung 4 over the numeric net

Interpret `numeric_tp_nta_reduction_correctness` at the ground problem (via WP-B) and lift the abstract
`num_valid_plan_imp_form_holds:2784` to:

```
num_valid_ground_plan_imp_num_form_holds :
  \<exists>\<pi>. numeric_plan_for_problem \<pi> \<Longrightarrow> num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula        (numeric net)
num_net_form_not_sat_imp_no_valid_ground_plan :                                      (contrapositive)
  \<not>(num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula) \<Longrightarrow> \<not>(\<exists>\<pi>. numeric_plan_for_problem \<pi>)
```

This is the numeric twin of `valid_ground_plan_imp_form_holds`
(`Ground_PDDL_NTA_Reduction_Correctness.thy:13`) but pointing at the **numeric** capstone over
`num_net_impl`, **not** the additive-tracking one over `net_impl`. Structurally it mirrors that proof
(`obtain \<pi>`; `interpret` the plan-carrying numeric locale; `by (rule num_valid_plan_imp_form_holds)`).
New file: `Ground_PDDL_Numeric_NTA_Reduction_Correctness.thy`.

### WP-C (exec) — `num_make_network_impl` + refinement

`num_make_network_impl` (mirror `make_network_impl:1427`) builds the concrete numeric net:

- `num_net_automata'` — main + action automata whose edges carry the numeric guards
  (`num_pre_guard`/`num_inv_guard`/`num_goal_guard`, `…Numeric_Defs.thy:55,58,61`) and numeric updates
  (`num_upd`/`num_init_upd`, `…Numeric_Defs.thy:64,67`), via `augment_edge` (`…Numeric_Defs.thy:107`);
- `num_net_bounds'` = `all_vars @ num_fluent_vars` (`…Numeric_Defs.thy:49`), the fluent `[lo,hi]` coming
  from the WP-E plug;
- `num_init_vars'` (`…Numeric_Defs.thy:148`), `num_reach_formula'` (= `reach_formula`, location-only),
  `num_init_locs'`.

Then `num_*_refine` + `num_make_network_impl_return_iff` (mirror `make_network_impl_return_iff:1447`)
tying the executable numeric net to the abstract `num_net_impl`
(`…Numeric_Model_Checking.thy:79`), and `num_model_checking_problem_refine` (mirror
`model_checking_problem_refine:1400`) composing WP-A. New file:
`Ground_PDDL_Numeric_NTA_Reduction_Impl.thy`.

### WP-D (exec) — numeric export  ⟵ *DEFERRED behind WP-E (see §4)*

Numeric entry point `check_and_cert_numeric_pddl_problem[_no_return]` + `num_check_and_make_network_opt`
(mirror `Check_Unsolvability.thy:1103,1193,1033`), wired to the **same** `make_certified_net` /
`Munta_Certificate_Checker` (fragment-agnostic — no numeric work there). `export_code` the numeric
constants (extend `Check_Unsolvability.thy:1235`, or a sibling `Check_Unsolvability_Numeric.thy`).
Register in `ROOT` under `PDDL_TP_Reduction`. **WP-D also repairs the propositional export tail**
(`check_ground_problem`, `make_network_impl`, `check_and_make_network` — the isolated blocks in
`Ground_PDDL_NTA_Reduction_Impl.thy`) and adds the numeric twins (`check_numeric_ground_problem`,
`num_make_network_impl`, `check_and_make_numeric_network`). **Scope decision (2026-07-10): do the
ASSEMBLY, DEFER the `export_code` / `String.literal` code-gen typeclass instances** if that block is a
rabbit hole.

**WP-D scouting result (2026-07-10), recorded for resume:**
- The propositional wf half — the linchpin — is SOLVED. Route the temporal well-formedness check through
  the *continuous* checker at the translated problem:
  ```
  definition "check_wf_temporal_problem P \<equiv> check_wf_cont_problem (temporal_to_continuous_problem P)"
  lemma check_wf_temporal_problem_return_iff[return_iff]:
    "check_wf_temporal_problem P = Inr () \<longleftrightarrow> wf_ast_temporal_problem P"
    <proof> interpret ast_temporal_problem P;
      unfolding check_wf_temporal_problem_def check_wf_problem_return_iff
      using wf_ast_cont_problem_equiv wf_ast_temporal_problem_def by simp
  ```
  `check_wf_cont_problem` / `check_wf_problem_return_iff` / `temporal_to_continuous_problem` /
  `wf_ast_cont_problem_equiv` all live in `Temporal_Planning.Temporal_PDDL_Checker_Explicit`, already
  imported by the Impl file. (NB `check_wf_problem_return_iff` yields `ast_cont_problem.wf_cont_problem`
  as the *0-ary sublocale* constant in the `ast_temporal_problem P` context — do NOT re-apply it to the
  translated problem.)
- `check_ground_problem` = that wf check + the nine `ground_ast_problem_core` structural checks via
  `check_all_list` (now INCLUDING the new `act_conds_no_args` — the eqAtm-free side condition added by the
  positivity re-point) + `functions D = []` + `consts D = []` + init check. Accessors changed by the
  re-point: `ast_temporal_action_schema_name` (not `ast_action_schema.name`), `D = ast_problem.domain P`.
  `check_ground_problem_return_iff` unfolds `ground_ast_problem_def`/`_axioms_def` +
  `ground_ast_problem_core_def`/`_axioms_def` + `list_all_iff` + `return_iff` (there is **no**
  `ground_ast_problem_defs_def` — the pure-import defs locale has no predicate `_def`); the leftover
  `ast_temporal_problem P` conjunct on the RHS needs a supplied fact (`by unfold_locales` did not close it
  — obtain it via `interpret ast_temporal_problem P` and thread it in).
- Numeric admission check `check_numeric_ground_problem` must (per HANDOVER) turn the leaf's
  `\<forall>w. num_val_ok w \<longrightarrow> nexp_ok w e` / `comp_ok` universals into a decidable STRUCTURAL sufficient
  condition and prove structural \<Longrightarrow> universal. The nexps come from `nexp_of_pddl` (NConst/NVar/NAdd/NSub/
  NMul/NDiv). A sound structural predicate: `NConst c \<Rightarrow> c \<in> \<int>`, `NVar f \<Rightarrow> f \<in> set nfluents`,
  Add/Sub/Mul recurse, `NDiv \<Rightarrow> False` (exact-division cannot be guaranteed structurally — the benchmarks
  have no NDiv). This gives only the FORWARD direction (`check = Inr () \<Longrightarrow> numeric_ground_ast_problem P`),
  which is exactly what the soundness assembly `check_and_make_numeric_network_and_plan` needs — NOT a full
  iff.

## 4. Dependency graph / ordering

**Ordering update (2026-07-10): WP-E is now sequenced CONCRETELY BEFORE WP-D**, not merely as a stubbed
interface. WP-A and WP-C are done carrying `fluent_lo`/`fluent_hi` as parameters and `num_seq_in_bounds`
as an assumption — that is sound for the *proof* chain, but WP-D produces a *runnable* checker whose
`num_net_bounds'` is built from `fluent_lo`/`fluent_hi` and whose admission must discharge
`num_seq_in_bounds`. A runnable checker cannot leave those abstract, so the real boundedness plug must land
before the export assembly.

```
WP-B  numeric admission check + numeric_ground_ast_problem locale         [DONE]
      │                        │
      ▼                        ▼
WP-A  rung-4 over num net     WP-C  num_make_network_impl + refinement     [DONE, bounds abstract]
      │                        │
      └───────────┬────────────┘
                  ▼
WP-E  bound inference: DEFINE fluent_lo/fluent_hi from P, DISCHARGE num_seq_in_bounds   ⟵ NEXT
      (Numeric_Bound_Inference/ interval AI; infer_fluent_bounds + infer_fluent_bounds_sound)
                  │
                  ▼
WP-D  numeric export_code + certificate wiring   (Munta cert checker reused UNCHANGED)
```

- WP-A/WP-C were built against **abstract** `fluent_lo`/`fluent_hi` + a carried `num_seq_in_bounds`, so the
  numeric proof chain is end-to-end verifiable already. WP-E swaps the abstract plug for one DEFINED from
  `P`; WP-D then consumes the concrete bounds.
- The certificate checker and `reach_formula` need **zero** numeric changes.

## 5. Verification / scope

- Per project rules: jEdit incremental (`jedit-status`), never a blind batch build; declare a file
  green only at `fully_processed: true` **and** `consolidated: true`, 0 errors, 0 sorries.
- The supported fragment is fixed by the `numeric_tp_nta_reduction[_correctness]` locale assumptions
  (integer-encoded fluents, exact-`NDiv` nexps, equality-only + read-only over_all invariants); WP-B's
  static checks are exactly the executable witnesses of those assumptions, and WP-E's plug the dynamic
  one.
- **End-to-end acceptance test:** a numeric instance that is *numerically unsolvable but
  propositionally reachable* — the propositional export yields no certificate, the numeric export
  yields a Munta-checked `Sat` \<Longrightarrow> "no valid numeric plan".

## 6. Cleanup / interlock flags

- `Numeric_Bound_Inference/` is untracked and in no ROOT — it is the natural home of WP-E; wire it in
  when the boundedness design lands.
- `TP_NTA_Reduction_Code.thy` is an orphan (in no ROOT, imported nowhere) — unrelated to this plan;
  retire or fold into the numeric export decision.
- Grounding interlock (numeric conditions/effects reaching the grounded target) is
  [GROUNDING_PLAN.md](GROUNDING_PLAN.md) §7 / [NUMERIC_PLAN.md](NUMERIC_PLAN.md) §4 — WP-B assumes the
  grounded numeric problem already carries `functions`, numeric effects, and numeric duration
  constraints (the numeric-free placeholder of the re-point must be lifted first).
