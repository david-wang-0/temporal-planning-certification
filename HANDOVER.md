# HANDOVER — numeric reduction is proved abstractly; NEXT = make it executable

## ⭐ SESSION STATUS (2026-07-23) — read this first

**Numeric certification runs END-TO-END.** `ML/out/plan_cert -certify numeric` emits nets for **4 of 5**
unsolvable gigante domains: majsp-impossible-1 (144260B), majsp-impossible-2 (3.8MB), MatchCellar-impossible
(159993B), sync-impossible (15757B). All committed & green.

**Landed & committed this session** (git `92ba24b … 0c8a49e`):
- Item 0 (snap-distinctness relaxation) end-to-end: primed `AtStart`/`AtEnd` reduction re-point, additive
  `numeric_tp_nta_reduction_bounds'` twin, `bound_inference` ground re-point, `nexp_struct_ok` rat exec-twins
  (Isabelle code-gen ignores type-instance code eqs → separate rat fun + eta bridge), harness `Or`-serializer fix.
- **PDDL quantifiers** (`forall`/`exists`) in the SML parser AST + two elimination strategies
  (`QUANT_EXPAND=early|grounded`, default early = quantifier-free grounder input = re-implementable in Isabelle;
  grounded = expand after schema-param instantiation). Fixed section-order parsing + empty `(and)` + conjunctive snaps.
- **Duration scaling** (`0c8a49e`): grounder multiplies all durations by LCM-of-denominators → integers
  (painter 4/5/6/15.004 → 1000/1250/1500/3751); K=1 no-op keeps others byte-identical. `quotient_of` added to the
  `export_code` list (durable).

**⏳ CURRENT NEXT STEP — relational fluent-fluent guard support (bounds painter's `counter`).** painter is the
ONLY domain not emitting a net: it now PARSES + grounds + scales durations, but `-certify numeric` stops at
`numeric bound inference failed` because `counter` is unbounded. Cause: its guard `(= (item_id ?i) (counter ?t))`
is fluent-vs-fluent (`item_id` is static: init-set 0/1/2, never assigned), and EVERY layer that handles guards is
fluent-vs-CONSTANT only, so it's dropped. FIX (chosen: **Approach 2 = relational interval refinement**, over the
"detect it's a constant" alternative — see below): make each guard layer refine a fluent `f` by the OTHER operand
`g`'s box interval `B g` (for `f = g`: refine BOTH to `B f ∩ B g`; painter's guard is `item_id = counter`, so the
STATIC LHS must also refine the RHS `counter`). Since the interval AI already infers `item_id = [c,c]` (no updates),
refining `counter` by it bounds `counter`. Soundness is LOCAL (interval meet), no plan invariant needed:
`comp_ok w (Comp op (NVar f) (NVar g))` ⟹ `nexp_ok w (NVar f) ∧ nexp_ok w (NVar g)` ⟹ **both f,g ∈ nfluents**
(`TP_NTA_Reduction_Numeric_Defs.thy:83`), so the box constrains `B g`.
FOUR layers, each currently fluent-const-only with a `_ ⇒ (None|B)` catch-all:
  1. **Draft projection** (untrusted, feeds SML bound inference): `g_int` datatype + `comp_to_gint`
     (`bound_parsing/Ground_PDDL_Numeric_Code_Export.thy:135,155-161`, exported to `code/Numeric_Projection.ML`).
     Add `(fluent,fluent)` `g_int` variants + project `Comp op (NVar f) (NVar g)`. **infer_box fails FIRST here**, so
     this + layer 2 are needed just to PROPOSE a bounded box.
  2. **The bound-inference AI itself** (verified HOL-IMP session `Numeric_Bound_Inference`) + SML glue
     `ML/plan_cert/src/numeric_glue/numeric_bound_glue.sml` (`pGint`, ~:52): extend the guard type + the interval
     refine to handle fluent-vs-fluent (refine by the other's interval). Re-verify + re-export.
  3. **Trusted re-check** (`refine_comp_exec`/`is_gbound_inv_exec`, `Ground_PDDL_Numeric_Code_Export.thy:54-61`):
     add the NVar-NVar cases so the proposed box VALIDATES (else rejected). Re-export.
  4. **Abstract cert** (frozen `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy`): `refine_comp` (:533-540) + the
     soundness lemma `refine_comp_pres` (:840) / `refine_box_sound` (:995) — add the 5 NVar-NVar cases + extend the
     proof (uses `B g` + `g ∈ nfluents` from `comp_ok`), for the exec⟹abstract correspondence.
Verify: painter emits a net under BOTH `QUANT_EXPAND`; majsp/MatchCellar/sync byte-identical. Then re-export
bound_parsing (`-e`), `make build_certifier`, re-run all 5.
*(NOTE for the fresh session: jEdit may be down — relaunch + rebuild the `Temporal_Planning_Base` heap for the
frozen-layer `refine_comp` proof. The exec/draft/glue parts are SML/build-only.)*

**Other open work:** the **nemo** datalog-reachability integration in `ML/plan_cert/src/grounder.sml` (grounder
task #22b — the grounder already does TFD-style relaxation); the deferred WP-D full code-gen tail (Containers/
`String.literal` typeclasses) if the numeric NETWORK builder ever needs to code-gen standalone.

---

> **RE-SEQUENCED (2026-07-10): do WP-E (numeric bound inference) BEFORE WP-D (executable export).**
> The exported checker must COMPUTE `fluent_lo`/`fluent_hi` and discharge `num_seq_in_bounds` from the
> problem `P`, so the boundedness plug has to land before the export assembly. A WP-D start was rolled
> back to committed-green on this decision. Details in the NEXT bullets of the 2026-07-09 status below.

## TODO / BACKLOG — consolidated (2026-07-10)

The canonical task list. `#N` labels are the ones referenced in commits/memory; the numbering is sparse
(only #1/#2/#8/#9 were ever assigned numbers), so **this section — not the numbers — is the source of
truth**. Per-task detail lives in the dated logs in the ARCHIVE below and in `NUMERIC_EXEC_PLAN.md`.

### IN PROGRESS / NEXT (ordered)

0. **SNAP-DISTINCTNESS RELAXATION — DONE END-TO-END & COMMITTED. The numeric certification pipeline emits nets for mixed simple+durative numeric problems (majsp) and the other parseable unsolvable domains.**
   *COMMITS:* `92ba24b` reduction re-point, `c5297f9` bounds twin, `932a62c` bound_inference ground re-point,
   Code_Export proof fix, `20ea933` harness Or-serializer fix, `22d2e30` nexp_struct_ok rat exec-twins.
   *SMOKE TESTS (2026-07-23, `ML/out/plan_cert -certify numeric`, easiest instance each):*
   majsp-impossible-1 ✅ net (144KB), majsp-impossible-2 ✅ net (3.8MB, box [0,25]),
   MatchCellar-impossible ✅ net (160KB, empty box = durative-only). painter-impossible / sync-impossible ❌
   still fail (in the HARNESS PDDL parser, NOT the numeric pipeline) — TWO gaps:
   (a) FIXED (`ML/plan_cert/src/parsing/pddl_refactor.sml`, committed): the domain parser enforced a fixed
       section order; painter/sync reorder them (`:constants` after `:functions`; `:functions` before
       `:predicates`). Now the 5 header sections parse in ANY order.
   (b) FIXED (`9029e43`): `forall`/`exists` quantifiers added to the SML PDDL AST (`Prop_all`/`Prop_ex`;
       `FORALL_EFFECT`/`FORALL_SNAP`) + parser (conditions + effects, typed binders), eliminated by expansion
       over the (subtype-aware) domain/problem objects with TWO selectable strategies (`QUANT_EXPAND=early|grounded`,
       default early): EARLY expands at the PDDL→C boundary (grounder sees quantifier-free input — matches the
       verified classical grounder, re-implementable in Isabelle); GROUNDED carries quantifiers past the C
       translation in a grounder-internal forall-carrying type (`QAst`), instantiates schema params FIRST, then
       expands + relax/fold per ground instance. Isabelle `Converter` types untouched. Also fixed two silent-drop
       bugs + two incidental grammar gaps (empty `(and)` precond, conjunctive `(at start (and e1 e2 …))` snaps).
   *POST-QUANTIFIER SMOKE (both strategies): sync-impossible NOW ✅ emits a net; majsp-1/2 + MatchCellar still ✅
   (byte-identical across strategies); painter-impossible now PARSES + grounds (127 actions) but no net — blocked
   by TWO quantifier-ORTHOGONAL limits: non-integer duration `15.004` (integer-duration net builder) + unbounded
   `counter` fluent (numeric bound-inference returns NONE). So 4/5 unsolvable domains emit numeric nets end-to-end;
   painter needs the (separate) non-integer-duration / unbounded-fluent handling. Compactness: early == grounded
   for these (forall vars independent of schema params).*
   *NEXT: nemo datalog-reachability integration in `grounder.sml` (task #22b); painter's non-integer-duration +
   unbounded-fluent handling.*
   Cleanup: `check_numeric_ground_problem_diag` + the `+ [dbg]`-free plan_cert are the runnable glue; the
   `check_numeric_ground_problem_diag` is still labelled temporary.
   *(historical: the final blocker was `nexp_struct_ok`'s `NConst c => c : Ints` clause code-generating
   polymorphically with a ring_1 dict (image over UNIV -> abort); FIXED via rat exec-twins routed into the
   admission check — Isabelle code-gen does NOT honour type-instance code equations, so a separate rat fun +
   eta-form bridge in _return_iff was needed, not a [code] redirect. `22d2e30`.)*
   *Why (original motivation):* `check_numeric_ground_problem` rejected majsp at the snap-distinctness clause — every SIMPLE action's
   `at_end_spec` is the constant `ground_non_action`, so `distinct (map at_end_spec actions_spec)` fails with ≥2
   simple actions. The numeric reduction inherits `snaps_disj` from the propositional base; the propositional path
   escapes it by building the net over the INJECTIVE `AtStart`/`AtEnd` snap_action datatype (primed layer
   `tp_nta_reduction_defs'` → `reduction_ref_impl`). The numeric stack had no primed layer.
   *DONE (committed `8956184`, both TA_Network files green, 0 sorries):*
   - `TP_NTA_Reduction_Numeric_Defs.thy`: `numeric_tp_nta_reduction_defs'` (twin of `tp_nta_reduction_defs'`,
     `reduction_ref_impl` at `AtStart`/`AtEnd`, numeric data via `rat_impl.set_impl.app_snap n_pre`/`upds`) + a
     DROP-IN aliasing block (64 `abbreviation X = reduction_ref_impl.X` + 57 `lemmas X_def`) so a leaf switched to
     `defs'` keeps every `ndefs.X`/`ndefs.X_def` resolving.
   - `TP_NTA_Reduction_Numeric_Model_Checking.thy`: `numeric_tp_nta_reduction_correctness'` +
     **`num_relabel_equiv`/`fold_reindex_collapse`** — the numeric analog of `plan_validity_equivalence`
     (Temporal_Plans.thy:1876): `num_valid_plan`/`num_valid_state_sequence` invariant under restrict-to-props +
     `AtStart` relabel. Crux: the non-injective relabel would double-apply the non-idempotent happening-fold, but
     `num_mutex_valid_plan` forces any snap-collision to `upds={}` (a numeric no-op), so the fold reparametrizes.
   *DONE (2026-07-22, jEdit-verified GREEN + consolidated on all 3 files, 0 sorries; UNCOMMITTED):*
   1. `Ground_PDDL_Numeric_Problem_Defs.thy` — leaf `numeric_tp_nta_reduction_defs` → `numeric_tp_nta_reduction_defs'`
      (identical arg list; `snaps_disj` drops, `ndefs.X` resolves via aliases). GREEN.
   2. `Ground_PDDL_Numeric_NTA_Reduction_Correctness.thy` — removed the dead `nred` sublocale; `num_plan` →
      `numeric_temp_plan_for_problem_list_impl_int'`; `ncorr` → `numeric_tp_nta_reduction_correctness'`, discharged by
      `by unfold_locales (fact num_plan.vp num_plan.nso num_plan.pap <14 leaf wf> num_valid_plan num_seq_in_bounds
      num_goal_comp_ok fluent_to_name_spec_inj)+` (order-independent). Capstone re-pointed to
      `ncorr.ref_correctness.num_valid_plan_imp_form_holds` + `x.ncorr.ref_correctness.num_a\<^sub>0_def`. GREEN.
   3. `Ground_PDDL_Numeric_NTA_Reduction_Impl.thy` — snap-arg refines re-stated PER SNAP (`num_pre_guard_refine_start/end`,
      `num_upd_refine_start/end` over `AtStart a`/`AtEnd a` = `at_start_spec a`/`at_end_spec a`; mutex/net_int_clocks/
      snap_vars/edge/automaton refines side-conditioned on `a \<in> set actions_spec` mirroring `Ground_PDDL_NTA_Reduction_Impl.thy`;
      restricted `pre_imp_restr_list` aligned via `pre_imp_restr_equiv_pre_imp`). Snap-distinctness clause DELETED from
      `check_numeric_ground_problem` + `_diag` (renumbered 3..16 → 2..15) + `_return_iff` conjunct; in `_sound` the
      `sd`/`se`/`sde` block + `snaps_disj_on` subgoal removed and the local interpret re-pointed to
      `numeric_tp_nta_reduction_defs'`, its 6 primed-base obligations discharged by
      `(fact core.abstr_model_checking.distinct_props … act_consts_in_init_consts)+` (the same facts
      `ground_ast_problem_base`'s `abstr_model_checking` sublocale proves), `ne_ok`/`cp_ok` intro rules switched to
      `ndefs.reduction_ref_impl.{nexp,comp}_struct_ok_sound`. GREEN + consolidated.
   *REMAINING = step 4. `isabelle build -d . PDDL_TP_Reduction` GREEN (2026-07-22, 1:41). BUT downstream
   `bound_inference` FAILS — a bigger re-point than "call-site fixes" (surfaced to David):*
   - `bound_inference/Ground_PDDL_Numeric_NTA_Reduction_Bounds.thy` + `_Cert_Impl.thy` are built entirely on the
     REMOVED unprimed `nred: numeric_tp_nta_reduction` sublocale: `numeric_ground_ast_problem_cert` assumes
     `nred.is_gbound_inv'` → `Undefined constant "nred.is_gbound_inv'"`. There is **no primed
     `numeric_tp_nta_reduction_bounds'` twin** (only `_defs'`/`_correctness'` were made in `8956184`).
   - GOOD NEWS: `num_bound_inv`/`is_gbound_inv'`/`is_gbound_inv'_imp_num_bound_inv` (`TP_NTA_Reduction_Numeric_Bounds.thy`
     :27/:549/:1020) are defined purely over DEFS-level data (`all_snaps`, `upds s`, `n_pre s`, `fluent_in_bounds`,
     interval `aeval`/`refine_box`) — they do NOT use `snaps_disj`/snap-injectivity, so they can be HOISTED from
     `context numeric_tp_nta_reduction` down into `context numeric_tp_nta_reduction_defs` (mechanical, no new proofs)
     and aliased into `numeric_tp_nta_reduction_defs'` → reachable as `ndefs.is_gbound_inv'` on the primed path.
   - WRINKLE (found while scoping — makes the "hoist + alias" NOT clean): the static SOUNDNESS bridge
     `is_gbound_inv'_imp_num_bound_inv` (:1020) + the interval lemmas (`const_to_int_round_trip`/`aeval_sound`/
     `refine_box_sound`/…) use `const_to_int_of_int`, which is an ASSUMPTION of `numeric_tp_nta_reduction`
     (`TP_NTA_Reduction_Numeric_Defs.thy:244`), NOT available at plain `numeric_tp_nta_reduction_defs`. So only the
     DEFINITIONS (`all_snaps`/`num_bound_inv`/`is_gbound_inv'`/`refine_box`/`box`/`map_ibnd2`/`in_refine_box` + the
     `num_bound_inv_initD/stepD/I` rules) hoist to plain defs; the soundness bridge needs an intermediate locale
     `numeric_tp_nta_reduction_defs + assumes const_to_int_of_int` (which `numeric_tp_nta_reduction` would then extend,
     and the primed ground path interprets at `reduction_ref_impl` — const_to_int_of_int holds there as the ground lemma
     `Ground_PDDL_Numeric_Problem_Defs.thy:138`). ALSO: `TP_NTA_Reduction_Numeric_Bounds.thy` is in the BASE
     `TP_NTA_Reduction` session, so ANY edit reverifies the whole tower (PDDL_TP_Reduction + bound_inference) — not
     "low-risk"; and aliasing into `defs'` needs a `context numeric_tp_nta_reduction_defs'` block IN Bounds.thy (defs'
     is defined upstream in Defs.thy, before the bounds definitions exist).
   - PLAN-CARRYING PART: the discharge `numeric_tp_nta_reduction_bounds` (:75) + `num_seq_in_bounds_derived` (:427) via
     `happening_preserves_fib` (:308) use `upds_functional` + `num_mutex_snap_action` non-interference — **NOT**
     `snaps_disj` or snap injectivity — so a primed twin `numeric_tp_nta_reduction_bounds'` re-deriving
     `numeric_tp_nta_reduction_correctness'` IS constructible via the same `num_relabel_equiv` machinery as `..._correctness'`
     (`8956184`). Real work, but the logic transfers.
   - RECOMMENDED SHAPE A' (refined 2026-07-22 after reading the ground cert files; David chose "A"): the plan-carrying
     discharge `num_seq_in_bounds_derived` fundamentally needs `numeric_tp_nta_reduction_bounds` at the INJECTIVE snaps
     (num_relabel_equiv machinery) — no frozen-free route for it. So the ONE needed frozen change is a single ADDITIVE locale
     `numeric_tp_nta_reduction_bounds'` in `TP_NTA_Reduction_Numeric_Bounds.thy` that MIRRORS the already-proven
     `numeric_tp_nta_reduction_correctness'` (`TP_NTA_Reduction_Numeric_Model_Checking.thy:527`), swapping `num_seq_in_bounds`
     for `num_bound_inv` (via `is_gbound_inv'_imp_num_bound_inv`) and re-deriving `numeric_tp_nta_reduction_correctness'` through
     its own `ref_bounds: numeric_tp_nta_reduction_bounds` sublocale at injective snaps. ADDITIVE (new locale, no edit to existing
     base locales) ⇒ reverifies only itself + downstream, NOT the whole tower; NO intermediate `const_to_int_of_int` locale
     needed (the twin's internal injective reduction interpretation carries `const_to_int_of_int` from the injective params).
     Then GROUND re-point `bound_inference/{Bounds,Cert_Impl}.thy` EXACTLY mirroring the committed Correctness re-point (`92ba24b`):
     `numeric_ground_ast_problem_cert` static cert via the injective reduction; `numeric_valid_ground_plan_cert` `num_plan`→primed
     + `nbnd: numeric_tp_nta_reduction_bounds'`; capstone via `nbnd.ref_bounds.*` (like `ncorr.ref_correctness.*`). Then rebuild
     bound_parsing + export + majsp test. NOT STARTED (paused at end of the 07-22 session; twin is the crux artifact).
   - Then re-point ground `Bounds.thy`/`Cert_Impl.thy` to the primed path (+ `_return_iff`/`_sound`), rebuild
     `bound_inference` → `-e bound_parsing` (re-export) → `cd ML && make build_certifier` → majsp test:
     `ML/out/plan_cert -domain examples/gigante/majsp-impossible-1/pddl21/domain_integers.pddl
     -problem …/instances/instance_1_2_3_1.pddl -model /tmp/m.muntax -certify numeric`.

1. **WP-E — numeric bound inference (soundness-critical). BOTH SIDES DONE & GREEN** (committed). Structure
   (David's Option 1): **`is_gbound_inv' ⟹ num_bound_inv ⟹ num_seq_in_bounds`**.
   - **Reduction check — `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy` (in ROOT): 0 sorries.** `num_bound_inv`
     cert (init+step; `_initD`/`_stepD`/`_I` rules); locale `numeric_tp_nta_reduction_bounds` swaps
     `num_seq_in_bounds` for the checkable `num_bound_inv`; bridge `num_seq_in_bounds_derived` GREEN (kernel
     `happening_preserves_fib` + induction on `i`) ⇒ `sublocale numeric_tp_nta_reduction_correctness` re-derives
     the numeric-net capstone from the cert (`_correctness` UNTOUCHED). Inline finite-`int` interval check
     `aeval`/`refine_box`/`is_gbound_inv'` + `aeval_sound`/`refine_box_sound`/`is_gbound_inv'_imp_num_bound_inv`
     all PROVED (NDiv `None`'d = fail-closed; `refine_box_sound` carries a guard-const-integrality hyp).
     `const_to_int_of_int` moved DOWN into base `numeric_tp_nta_reduction` (`TP_NTA_Reduction_Numeric_Defs.thy:244`).
   - **Compute — `Numeric_Bound_Inference/` (session `= "HOL-IMP"` in main ROOT): green.** Threshold analysis +
     tight `thr_set` + NEW `Numeric_Bound_Inference_Extract.thy`: `infer_fluent_bounds` (`ginfer_thr` `eint` box →
     finite `int` box, `None` = "bound-inference failed" on any ∞) + `infer_fluent_bounds_sound`; `value` demos
     `Some (0,1)` / `None`. **TERMINATION proof SKIPPED** (by design).
   - **WP-D INTEGRATION (proof-side) — DONE & GREEN (2026-07-11), UNCOMMITTED.** New file
     `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Bounds.thy` (in ROOT after `…_Numeric_NTA_Reduction_Impl`;
     fully_processed + consolidated, 0 errors/sorries; 1 benign ambiguous-parse warning on the
     `sem, a\<^sub>0 \<Turnstile> formula` notation — identical to the committed WP-A file's). Structure (mirrors the WP-A file
     `…_Numeric_NTA_Reduction_Correctness.thy`, swapping the per-plan `num_seq_in_bounds` for the static cert):
       - plan-free `locale numeric_ground_ast_problem_cert = numeric_ground_ast_problem + assumes nred.is_gbound_inv'`;
         `lemma num_bound_inv: nred.num_bound_inv` via `nred.is_gbound_inv'_imp_num_bound_inv`;
       - plan-carrying `locale numeric_valid_ground_plan_cert` (twin of `numeric_valid_ground_plan`, WITHOUT the
         `num_seq_in_bounds` assumption) `sublocale nbnd: numeric_tp_nta_reduction_bounds` (3 subgoals: `num_valid`,
         `num_bound_inv`, `num_goal_comp_ok`), re-deriving the numeric-net capstone from the cert;
       - `num_valid_ground_plan_imp_num_form_holds` + contrapositive `num_net_form_not_sat_imp_no_valid_ground_plan`
         over `num_net_impl.sem` — boundedness now discharged, NOT a per-plan assumption. `fluent_lo/hi` stay
         parameters (a concrete instance fixes them to the inferred box).
   - **NEXT = WP-D EXECUTABLE end-to-end** (rides with the export tail): actually *computing* `fluent_lo/hi` from
     `P` (`infer_fluent_bounds`) and *eval-checking* `nred.is_gbound_inv'` needs a reduction-snaps → draft-gactions
     translation via EXPORTED ML — cannot be one theory (HOL-IMP `option`-arity clash). Folds into WP-D §2 below.
   - **Facts locked (don't re-litigate):** HOL-IMP not importable into the reduction (`option`-arity clash);
     `int` is FORCED (Munta `Simple_Network_Impl`, `Simple_Network_Language_Impl.thy:186`); **rebuild the clean
     base heap** (`isabelle build -b Temporal_Planning_Base`, drops the stale `Abs_Int3` bake) before relying on
     it locally. Cleanup: hoist the duplicated base-locale `const_to_int_*`/`nexp_ok_*` twins; delete stray
     `.thy~`. Detail: `NUMERIC_EXEC_PLAN.md` §WP-E + `Numeric_Bound_Inference/BOUND_INFERENCE_PLAN.md` §0' +
     memory `numeric-bound-inference-draft`.
2. **WP-D — executable admission-check + network assembly. DONE & COMMITTED (2026-07-11).** Commits
   `cf3c0f0` (bounds-discharge integration + prop export tail + numeric structural core), `998170e`
   (`check_ground_problem_core` refactor + `check_numeric_ground_problem` forward soundness),
   `3b14aa8` (`num_make_network_impl` + `check_and_make_numeric_network` soundness + missing-theory-end fix).
   **NOT YET DONE (the runnable tail, per David deferrable):** the actual `export_code` / `String.literal`
   code-gen typeclass instances (`proper_interval`/`Abs_literal`), and the bound-computation ML bridge that
   *computes* `fluent_lo/hi` from `P` (`infer_fluent_bounds`, cross-session HOL-IMP) + *eval-checks*
   `nred.is_gbound_inv'` so `check_and_make_numeric_network`'s soundness upgrades from the per-plan
   `numeric_valid_ground_plan` conclusion to the bounds-discharged `numeric_valid_ground_plan_cert` capstone.
   Detail of what landed below (kept for the recipes).
   - **Propositional export tail RE-DERIVED & green** in `Ground_PDDL_NTA_Reduction_Impl.thy` (bottom, new
     `section` at global scope, ast_cont_* namespace): `check_wf_temporal_problem` (+`_return_iff` +
     `isOK_check_wf_temporal_problem[simp]` bridge), `check_ground_problem` (+`_return_iff` \<longleftrightarrow>
     `ground_ast_problem P`; proof = `interpret ast_temporal_problem P` then unfold
     `ground_ast_problem_def`/`_axioms_def`/`ground_ast_problem_core_def`/`_axioms_def` then
     `by (auto simp: return_iff list_all_iff)` — return_iff as SIMP, not `unfolding`, else the do-block binds
     don't fire), `make_network_impl` (+`_return_iff`), `check_and_make_network` (+`check_and_make_network_and_plan`
     via `ground_ast_problem.model_checking_problem_refine`). Net constructors unchanged since the OLD template
     (`ground_ast_problem_defs.net_automata' P` etc.). The two TOP `WP-D ISOLATION` text notes + the bottom one
     are now STALE (code re-derived) — update in a cleanup pass (editing them reprocesses ~900 cmds).
   - **Numeric structural-faithfulness CORE done & green** in `Ground_PDDL_Numeric_NTA_Reduction_Impl.thy`
     (new subsection after the constructors context): global `nexp_struct_ok`/`comp_struct_ok`
     (`NConst\<Rightarrow>\<in>\<int>`, `NVar\<Rightarrow>\<in>fs`, +/-/* recurse, `NDiv\<Rightarrow>False`) + `context numeric_tp_nta_reduction_defs`
     lemmas `nexp_struct_ok_sound`/`comp_struct_ok_sound` (`struct \<Longrightarrow> \<forall>w. num_val_ok w \<longrightarrow> nexp_ok/comp_ok`;
     `by (induction e) (auto simp: num_val_ok_def)` / `by (cases c) (auto intro: nexp_struct_ok_sound)`). This is
     the HARD linchpin the plan flagged.
   - **(a) DONE** — prop `check_ground_problem_core` (9 checks, ⟷ `ground_ast_problem_core P`) + `isOK` bridge
     `isOK_check_ground_problem_core[simp]` + `check_ground_problem = core + no_functions`. In `…_NTA_Reduction_Impl.thy`.
   - **(b) DONE** — `check_numeric_ground_problem fluent_lo fluent_hi` (`context numeric_ground_ast_problem_defs`):
     core + decidable leaf checks + structural nexp/comp + a fail-closed snaps-disjointness check; forward
     soundness `check_numeric_ground_problem_sound : = Inr () ⟹ numeric_ground_ast_problem P fluent_lo fluent_hi`
     (`isOK_check_all_list[simp]` helper; structural universals via `nexp_struct_ok_sound`/`comp_struct_ok_sound`).
     \<^bold>\<open>ADMISSION RESTRICTION discovered\<close>: the numeric `ndefs` inherits the UNPRIMED
     `temp_planning_problem_list_impl_int`, which requires `snaps_disj` (distinct raw start/end ground snaps) — the
     propositional side uses the PRIMED variant to tolerate snap non-injectivity, but the numeric layer does not.
     So the check verifies snap-disjointness fail-closed (sound; mild for the numeric fragment — durative schemas
     with distinct bodies pass, ≥2 simple/instantaneous schemas are rejected since `at_end_spec` collapses them to
     `ground_non_action`). Lifting it = re-base the numeric reduction on labelled snaps (a design change, not a fix).
   - **(c) DONE** — `num_make_network_impl` + `_return_iff`, `check_and_make_numeric_network` +
     `check_and_make_numeric_network_and_plan` (net unreachable ⟹ ¬∃π. `numeric_valid_ground_plan` — the WP-C
     `num_model_checking_problem_refine`, PER-PLAN bounds). Broadcast bridge needs the leaf interpretation
     (`interpret leaf_i; unfolding leaf_i.ndefs.net_broadcast_def` — the abstract/exec broadcasts are both `[]` but
     the constant is a parameterized locale-def). Also fixed a pre-existing MISSING theory-`end` in this file
     (never consolidated; batch-build would reject; nothing imports it so latent).
   - **(d) NO-PER-PLAN-BOUNDS soundness DONE & green (2026-07-12), UNCOMMITTED.** NEW file
     `Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl.thy` (in ROOT after `…_Bounds`; imports WP-C Impl + WP-D Bounds;
     fully_processed + consolidated, 0 errors/sorries; opened in the running jEdit WITHOUT a restart — imports
     already loaded). `context numeric_ground_ast_problem_cert`: `num_model_checking_problem_refine_cert` (mirror
     of the WP-C `num_model_checking_problem_refine` but firing the WP-D cert capstone
     `num_net_form_not_sat_imp_no_valid_ground_plan`, which shadows the inherited WP-A one) — exec net unreachable
     ⟹ ¬∃π. `numeric_valid_ground_plan_cert`. Global `check_and_make_numeric_network_and_plan_cert`: given the
     check result + `numeric_ground_ast_problem_cert P fluent_lo fluent_hi` (leaf + `is_gbound_inv'` — the static
     boundedness cert, an ASSUMPTION here), a Munta-unreachable exec net ⟹ NO valid numeric plan (no residual
     per-plan `num_seq_in_bounds`). Proof reuses the per-plan assembly's chk/mk/eqs + broadcast bridge
     (`interpret C; unfolding … C.ndefs.net_broadcast_def`).
   - **NEXT (fully runnable):** make `is_gbound_inv'` EXECUTABLE + the `infer_fluent_bounds` cross-session ML
     bridge, so `check_and_make_numeric_network` (or a `_cert` variant) *computes* `fluent_lo/hi` and *discharges*
     the `numeric_ground_ast_problem_cert` hypothesis by eval instead of assuming it; then `export_code` (DEFER
     the `proper_interval`/`Abs_literal` String.literal code-gen instances per David if they rabbit-hole).

### OPTIONAL / completeness (not a WP blocker)
- **#9 — replace the over-approximating numeric mutex with the CORRECT (FPS `acts_non_intrf`) condition.**
  Est. **MEDIUM–HARD, ~1–2 focused days**, deep in the commutation core. It lifts the deliberate "design B"
  soundness shortcut (`d809a59`), so it is a generality gain (accept additive co-writers like the painter
  `counter`), not a fix. Current `num_mutex_snap_action` (`Temporal_Plans.thy:361`) flags **any** shared
  write as mutex; the correct FPS clause (`Formal-PDDL-Semantics/Continuous_Planning/Numeric_Update_Functions.thy:64`
  `acts_non_intrf`) permits a shared write when **both** are additive
  (`lvalues\<^sub>a \<inter> lvalues\<^sub>b \<subseteq> additive_lvalues\<^sub>a \<inter> additive_lvalues\<^sub>b`; + intra-action `numeric_effects_non_intrf`).
  Work, by hardness:
  - **(2, HARD — load-bearing) re-prove commutation** `snap_num_update_commute` / `happening_num_update_swap`
    / `comp_fun_commute_on_snap_num_update` (`Temporal_Plans.thy:437–519`). Current proof = disjoint supports
    \<Rightarrow> equal rhs reads \<Rightarrow> commute; that DIES for additive co-writes (both write+read `f`). New proof splits the
    shared-`f` case and uses `+`/`-` assoc+comm on `'r` (verify the locale's `'r` sort is an additive abelian
    group — rat/int qualify). Must reconcile the abstract COMBINED form `(f, NAdd (NVar f) e)` (our fold reads
    rhs at the RUNNING val) with FPS's UNCOMBINED `w' a + b\<lbrakk>w\<rbrakk>` (rhs at the FIXED pre-state): they agree
    exactly under `lvalues \<inter> rvalues = {}`, so that clause must be threaded as a hypothesis.
  - **(1, LOW–MED) refined def** — add `snap_additive_writes`, relax the write/write clause, and STRIP the
    implicit additive self-read (`NVar f`) from `snap_reads` so it matches FPS `rvalues`. `Temporal_Plans.thy:342–365`.
  - **(3, MED) re-thread ~43 uses** (Numeric_Edges 15, Numeric_Projection 6, Temporal_Plans 22):
    `num_mutex_valid_plan` weakens (fine — `TP_NTA_Reduction_Numeric_Edges.thy:713` reads it off `num_valid`);
    consumers `happening_num_noninterfere` \<rightarrow> order-independence carry the extra `lvalues \<inter> rvalues` hyp; the
    \<epsilon>-guard generator (`TP_NTA_Reduction_Properties.thy` `mutex_{0,eps}_constraint_sat`, `mutex_effects`) emits
    fewer guards, so `TP_NTA_Reduction_Numeric_{Steps,Projection}` must show interleaved zero-delay additive
    edges reproduce the simultaneous accumulate (multi-same-var-write-per-happening equivalence).
  - **(4, MED — the payoff) executable bridge** — the grounder side (`Ground_PDDL_Plan_Defs.thy:660`
    `acts_non_intrf_imp_mutex_snap_action`) ALREADY uses the correct FPS `acts_non_intrf`; the numeric
    co-write is currently dodged via `wf_ground_action_{numeric_effects,lvalues,additive_lvalues}_Nil` +
    fail-closed Layer-C. Once the abstract def matches, prove the numeric bridge and lift the fail-closed
    restriction.
  - **(5, LOW) migration** — `num_mutex_snap_action_empty` / `num_mutex_valid_plan_empty` still hold; minor
    re-proof. Biggest risks: step 2's algebraic commute + step 3's Munta same-clock multi-write.

### DONE & COMMITTED
- **#1** `fluent_to_var` refactor — now a DEFINED constant off `fluent_to_name` (mirrors `prop_to_var`) — `4d92574`.
- **#2** core-rebase (gate for WP-A) — `ground_ast_problem_core` given the body; classical demoted to
  `core + no_functions` — `fef6bc9`.
- **WP-A** numeric-net lift (`Ground_PDDL_Numeric_NTA_Reduction_Correctness.thy`) — `fef6bc9`.
- **WP-C** executable numeric net + refinement (`Ground_PDDL_Numeric_NTA_Reduction_Impl.thy`) — `fef6bc9`.
- Propositional exec/export layer REPAIR (`Ground_PDDL_NTA_Reduction_Impl.thy`, committed-broken since the
  FPS re-point) — `fef6bc9`.
- **#8** numeric over-all redesign (design **B**, a sound over-approximation; design A rejected as unsound) —
  `d809a59`. See `numeric-overall-redesign-decisions` memory + `NUMERIC_OVERALL_REDESIGN.md` (DO-NOT-IMPL-A banner).

### COMMITTED since (supersedes the old "UNCOMMITTED (WP-E code)" list)
- **WP-E — numeric bound inference COMPLETE** (`aeaba18`, on top of `ea1e9e1`): reduction interval check
  (`TP_NTA_Reduction_Numeric_Bounds.thy`, 0 sorries) + compute-side extract/reject (`Numeric_Bound_Inference/`).
  The base heap was rebuilt clean **before** that commit — `isabelle build -n Temporal_Planning_Base` reports
  up-to-date, and the reduction chain loads green on it in jEdit (no `option`-arity clash). No rebuild needed now.
- The git tree is **CLEAN** as of `aeaba18`; the old per-file "uncommitted" enumeration below is stale.

### UNCOMMITTED (WP-D INTEGRATION + docs)
- NEW `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Bounds.thy` (green; in `ROOT` after
  `…_Numeric_NTA_Reduction_Impl`) — the proof-side WP-D integration (see TODO item 1).
- `ROOT` (one line added). `HANDOVER.md` (this update).

**Docs (pre-existing, from the WP-E cycle):** `ARCHITECTURE_pipeline.md`, `NUMERIC_PLAN.md`, `NUMERIC_EXEC_PLAN.md`,
`SEMANTICS_REPOINT_PLAN.md`, `Numeric_Bound_Inference/BOUND_INFERENCE_PLAN.md` (§0'). Untracked docs:
`ARCHITECTURE_dependencies.md`, `REFACTOR_SPEC.md`.

### CLEANUP flagged (do not silently skip — per project preference)
- **Dedup the RAW-level refine stack.** WP-C re-proved ~40 `ndefs_*` refine lemmas because the prop
  `*_refine` are gated behind `no_functions` and target the REFINED net; a shared RAW-level refine stack in
  `ground_ast_problem_core` would dedup. Memory `numeric-exec-impl-layer-status`.
- **Stray `find_theorems "inst_of_plan_action"`** in `Ground_PDDL_Plan_Defs.thy` (~line 1527, green territory).
- **Stray `.thy~` editor backups** (in no ROOT) in `TA_Network/` (many) + `Ground_PDDL_Exec_Imp/` — delete in a
  housekeeping pass. (Also `Numeric_Bound_Inference/*.thy~`.)
- **Stale `SORRY (WP-E)` doc comments** in `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy` (the `text` blocks
  above `aeval_sound` ~line 723, `refine_box_sound` ~993, `is_gbound_inv'_imp_num_bound_inv` ~1014) still read
  "\<^bold>SORRY (WP-E)" though those lemmas are now fully proved (no `sorry` tokens; `aeaba18` closed them).
- **Stale Isabelle component registration** (`~/.isabelle/Isabelle2025-2/etc/components`): the retired
  `/home/david/work/verified-classical-sat-based-pddl-planner` (+ its `Isabelle-Graph-Library` submodule) is
  still listed — de-submoduled per memory `dependency-layout`, so every `isabelle` invocation warns "Missing
  Isabelle component". Also `~/stuff/AutoCorrode/isabelle-assistant`, `hugo-0.152.0`. Non-blocking; prune the
  dead lines.
- **Hoist the `_bnd` S-property lemmas.** The bridge (`TP_NTA_Reduction_Numeric_Bounds.thy`) re-derived
  `happening_finite_bnd`/`happening_subseteq_all_snaps`/`happening_num_noninterfere_bnd`/… because their
  `_correctness` twins sit in the sublocale it establishes; hoist the plan-derived S-property lemmas to a shared
  ancestor (`numeric_tp_nta_reduction` + `num_valid`) so both `_bounds` and `_correctness` share one copy.

---

## CURRENT STATUS (2026-07-09) — detailed log (see TODO above for the live snapshot)

> NOTE (2026-07-10): the #1/#2/WP-A/WP-C/exec-repair work described below as "UNCOMMITTED on disk" is now
> COMMITTED (`fef6bc9`, `4d92574`); #8 is `d809a59`. Only docs remain uncommitted (see TODO). Kept as the
> per-task detail record.

**Backlog #8 (numeric over-all invariant redesign) is DONE and committed (`d809a59`, branch
`numeric-conditions-effects`; whole numeric chain green, 0 sorries).** Implemented as design **B** (a sound
over-approximation), NOT the lock design in `NUMERIC_OVERALL_REDESIGN.md` — design **A** was reconsidered
and REJECTED as an unsound *under*-approximation for this forward-only unsolvability certifier (its
write-guard would reject valid interfering plans); that doc now carries a big DO-NOT-IMPLEMENT-A banner.
The static `n_inv_eq`/`n_inv_readonly`/`n_inv_init_sat` contract is gone; the over-all fragment is now
GENERAL (arbitrary while-active comparisons); the guard is discharged from validity's active clause at BOTH
`num_edge_2` (start) and the new `num_edge_3` (end) check, via bridge lemmas `starting_index_active_Suc` /
`ending_index_inv_sat` (`TA_Network/TP_NTA_Reduction_Numeric_Projection.thy`). Full detail is in the memory
`numeric-overall-redesign-decisions.md`. Side effect: `numeric_tp_nta_reduction_correctness` now has FEWER
assumptions + a broader fragment, so WP-A's interpretation is easier and more general.

**The core-rebase AND WP-A are now DONE & green (2026-07-09, UNCOMMITTED on disk).**
- **Core-rebase (gate) — done.** `ground_ast_problem_core` was given the body (all former
  `ground_ast_problem` body-lemmas + `goal_in_props`, which is `no_functions`-free, relocated into core);
  `ground_ast_problem = core + no_functions` keeps only the 3-lemma `no_functions` cluster
  (`no_functions_no_wf_func_assign`/`init_wf_fmla_atoms`/`init_in_props`). `Ground_PDDL_Problem_Reduction.thy`
  + `Ground_PDDL_Plan_Defs.thy:271` re-pointed to `context ground_ast_problem_core`; the two `init_in_props`
  uses in the reduction were dropped (goal⊆props ⇒ LHS empty via `goal_in_props`; ex-falso from `x∈{}`).
- **Leaf reconciled to design B.** `Ground_PDDL_Numeric_Problem_Defs.thy`: the 3 now-dead over-all
  assumptions (`n_inv_eq`/`n_inv_readonly`/`n_inv_init_sat`) were removed from `numeric_ground_ast_problem`
  (the abstract `numeric_tp_nta_reduction` dropped them in #8), stale design-A comment replaced.
- **WP-A — done.** New `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Correctness.thy` (registered
  in `ROOT`, fully_processed + consolidated, 0 errors/sorries): `sublocale nred: numeric_tp_nta_reduction`
  in the leaf (15 static assumptions discharged one-for-one) + hoisted plan-free `num_net_impl`/`num_a\<^sub>0`;
  a plan-carrying `locale numeric_valid_ground_plan` (twin of `valid_ground_plan`) that `sublocale ncorr:
  numeric_tp_nta_reduction_correctness`; and the Rung-4 lemmas
  `num_valid_ground_plan_imp_num_form_holds` (`\<exists>\<pi>. numeric_valid_ground_plan \<dots> \<pi> \<Longrightarrow>
  num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula`, over the NUMERIC net) + contrapositive
  `num_net_form_not_sat_imp_no_valid_ground_plan`.
- **DESIGN DEVIATION from NUMERIC_EXEC_PLAN.md WP-A (deliberate, sound):** the plan doc stated the
  hypothesis as `\<exists>\<pi>. numeric_plan_for_problem \<pi>`, but that (PRIMED) numeric-plan abbreviation is
  fixes-only / carries ONLY propositional validity — the numeric-net capstone genuinely needs `num_valid`
  (numeric plan validity). So the honest hypothesis is `\<exists>\<pi>. numeric_valid_ground_plan \<dots> \<pi>`, a plan
  predicate bundling propositional validity + `num_valid` + the WP-E plug `num_seq_in_bounds` (carried as an
  explicit, commented locale assumption — NOT discharged; reserved for David).

**WP-C/D underway (2026-07-10) — a big prerequisite was discovered + fixed first.** Starting WP-C surfaced
that the propositional EXECUTABLE + EXPORT layer (`Ground_PDDL_NTA_Reduction_Impl.thy`, imported by
`Check_Unsolvability.thy`) had been **committed-BROKEN since the FPS re-point** (WIP commit `31a9e17`, 90
errors) — latent because only the PROOF chain was ever reprocessed. Fixed (David: "repair, defer export
tail"): `Ground_PDDL_NTA_Reduction_Impl.thy` is now GREEN (net constructors + `*_refine` +
`model_checking_problem_refine`) — the action-schema TYPE change (`ast_action_schema` ->
`ast_temporal_action_schema`), `wf_problem` -> `wf_temporal_problem`. **ISOLATED for WP-D** (commented,
`text \<open>WP-D ISOLATION\<close>`): the code-gen typeclass block (`proper_interval`/`Abs_literal`/`derive`,
broken by the new `String.literal` repr), `check_ground_problem`(+`_return_iff`), `make_network_impl`
(+`check_and_make_network`+soundness), and the `value`/`export_code` tail — all need re-derivation against
the `ast_cont_*` namespace. Full detail in memory `numeric-exec-impl-layer-status.md`.
- **WP-C (numeric net + refinement) — DONE & green (2026-07-10)**: new
  `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Impl.thy` (in ROOT; fully_processed, 0 errors/
  sorries — the `consolidated` flag lags on these big nodes, see the memory). Executable `num_net_*'`
  constructors (augment the propositional `net_*'`) + numeric `*_refine` lemmas + the capstone
  `num_model_checking_problem_refine` (executable numeric net unreachable ==> no valid numeric plan, over
  the REAL `num_net_impl`). Load-bearing finding: the propositional `*_refine` lemmas are gated behind
  `no_functions` (in `ground_ast_problem`, not core) AND target the REFINED net, while the numeric net
  augments the RAW net — so the agent re-proved the propositional refine stack at RAW/`ndefs` level
  (~40 `ndefs_*` lemmas). CLEANUP flagged: a shared RAW-level refine stack in `ground_ast_problem_core`
  would dedup this (see memory `numeric-exec-impl-layer-status.md`).
- **`fluent_to_var` refactor — DONE & green (2026-07-10, backlog #1), UNCOMMITTED (on top of `fef6bc9`).**
  `fluent_to_var` is now a DEFINED constant off a new `fluent_to_name` parameter (exact mirror of
  `prop_to_var`/`prop_to_name`): `numeric_tp_nta_reduction_defs` fixes `fluent_to_name` + defines
  `fluent_to_var f = STR ''fluent_'' + fluent_to_name f`; `numeric_tp_nta_reduction` gains
  `fluent_names: unique_names fluent_to_name "set nfluents"` (the generic `type_naming`/`unique_names`
  helpers MOVED from `Model_Checking` down to `Defs`), so `fluent_to_var_inj`/`fluent_vars_fresh` are now
  LEMMAS. Ground: `fluent_to_name_spec = func.name`, inj from `wf_domain_signature`'s distinct functions.
  The `fluent_to_var` param is DROPPED from leaf/WP-A/WP-C; ONLY `fluent_lo`/`fluent_hi` (WP-E) remain
  parameters. 7 files (4 TA_Network + 3 Ground_PDDL). Full detail: memory `numeric-exec-ladder-design.md` #1.
- **RE-SEQUENCING DECISION (2026-07-10, David): WP-E (bound inference) now comes BEFORE WP-D.** WP-D is the
  executable export/assembly — it builds `num_net_bounds'` from `fluent_lo`/`fluent_hi` and needs the
  `num_seq_in_bounds` discharge to instantiate the numeric leaf on a *concrete* problem. Leaving those
  abstract (WP-A/WP-C carry them as a parameter/assumption) is fine for the *proof* chain but is useless
  for a *runnable* checker: the exported `check_and_make_numeric_network` must COMPUTE the bounds from `P`,
  not receive them as a locale parameter. So the boundedness plug must land first. **A WP-D start was
  attempted (2026-07-10) and rolled back to committed-green** on this decision; its design is recorded below
  under "WP-D (deferred behind WP-E)".
- **NEXT = WP-E** (boundedness: discharge `num_seq_in_bounds`, define concrete `fluent_lo`/`fluent_hi` as a
  function of `P`). The candidate is the standalone, untracked `Numeric_Bound_Inference/` (interval abstract
  interpretation, verified green per memory `numeric-bound-inference-draft`; own ROOT, not wired into
  `PDDL_TP_Reduction`). WP-E must expose the interface the rest keys off:
  `infer_fluent_bounds :: numeric_ground_problem \<Rightarrow> (func \<Rightarrow> int \<times> int) option` +
  `infer_fluent_bounds_sound` (`Some b \<Longrightarrow> num_seq_in_bounds` at `fluent_lo/hi := fst/snd \<circ> b`), then wire it
  into the numeric leaf so `fluent_lo`/`fluent_hi` are DEFINED from `P` and `num_seq_in_bounds` becomes a
  lemma (not a carried assumption). See `Numeric_Bound_Inference/BOUND_INFERENCE.md` +
  [NUMERIC_EXEC_PLAN.md](NUMERIC_EXEC_PLAN.md) §WP-E.
- **THEN WP-D (deferred behind WP-E)** = re-derive the isolated propositional export machinery + its NUMERIC
  twins (`check_numeric_ground_problem`, `num_make_network_impl`) + `export_code`. **David's WP-D scope
  decision (2026-07-10): do the ASSEMBLY** — `check_numeric_ground_problem` + `num_make_network_impl` +
  `check_and_make_numeric_network` (the soundness assembly) — **but DEFER the actual `export_code` /
  `String.literal` code-gen instances** if that block (the isolated `proper_interval`/`Abs_literal` typeclass
  instances) turns into a rabbit hole. Watch out: `check_numeric_ground_problem`'s executable admission check
  must turn the leaf's `\<forall>w. num_val_ok w \<longrightarrow> nexp_ok w e` / `comp_ok` universals into
  decidable STRUCTURAL sufficient conditions (exact-`NDiv`-only etc.), then prove structural
  \<Longrightarrow> the universal.
  - **WP-D scouting DONE (2026-07-10), recorded for resume.** The propositional wf half is the linchpin and
    is SOLVED: the temporal well-formedness check routes through the *continuous* checker at the translated
    problem — `check_wf_temporal_problem P \<equiv> check_wf_cont_problem (temporal_to_continuous_problem P)`, with
    `check_wf_temporal_problem P = Inr () \<longleftrightarrow> wf_ast_temporal_problem P` proved by
    `unfolding check_wf_temporal_problem_def check_wf_problem_return_iff` then
    `using wf_ast_cont_problem_equiv wf_ast_temporal_problem_def by simp` (interpret `ast_temporal_problem P`
    first; `check_wf_problem_return_iff` + `wf_ast_cont_problem_equiv` live in
    `Temporal_Planning.Temporal_PDDL_Checker_Explicit`, already imported). `check_ground_problem` = that wf
    check + the nine `ground_ast_problem_core` structural checks (`check_all_list`, now including the NEW
    `act_conds_no_args`) + `functions D = []` + `consts D = []` + init; accessors are
    `ast_temporal_action_schema_name` (not the old `ast_action_schema.name`) and `ast_problem.domain P` for
    `D`. `check_ground_problem_return_iff` unfolds `ground_ast_problem_def`/`_axioms_def`/
    `ground_ast_problem_core_def`/`_axioms_def` + `list_all_iff` + `return_iff` (NO `ground_ast_problem_defs_def`
    — that pure-import locale has no `_def`); the leftover `ast_temporal_problem P` conjunct needs a fact
    (`by unfold_locales` did NOT close it — supply via `interpret ast_temporal_problem P` and thread it).
- (**#9** — correct numeric mutex — moved to the TODO/BACKLOG section at the top of this file.)
Uncommitted docs on disk (ARCHITECTURE_pipeline.md, NUMERIC_PLAN.md, SEMANTICS_REPOINT_PLAN.md,
Numeric_Bound_Inference/, ...) predate #8 and were left untouched.

---

# ═ ARCHIVE — dated logs below (historical; superseded by the TODO + 2026-07-09 log above) ═

## CURRENT STATUS (2026-07-08) — historical (WP-B stages 1-2, core-rebase spec, WP-A blueprint, #8: all DONE above)

WP-B (the executable numeric layer) is underway, restructured as a **grounder-idiomatic locale ladder**
(design locked; see [NUMERIC_EXEC_PLAN.md](NUMERIC_EXEC_PLAN.md) §3 "Locale architecture — the ladder"):

- **Stage 1 DONE & green** — `Ground_PDDL_Problem_Defs.thy`: extracted `ground_ast_problem_core`
  (the numeric-INCLUSIVE base = the 9 shared admission assumptions); `ground_ast_problem` is now
  `core + no_functions` (classical leaf, **name unchanged**, so the whole propositional pipeline below
  it is untouched). fully_processed + consolidated, 0 errors. (In the jEdit buffer; not yet saved/committed.)
- **Stage 2 DONE & green** — `Ground_PDDL_Numeric_Problem_Defs.thy` (fully_processed + consolidated,
  0 errors, 0 sorries): the top-level translation funs `nexp_of_pddl`/`num_comps`/`upd_of_ne`; the
  `numeric_ground_ast_problem_defs` locale **DEFINING** the numeric data from P (`nfluents`/`n_pre`/
  `n_inv`/`upds`/`num_goal`/`num_init`, via the translation over the FPS snaps/goal/init); and the leaf
  `numeric_ground_ast_problem = numeric_ground_ast_problem_defs + ground_ast_problem_core + <numeric-fragment wf>`.
  Fluent identity `'n := func` (bare name-wrapper — exact mirror of props' `'proposition := predicate`).
  Only `fluent_lo`/`fluent_hi`/`fluent_to_var`/`const_to_int` stay parameters (the WP-E bounds plug + the
  two encoding maps). The draft's 2 antiquotation errors are gone. NB two constructor-clash gotchas fixed:
  `numeric_effect_op.Assign` (clashes with `form.Assign` from Approximation), and locale-local consts need
  `@{text …}` not `@{const …}` in doc comments.
- **Two findings baked into the design:** (a) the propositional snaps `at_start_spec`/`at_end_spec` carry
  the numerics (`pre_spec`/`adds_spec` only *project them out*) ⇒ `upds`/`n_pre` are definable with **no
  placeholder-lift**; on classical instances they are provably `[]` via `wf_ground_action_numeric_effects_Nil`.
  (b) `upds_no_cross_read` is the sequential=simultaneous side-condition (`is_upds_num_upd`) — keep it
  (mild, statically checkable, benchmark-trivial).
- **DONE (Stage 3a):** `const_to_int` defined (`= floor`), `const_to_int_of_int` now a lemma; leaf down
  to 3 params (`fluent_to_var`/`fluent_lo`/`fluent_hi`). Green, saved.
- **NEXT — the core-rebase (gate for WP-A), fully scoped 2026-07-09.** WP-A must interpret
  `numeric_tp_nta_reduction_correctness`, which reuses the propositional reduction `abstr_model_checking`
  (`Ground_PDDL_Problem_Reduction.thy`) + the plan-carrying `red_corr`/`valid_ground_plan`
  (`Ground_PDDL_Plan_Reduction.thy`/`Ground_PDDL_Plan_Defs.thy`) — but all of that is anchored in the
  CLASSICAL leaf `ground_ast_problem` (has `no_functions`), so the numeric leaf can't reuse it. Fix
  (chosen by David): re-base the propositional machinery onto `ground_ast_problem_core`. Precise spec:
    - `Ground_PDDL_Problem_Defs.thy`: give `ground_ast_problem_core` a `begin…end` body holding **all**
      current `ground_ast_problem`-body lemmas (809–1445, 43 of them) EXCEPT the `no_functions` cluster
      `{no_functions_no_wf_func_assign (1406), init_wf_fmla_atoms (1422), init_in_props (1431)}`, which
      stay in the `ground_ast_problem` body. (Checked: only those 3 touch `no_functions`; `goal_in_props`
      and the ~40 others are `no_functions`-free. `init_wf_fmla_atoms` genuinely needs it — numeric init
      carries `numericEqAtm` assignments, so "all init facts are `wf_fmla_atom`" is false with functions.)
    - `Ground_PDDL_Problem_Reduction.thy`: `context ground_ast_problem` → `context ground_ast_problem_core`.
      Its `abstr_model_checking` proof uses `init_in_props` at the `goal-⊆-init` and `action_consts` goals,
      but both reduce to `goal_in_props` (goal_spec ⊆ props ⇒ the diff is ∅) + ex-falso — so **drop the
      `using init_in_props`** there; that's the one proof repair.
    - `Ground_PDDL_Plan_Defs.thy`: `context ground_ast_problem` (271–376, 2 `no_functions`-free lemmas)
      → `context ground_ast_problem_core`.
    - Downstream is unaffected by name: `ground_ast_problem` still re-exports core's lemmas by inheritance,
      so `ground_ast_problem.X` / interpretations keep resolving. Re-verify the whole prop + numeric chain.
      Needs a jEdit restart (disk edits) — `jedit-down` before the bulk edit, `jedit-up` after.
- **THEN WP-A (blueprint ready).** New file `Ground_PDDL_Numeric_NTA_Reduction_Correctness.thy`: a numeric
  plan-carrying locale extending `numeric_ground_ast_problem` + a plan π + `num_seq_in_bounds` (WP-E plug),
  interpreting `numeric_tp_nta_reduction_correctness` (imports `TP_NTA_Reduction_Correctness_Numeric`) to
  get `num_valid_plan_imp_form_holds : num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula`; lift to a
  `ground_ast_problem`-level corollary (twin of `num_valid_ground_plan_imp_form_holds:37`).
- (`Ground_PDDL_Numeric_Problem_Defs` is already in `ROOT` under `PDDL_TP_Reduction`.)
- **SEPARATE deep task (backlog #8) — numeric over-all redesign, fully specified in
  [NUMERIC_OVERALL_REDESIGN.md](NUMERIC_OVERALL_REDESIGN.md).** David's design: drop the restrictive
  `n_inv_eq`/`n_inv_readonly`/`n_inv_init_sat` static contract; instead a per-fluent invariant lock
  (inc on edge_2/start, dec on edge_3/end) + a write-guard on the fluent-writing edges (`num_start_edge`/
  `num_end_edge`) forbidding writes to a locked (active-invariant) fluent, discharged from a numeric
  plan-validity non-interference condition — the numeric twin of the propositional "no delete while
  active" lock. Over-all value checked once at start (edge_2, last+write-free, sees settled valuation);
  no end re-check. A net-structure change to green `TA_Network`; NOT a WP-A→D blocker (benchmarks have no
  numeric over-all). The redesign doc has all anchors + the ordered plan.
- **Uncommitted, ON DISK & green:** the Stage-1 core split (`Ground_PDDL_Problem_Defs.thy`), the whole
  Stage-2 numeric file, + these doc updates. Nothing committed.

The 2026-07-06 status below (abstract numeric-net certificate proved & committed) still holds and is the
substrate this builds on.

## CURRENT STATUS (2026-07-06) — historical

The semantics/positivity re-point AND the numeric-net correctness ladder are **green and committed**;
the `TA_Network` reduction has been reorganized (committed `11707ff`). The whole proof-side numeric
reduction is done. **What remains is the EXECUTABLE numeric layer** — planned in
[NUMERIC_EXEC_PLAN.md](NUMERIC_EXEC_PLAN.md).

- **Proved & committed (abstract):** `num_valid_plan_imp_form_holds : num_net_impl.sem, num_a\<^sub>0 \<Turnstile>
  reach_formula` (`TA_Network/TP_NTA_Reduction_Correctness_Numeric.thy:2784`), hypothesis-free in
  `numeric_tp_nta_reduction_correctness`. The re-point (`Ground_PDDL_Problem_Defs` + `Plan_Defs`,
  `temp_plan_valid`) is green and committed. **0 sorries** across `TA_Network/*.thy`.
- **MISSING — Rung 4 over the numeric net.** The only Ground_PDDL numeric lemmas
  (`Ground_PDDL_Exec_Imp/Ground_PDDL_NTA_Reduction_Correctness.thy:37,44`) certify over the
  **propositional** `net_impl` via the additive-tracking shortcut
  (`TP_NTA_Reduction_Correctness.thy:664`) — *not* over `num_net_impl`. (NUMERIC_EXEC_PLAN WP-A.)
- **MISSING — the whole executable numeric net.** No `num_make_network_impl`, no numeric
  `check_ground_problem`, no numeric `export_code`; the only live export
  (`Check_Unsolvability.thy:1235`) is propositional. (NUMERIC_EXEC_PLAN WP-B/C/D.)
- **RESERVED FOR HUMAN DESIGN — boundedness.** Discharging `num_seq_in_bounds`
  (`TP_NTA_Reduction_Numeric_Model_Checking.thy:66`) + choosing `fluent_lo`/`fluent_hi` is
  soundness-critical and left to David (candidate: the untracked `Numeric_Bound_Inference/` interval
  AI). (NUMERIC_EXEC_PLAN WP-E — everything downstream is built against its interface.)
- **Uncommitted on disk:** the doc updates (`HANDOVER.md`, `NUMERIC_PLAN.md`,
  `ARCHITECTURE_dependencies.md`, `REFACTOR_SPEC.md`, `NUMERIC_EXEC_PLAN.md`), `Numeric_Bound_Inference/`,
  and a stray `Ground_PDDL_Exec_Imp/Ground_PDDL_Problem_Defs.thy` change **David did not review** — leave
  it, do not commit it.

Everything below is historical detail (re-point endgame, numeric run-lift closure) kept for reference;
it predates the 2026-07-05 reorg and refers to the OLD file names.

---

## FILE REORGANIZATION (2026-07-05) — DONE, green, committed (`11707ff`)

The `TA_Network` reduction was restructured (see `REFACTOR_SPEC.md`, `ARCHITECTURE_dependencies.md`).
Whole prop + numeric chain re-verified green (0 errors) after each seam. Summary:
- **Naming:** `Correctness` infix dropped from stage files; it survives only on the two capstones
  (`TP_NTA_Reduction_Correctness`, `TP_NTA_Reduction_Correctness_Numeric`). Stage files are
  `TP_NTA_Reduction_[Numeric_]<Stage>`.
- **Propositional kernel:** `Defs → Model_Checking → Utils → Prelims → Edges → Happenings →
  Properties → Steps → Correctness`. `Happenings` is now conditions + I/E/D rules ONLY;
  `Properties` (new) holds general automaton props + constraint-satisfaction lemmas + `steps_seq` +
  invariant-maintenance; `Utils` (new) holds generic pure-HOL + Munta-global helpers; the
  plan-stepping defs moved to `Steps`.
- **Numeric layer:** `Numeric_Defs` (split from Defs) → `Numeric_Model_Checking` (locale + `num_a0`)
  → `Numeric_Prelims` (was Tracking) → `Numeric_Edges` (was StepInfra) → `Numeric_Projection` →
  `Numeric_Steps` (was PhaseLifts) → `Correctness_Numeric` (was Plan + merged Happening). The
  numeric chain is a tightly-coupled lifting pipeline and was NOT re-layered like the kernel
  (its conditions/step-props are consumed by numeric Edges/Projection).
- **Folders:** kept flat in `TA_Network/` (single session). A `propositional/`+`numeric/` subfolder
  split was tried and reverted — one-session subdirs break jEdit's session association (would need two
  sessions); the `Numeric_` prefix already distinguishes the layers.
- The `<todo: fill this in>` in `…_Correctness` was filled (points to `num_valid_plan_imp_form_holds`
  in `TP_NTA_Reduction_Correctness_Numeric`).

Everything below this section predates the reorg and refers to the OLD file names.

---


Living inventory + ordered next-steps for the RE-POINT of the development onto Formal-PDDL-Semantics (FPS)
`Temporal_Planning` + the grounder's grounded/positive temporal locales (session `Grounding_Temporal_Common`,
a registered Isabelle component). Design docs: `SEMANTICS_REPOINT_PLAN.md`, `GROUNDING_PLAN.md`,
`ARCHITECTURE_pipeline.md`, `ARCHITECTURE_grounding.md`. The numeric run-lift is DORMANT (appendix below); it
resumes once this re-point lands green.

## HEADLINE STATUS (2026-07-02)
- **`Ground_PDDL_Problem_Defs.thy`: GREEN** — fully_processed + consolidated, 0 errors, 0 sorries. The whole
  positivity re-point is done and verified.
- **`Ground_PDDL_Plan_Defs.thy`: GREEN** — fully_processed + consolidated, 0 errors, **0 sorries**, 9283
  commands (2026-07-02). `temp_plan_valid` and `acts_non_intrf_simplified_of_fps` are done; the whole
  reduction (Problem_Defs + Plan_Defs) is now green. How the endgame closed:
    - **§A mutex** — reworked off the (now-false) snap injectivity onto POSITION-based non-interference:
      distinct ref-plan entries at the same htp occupy distinct positions in the snap list, so
      `list_pairwise acts_non_intrf` (from FPS `htps_acts_list_pairwise`, transferred to the project snaps
      via a position-preserving `list_all2` bridge + `acts_non_intrf_mono`) gives non-interference without
      needing `at_start_spec a \<noteq> at_start_spec b`. `acts_non_intrf_simplified_of_fps` rebuilt the same way
      (the unprovable `a_ne_b` hole and the phantom `acts_of_plan_snap_full_bridge'` are gone). New helpers:
      `acts_of_plan_at_simplified_fps_list_all2`, `all_htps_acts_non_intrf_simplified`,
      `list_pairwise_concat_{distinct_blocks,same_block}`, `at_{start,end}_block_of_ref_plan`,
      `acts_non_intrf_simplified_{distinct_entries,same_entry}`.
    - **§B durations** — `durations_match d (map snd dcs) ps as` derived from PLAN VALIDITY (FPS
      `wf_plan_action` gives only `0 \<le> d`), via new `durations_match_of_valid`: the At_Start/At_End snaps
      fold the `filter_time_spec`-routed duration atoms into their preconditions, and plan validity
      (`valid_temporal_state_seq_head_precond`) makes the valuation model them at value `d`, yielding
      `d = r`/`\<le>`/`\<ge>` per dc. Helper chain: `valid_temporal_state_seq_some_state_precond`,
      `htp_{start,end}_of_durative`, `inst_formula_{And,BigAnd_conjunct}`,
      `duration_matches_of_{inst_atom,snap_precond}`, `res_inst_snap_action_eq`, `at_{start,end}_snap_mem`.
- UNCOMMITTED. The pre-session green commit is intact in git; the mutex/durations rework is on disk, verified
  green in jEdit, not yet committed.
- Base heap: build `Temporal_Planning_Base` once, launch `isabelle jedit -d . -l Temporal_Planning_Base`
  (it now also preloads `Grounding_Temporal_Common.Temporal_PDDL_Normalization`).

## WHAT LANDED (all green)
### Step 1 — grounder wired into the base heap
`Grounding_Temporal_Common` added to `Temporal_Planning_Base`'s `sessions` + preloaded `theories` in `ROOT`
(mirrors how FPS `Temporal_Planning` is baked in, so jEdit resolves grounder imports fast); also added to
`PDDL_TP_Reduction`'s `sessions`. Base rebuilt green.

### Step 2 — positivity re-point (Problem_Defs, GREEN)
Project `is_pos_lit`/`is_pos_conj` RETIRED; the grounder's adopted (right-deep `is_pos_conj`; `is_pos_lit`
accepts `eqAtm`+-). Two design forks (decided):
- **eqAtm gap** -> grounder positivity + an explicit eqAtm-free SIDE ASSUMPTION, realised as the locale
  predicate `act_conds_no_args` (parallel to `act_pres_pos`) + locale assumption `conds_no_args` +
  `act_conds_no_args_spec`, threaded through the `*_snap_pre_pos_conj` and `*_no_params` lemmas. To be
  DISCHARGED once the grounder adds an eqAtm-elimination stage (recorded in the grounder repo's HANDOVER).
- **right-deep vs nested `BigAnd`** -> a nesting-tolerant, project-local
  `pos_conj_form form == (Atom \` atoms form = set (to_literals form))`;
  `ground_act_pres_pos (GroundAction pre eff) = pos_conj_form pre`.
New Problem_Defs lemmas (green): boundary bridge `pos_conj_form_inst_formula` / `pos_conj_form_map_atom`
(from `is_pos_conj` + `form_preds_no_args`), the `inst_formula`/`map_atom` preservation lemmas,
`pos_conj_form_BigAnd`, `inst_formula_BigAnd`, `pos_conj_form_predicates`, `wf_fmla_imp_wf_to_literals`,
locale `integer_duration_problem`. DELETED `wf_fmla_no_args` (false under the grounder's `is_pos_conj`);
`wf_fmla_atom_no_args` / `wf_ground_action_pres_in_props` re-proved from well-formedness alone.

### Step 3 — Plan_Defs Blocker A (duration-fold snap mismatch) RESOLVED
FPS `res_inst_snap_action` FOLDS duration constraints into the snap precondition as numeric atoms; the
project's `at_start_spec`/`at_end_spec` are at `dc=[]`, `dur=0` (durations carried by the network clock bounds
`lower_spec`/`upper_spec`, not the precondition). Fix (the `acts_of_plan_at_simplified` design): a simplified
plan-actions-at-t using the project snaps + snap bridges — FPS and project snaps have EQUAL `adds`/`dels`
and EQUAL `to_literals(precondition)` (the numeric duration atoms + the duration value drop under
`to_literals`). Re-pointed `at_start_snap_at_t` / `at_end_snap_at_t` / `acts_of_temporal_plan_at_no_args` /
`plan_happ_seq_alt` / `apply_effects_subseq` / mutex-membership onto it. Mirrors the green
`over_all_spec_eq_res_inst_temporal_inv`.

## temp_plan_valid endgame — RESOLVED (2026-07-02, green; see HEADLINE STATUS for how §A/§B closed)
The section below is the original problem analysis, kept as historical record — both (A) and (B) are DONE.
### (A) mutex — a semantic regression the re-point surfaced
The mutex proof relied on snap INJECTIVITY (`inj_on_at_start_spec`: distinct schema => distinct snap). Now
FALSE: FPS builds the snap via `tsubst (ActionHead n ps) []` = `subst_term (psubst (parameters h) [])`,
depending ONLY on the parameters, NEVER the schema name (and `acts_no_params` forces `ps=[]`) — so two
distinct schemas sharing a body give the SAME snap. **FIX: rework the mutex onto position-based
`list_pairwise acts_non_intrf (acts_of_plan_at_simplified t tp)`** (distinct plan entries => distinct
positions in `concat (map ..)`; `list_pairwise` gives non-interference even when two snaps are equal, which
validity precludes since `acts_non_intrf s s = False`). This also dissolves the `a_ne_b`/functional-bridge
need. Position/count-preserving transfer from FPS `htps_acts_list_pairwise` + a clean `acts_non_intrf_mono`,
using the green numeric-effect-trivial helpers below + the `to_literals`/`adds`/`dels` bridges. (Rejected
alternative: embed a name-guard atom in each snap — that changes snap semantics.)

Green helpers already added for this (numeric conjuncts of `acts_non_intrf` trivial, from the locale's
`no_functions`): `no_func_sig`, `no_wf_func_args`, `no_wf_numeric_effect`, `wf_effect_numeric_effects_Nil`,
`wf_ground_action_numeric_effects_Nil`, `wf_ground_action_lvalues_Nil`, `wf_ground_action_additive_lvalues_Nil`.

### (B) `durs_valid` — `durations_match` from PLAN VALIDITY (a ~100-line lemma)
FPS `wf_plan_action` gives only `d >= 0`. The FPS snap FOLDS `map (\<lambda>(x,y).(x, duration_constraint_as_formula y)) dcs`
(routed by `filter_time_spec ta`) into its precondition; `duration_constraint_as_formula (DurationConstraint EQ r)
= Atom (numericEqAtm DurationExpr r)` (LEQ/GEQ analogues); `inst_formula f d` sends `DurationExpr -> ConstantExpr d`.
So plan validity (`valuation M models precondition` of the At_Start/At_End snap) already verifies `d = r` / `<= r`
/ `>= r`. Derive `durations_match d (map snd dcs) ps as` from the satisfied snap duration atoms via the validity
hook `pres_sat` / `valid_temporal_state_seq_head_precond`. NOTE `dcs :: (temporal_annotation, term
duration_constraint) list`, so `durations_match d dcs` / `dc_list_lower dcs` / `dc_list_upper dcs` need
`map snd dcs`. Also: `resolve_action_wf` -> `wf_ast_temporal_domain.resolve_temporal_action_wf` (FPS
`Temporal_Instantiations.thy`); verify `temp_plan_valid`'s conclusion constants are the actual
`imp_defs.rat_impl.` names (`valid_plan` / `valid_state_sequence` / `valid_plan_def`).

## GOTCHAS / RULES
- Do NOT commit (per current instruction). Do NOT leave a `sorry`.
- Do NOT disturb the green `acts_of_plan_at_simplified` / snap-bridge machinery, the green helpers, or
  the green `Ground_PDDL_Problem_Defs.thy`.
- When a `.thy` is open in jEdit, mutate through the buffer (`mcp__isabelle__write_file`); declare green only
  when `fully_processed: true` AND `consolidated: true`.
- Stray `find_theorems "inst_of_plan_action"` in Plan_Defs (~line 1527, green territory) — cleanup candidate.

---

# APPENDIX (DORMANT) — numeric run-lift (closing `num_happening_steps_possible`)

> This appendix is the PRIOR handover for the (dormant) numeric run-lift. Its "Git state" and
> "ORDERED NEXT STEPS" below are STALE relative to the active re-point above; ignore until the re-point is
> green. The numeric run-lift resumes only after `temp_plan_valid` closes.

Living inventory + ordered next-steps for the numeric-fluent extension of the
"timed-automata network simulates a temporal plan" proof. The propositional case is fully
green; this work extends it to numeric fluents. The whole effort funnels into one lemma,
`num_happening_steps_possible` (`TA_Network/TP_NTA_Reduction_Correctness_Numeric_Happening.thy`).

> **Current active work is the semantics RE-POINT (P0), not this numeric run-lift.** The development
> is being re-pointed onto Formal-PDDL-Semantics' `Temporal_Planning`; see the **HANDOFF (2026-06-28)**
> at the top of [SEMANTICS_REPOINT_PLAN.md](SEMANTICS_REPOINT_PLAN.md). `Ground_PDDL_Plan_Defs.thy` is
> at 214 errors (down from ~616), all foundational/design-hard pieces green, remaining is a mechanical
> body grind + one `validity \<Rightarrow> durations_match` derivation. The numeric run-lift below resumes once the
> re-point lands green.

## File layout — numeric split (2026-06-25)

Layer B was carved out of `TP_NTA_Reduction_Correctness.thy` (now propositional-only, ~675 lines)
into six per-concern files in `TA_Network/`, all in locale `numeric_tp_nta_reduction_correctness`,
chained linearly (each imports the previous), all verifying green:
`…_Numeric_Tracking` (locale def + sublocales + tracking/encoding/invariants) →
`…_Numeric_StepInfra` (numeric net-step infra, non-interference, delay) →
`…_Numeric_Projection` (REL projection + run-lift engine + forward framework; holds `num_steps_seq`) →
`…_Numeric_PhaseLifts` (REL/RELC/RLP defs, per-edge step-lifts, per-phase lifts) →
`…_Numeric_Happening` (struct exports + `num_happening_steps_possible`) →
`…_Numeric_Plan` (pre/post bridges + `num_plan_steps_possible`).
Verify/launch commands below that name `TP_NTA_Reduction_Correctness.thy` now apply to the relevant
split file (the numeric run-lift is in `…_Numeric_Happening` / `…_Numeric_PhaseLifts`).

## Headline status (2026-06-25)

**The last `sorry` is CLOSED on disk — 0 sorries across `TA_Network/*.thy` +
`Temporal_Planning_Semantics/*.thy`.** The numeric simulation theorem is *logically* complete:
all five phase-lifts are assembled, the `happening_num_update` fold is threaded to
`snd (M (Suc i))`, and `num_happening_post` + `num_LvP` are concluded.

**NOT yet consolidation-verified.** This is the one open item. Sequence of events:
1. The closure was built in a single ~2.5h agent session (hundreds of `write_file` reprocesses).
2. That left jEdit's PIDE in a wedged state (`unprocessed: 1002, running: 3`, frozen 30+ min) — so
   the file never reached `fully_processed: true` + `consolidated: true`. Per project rule, a
   `0 errors` over an unprocessed tail is a FALSE green, so this is NOT declared done.
3. A full audit of the ~640-line new proof (lines 6222–7244) found **no diverging tactic** — every
   `auto`/`blast`/`simp` is over a fixed/finite goal, none over a recursive predicate
   (`graph_impl.steps`/`RLP`/`RELC`/`num_tracks`). Diagnosis: degraded prover state from the
   marathon session (possibly compounded by earlier failed `repl_connect` attempts leaving stray
   `ML_Repl`/`poly` helpers), NOT a logic bug.
4. jEdit was restarted clean (`jedit-down` then
   `jedit-up Temporal_Planning_Base TA_Network/TP_NTA_Reduction_Correctness.thy`). During the
   cold-start reprocess, **a command was observed to "take too long" in the editor** — likely one
   of the known slow combinator proofs (below), but possibly a genuine slow/divergent spot that only
   the clean prover surfaces. This is where work paused.

## Git state

- Last commit: `2bc7113` — *STEP 4 (partial): assembly framework + 3 of 5 phase-lifts*.
- **Uncommitted:** the `edge_phases` closure (edge_3 + edge_2 RLP phases) — `git status` shows
  `M TA_Network/TP_NTA_Reduction_Correctness.thy`. **Commit only after consolidated-green.**
- Commit map of the numeric run-lift (newest first):
  - `2bc7113` STEP 4 partial — assembly + instant/start/end phase-lifts
  - `01451d7` STEP 3 — per-phase struct-exports + `graph_impl_steps_nth_bounded`
  - `6015814` struct-export foundation (run-bound + target-pinning)
  - `c41934e` edge_2 phase-lift + `n_inv_init_sat` + `inv_sat_at_fold`
  - `9aa9e73` writing-edge kernels + start/end/instant phase-lifts
  - `98cb1e5` contract + foundation + lifting framework + edge_3 phase

## ORDERED NEXT STEPS

1. **Let the cold-start fully process.** `jedit-up` is done (port up); the file has ~14.5k commands
   and reprocesses the whole `TP_NTA_Reduction_*` chain on top of the `Temporal_Planning_Base` heap —
   expect several minutes. Verify with `mcp__isabelle__get_diagnostics`
   (`severity=error, scope=file, wait_until_processed=true`) + `get_sorry_positions`. Use `jedit-status`.
2. **Identify the "takes too long" command.** If processing stalls, the stuck command is at the
   `unprocessed` boundary inside `num_happening_steps_possible` (everything past its `qed` ~line 7244
   waits on it). Candidates are the known slow combinator proofs (5–11s, over `ext_seq`/`fold`, NOT
   recursive predicates — they DO terminate):
   - line ~6284 `by simp`; ~6306 `apply (subst hd_ext_seq, simp)+`; ~6798 `by (auto simp: <edge defs>)`;
     ~6806 `by simp`; phase-head `last` simps ~6882/6913.
   Tighten each with `(simp only: <named lemmas>)` / explicit `rule` chains (user wants FAST proofs —
   no eternal `auto`/`simp`). If a command genuinely diverges on the clean prover (still `running`
   after minutes), that is a real bug to fix at that line — but the audit predicts only slowness.
3. **Confirm green:** `fully_processed: true` AND `consolidated: true`, 0 errors, 0 sorries.
4. **Commit** (locally, no push) — message e.g. *"Numeric run-lift STEP 4: close edge_phases —
   numeric simulation theorem complete (0 sorries)"*. Then the end-to-end theorem
   `numeric_valid_temp_plan_imp_form_holds` is fully green.

## STRUCTURE OF THE CLOSED PROOF (for whoever resumes)

`num_happening_steps_possible` (~6222–7244) mirrors the propositional `happening_steps_possible`
(lines 6–199), but LIFTS the propositional happening run config-by-config instead of reconstructing it:
- **Setup (≤6247):** `cfg=(L,v,c)`, `ppd`/`tr`/`bnd`/`lvpr`, the propositional run `prun` +
  `ppost` from `happening_steps_possible`.
- **SEED + prop-run rebuild:** seed `RELC` from `tr`/`bnd`; rebuild the delay-headed prop run
  `prun_seq` by replaying the five propositional phase constructors from `pres'`.
- **Segment decomposition:** `SEG1..SEG4` / heads `h1..h5` peel each phase's prop sub-run.
- **Five phase-lifts** in `delay_and_apply` order edge_3 → instant → start → end → edge_2:
  - instant/start/end (RELC-style, fold GROWS): `num_{instant,start,end}_phase_lift` discharged by the
    GREEN `{instant,start}_phase_struct` / `end_phase_struct` (source-loc via target-pinning, length +
    `L!0` preserved along `seq_apply`, post-bound via `graph_impl_steps_nth_bounded`).
  - **edge_3 + edge_2 (RLP-style, fold FIXED) — the final `edge_phases` `have` (~6857):** these are
    no-FLUENT-write edges (they increment/decrement the propositional `prop_to_lock` over_all vars but
    not the numeric fluents, so the fold `w` is unchanged). Discharged via `num_edge_3_phase_lift`
    (`rlp3`, ~6606) / `num_edge_2_phase_lift` (`rlp5`, ~6730) with `P`/`Q` PINNED to the actual run
    position (`P j s ≡ s = run!j`), so the per-step source-loc/length/post-bound are all run-lookups
    (`graph_impl_steps_nth_bounded`, `RLP_edge_3_single`/`RLP_edge_2_single`). edge_3 source `running_loc`
    from `pres'` (`happening_pre_end_starts_dests(3)`) + a `loc_pres` propagation; edge_2 source
    `starting_loc` by target-pinning (only edge_2 targets `running_loc`).
- **Splice + delay-absorb:** `num_graph_impl.steps_append` chain (`by (simp only: append_Cons append_assoc)`)
  + `num_steps_delay_replace[OF _ _ num_no_urgent]`.
- **Conclude:** terminal fold `= snd (M (Suc i))` via `run_order_fold_eq_happening_num_update_set`;
  `num_happening_post` via `num_happening_postI` (prop half from `ppost` through the net_bounds
  projection); `num_LvP` via `num_Lv_conds_maintained`.

## KEY REUSABLE LEMMAS ADDED (all GREEN, committed)

- `graph_impl_steps_nth_bounded` — every non-head config of a prop run is `net_bounds`-bounded (from
  the internal step's `''bounded''` post-premise; `Simple_Network_Language.thy` step_int, lines 80–92).
- `graph_impl_steps_nth_step` — extract the step `xs!k → xs!Suc k` from a `graph_impl.steps` run.
- `step_u'_net_impl_post_bounded`; `prop_step_source_off`/`_ending` (+ `prop_step_edge_at_Sucn`) —
  target-based edge pinning.
- `start_phase_struct` / `end_phase_struct` / `instant_phase_struct` — discharge the RELC-style structs.
- (uncommitted, in the closure) `rlp3`/`rlp5`/`loc_pres`/`struct3` inside `edge_phases`.

## CONTRACT / SCOPE NOTES

- The supported numeric fragment is fixed by locale assumptions in `numeric_tp_nta_reduction`
  (`TP_NTA_Reduction_Defs.thy`): integer-encoding faithfulness (`snap_*_nexp_ok`/`comp_ok`,
  `num_init_val_ok`), reachability range invariant `num_seq_in_bounds`, and numeric over_all =
  equalities + read-only (`n_inv_eq`/`n_inv_readonly`/`n_inv_init_sat`). No Gigante benchmark has a
  numeric over_all, so this is not a practical restriction. See the auto-memory
  `numeric-run-lift-contract` for the htpl-accessor + M0-anchor gotchas.

## GOTCHAS

- `happening_num_update` is a `fold`; grow it via `subst happening_num_update_Cons` /
  `unfolding ..._def`+`fold_append`+`o_apply`, NEVER `simp add: ..._Cons`.
- No I/R REPL in this jEdit (the `iq` component isn't loaded); develop via `write_file` +
  `get_diagnostics`. Do not `repl_connect` (it spawns helpers that can degrade the prover).
- Restarting jEdit: `jedit-down`, then from the repo root
  `jedit-up Temporal_Planning_Base TA_Network/TP_NTA_Reduction_Correctness.thy`. The MCP bridge
  reconnects automatically on the next `mcp__isabelle__*` call (re-`authenticate`); `/mcp` only if not.
