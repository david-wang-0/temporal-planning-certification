# Numeric bound inference — what's done

The numeric NTA reduction encodes each numeric fluent as a **bounded-`int`** Munta network variable
(`fluent_lo f .. fluent_hi f`). Soundness of the numeric-net certificate depends on every reachable
fluent value staying inside its declared box — the locale assumption **`num_seq_in_bounds`**
(`TA_Network/TP_NTA_Reduction_Numeric_Model_Checking.thy:68`). "Numeric bound inference" is the machinery
that *supplies bounds* and *discharges that assumption* — statically, once per problem, so the exported
checker's conclusion carries **no per-plan boundedness obligation**.

## Soundness chain (the whole argument)

```
                COMPUTE SIDE (session Numeric_Bound_Inference = HOL-IMP, standalone)
                interval abstract interpretation over guarded actions
   infer_fluent_bounds P = Some b   ── infer_fluent_bounds_sound ─▶   reachable fluents ⊆ b   (finite int box)
                │  (box crosses to the reduction as plain data — HOL-IMP can't be imported: option-arity clash)
                ▼
                REDUCTION-NATIVE CERTIFICATE (TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy)
   is_gbound_inv'  ── is_gbound_inv'_imp_num_bound_inv ─▶  num_bound_inv  ── num_seq_in_bounds_derived ─▶  num_seq_in_bounds
   (eval-decidable       (interval-eval soundness)          (finite-int          (per-happening induction)      (locale
    interval check)                                          post-fixpoint)                                      assumption)
                │  numeric_tp_nta_reduction_bounds  (assumes num_bound_inv;  sublocale numeric_tp_nta_reduction_correctness)
                ▼
                GROUND INTEGRATION (Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Bounds.thy)
   numeric_ground_ast_problem_cert  (= numeric leaf + assumes nred.is_gbound_inv';  derives nred.num_bound_inv)
   ⟹ num_net_form_not_sat_imp_no_valid_ground_plan     (numeric-net capstone, bounds discharged)
                │
                ▼
                CERT-LEVEL EXECUTABLE SOUNDNESS (Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl.thy)
   check_and_make_numeric_network_and_plan_cert :
      exec numeric net unreachable  ⟹  NO valid numeric plan     (no residual num_seq_in_bounds)
```

Two representations of the "post-fixpoint bound" invariant, connected by evaluation:
- **`is_gbound_inv`** / **`is_gbound_inv'`** — the *eval-decidable* form: init in the box, and every update
  RHS, interval-evaluated over the guard-refined box, lands in bounds. `is_gbound_inv` lives on the compute
  side (`'n aenv` boxes); `is_gbound_inv'` is its self-contained twin on the reduction heap (finite-`int` box).
- **`num_bound_inv`** — the reduction-native *semantic* certificate the correctness proof actually consumes.

---

## 1. Compute side — standalone interval AI (`Numeric_Bound_Inference/`, session `= "HOL-IMP"`)

Threshold interval abstract interpretation. Cannot share the reduction heap (HOL-IMP's `Abs_Int0`
option-lattice arity clashes with the Munta/FPS tower), so it is a **separate session**; the inferred box
crosses to the reduction as plain `int` data. Termination proofs are **skipped by design**.

### 1a. Base abstract interpreter — `Numeric_Bound_Inference.thy`

| file:line | change | kind | purpose |
|---|---|---|---|
| `Numeric_Bound_Inference.thy:64` | `eval` | fun | concrete `'n nexp` evaluation over an `'n valuation` (`int`) |
| `:79` | `apply_upds` | def | concrete simultaneous update step of an `'n action` |
| `:99` | `\<gamma>_env` | abbreviation | concretization of an abstract env `'n aenv` to a valuation set |
| `:102` | `mono_gamma_env` | lemma | `\<gamma>_env` is monotone (`E1 \<le> E2 \<Longrightarrow> \<gamma>_env E1 \<subseteq> \<gamma>_env E2`) |
| `:119` | `aeval` | fun | **interval** evaluation of a nexp over an abstract env (`ivl`) |
| `:141` | `aeval_sound` | lemma | `v \<in> \<gamma>_env E \<Longrightarrow> eval v e \<in> \<gamma>_ivl (aeval E e)` (interval eval over-approximates) |
| `:174` | `astep_upds` | def | abstract update step (interval `apply_upds`) |
| `:177` | `astep_upds_sound` | lemma | one abstract update step over-approximates the concrete one |
| `:196` | `astep` | def | one abstract Kleene step over an action list (join of per-action steps) |
| `:231` | `astep_extensive` | lemma | `E \<le> astep acts E` |
| `:246`–`:312` | `mono_minus_ivl2`, `aeval_mono`, `astep_upds_mono`, `fold_sup_mono`, `astep_mono` | lemma | monotonicity of the abstract transformers (soundness of widening/narrowing) |
| `:324` | `is_bound_inv` | def | **post-fixpoint certificate**: `init_env v0 \<le> E \<and> astep acts E \<le> E` |
| `:327` | `bound_inv_sound` | theorem | `is_bound_inv v0 acts E \<Longrightarrow> reach v0 acts \<subseteq> \<gamma>_env E` (the master soundness) |
| `:360` | `init_env` | def | abstract env pinning each var to its initial point interval |
| `:363` | `widen_env` | def | pointwise interval widening of two envs |
| `:366` | `infer` | def | Kleene iteration with widening → `'n aenv option` |
| `:386` | `infer_sound` | theorem | `infer acts v0 = Some E \<Longrightarrow> is_bound_inv v0 acts E` |
| `:410` | `narrow_env` | def | pointwise interval narrowing |
| `:431`–`:443` | `narrow_post_fixpoint`, `narrow_sound` | lemma | narrowing preserves the post-fixpoint / soundness |
| `:457` | `infer_narrow` | def | infer-then-narrow (tighten the widened box) |
| `:464` | `infer_narrow_sound` | theorem | `infer_narrow acts v0 = Some E \<Longrightarrow> is_bound_inv v0 acts E` |
| `:503`–`:540` | `cnt_*` + `cnt_reachable_bounded` | def/lemma/theorem | worked example: bounded counter (`counter := 5`) |
| `:559`–`:611` | `inc_*` + `inc_reachable_nonneg` | def/lemma/theorem | worked example: unbounded monotone counter (box `[0, \<infinity>]`) |

### 1b. Threshold widening — `Numeric_Bound_Inference_Threshold.thy`

| file:line | change | kind | purpose |
|---|---|---|---|
| `Numeric_Bound_Inference_Threshold.thy:31` | `thr_below` / `thr_above` | def | snap an `eint` endpoint down/up to the nearest threshold |
| `:77` | `widen_thr_ivl` | lift_def | **threshold** interval widening (jump only to threshold constants, not `\<infinity>`) |
| `:130` | `widen_env_thr` | def | pointwise threshold widening of envs |
| `:136` | `infer_thr` | def | Kleene iteration with threshold widening |
| `:150` | `infer_thr_sound` | theorem | `infer_thr T acts v0 = Some E \<Longrightarrow> is_bound_inv v0 acts E` |
| `:168` | `nexp_consts` | fun | collect literal constants of a nexp (threshold candidates) |
| `:176` | `action_consts` | def | threshold constants of an action list |
| `:219`–`:240` | `pstep`, `sstep`, `sstep_le_iff_bound_inv` | def/lemma | gfp characterization: `sstep acts v0 E \<le> E \<longleftrightarrow> is_bound_inv v0 acts E` |
| `:275` | `infer_narrow_thr` | def | threshold widen + narrow |
| `:281` | `infer_narrow_thr_sound` | theorem | soundness of `infer_narrow_thr` |
| `:322`–`:421` | `cnt_*` / `ctr_*` + `infer_thr_cnt`, `ctr_reachable_nonneg` | def/lemma/theorem | worked examples recovering tight boxes via thresholds |

### 1c. Guarded actions — `Numeric_Bound_Inference_Guards.thy`

Adds guards (`'n gaction = 'n gcomp list × updates`); guards refine the box before the update.

| file:line | change | kind | purpose |
|---|---|---|---|
| `Numeric_Bound_Inference_Guards.thy:30` | `sat_gcomp` / `:35` `sat_guard` | fun/def | concrete guard satisfaction |
| `:56` | `ivl_le` / `:57` `ivl_ge` | def | half-bounded intervals `[-\<infinity>,k]` / `[k,\<infinity>]` |
| `:72` | `refine_gcomp` / `:77` `refine_guard` | fun/def | **tighten** the box by a guard (var-vs-const comparisons) |
| `:80`–`:117` | `refine_gcomp_sound`, `fold_refine_gcomp_sound`, `refine_guard_sound` | lemma | guard refinement is sound (keeps every satisfying valuation) |
| `:127` | `gastep_upds` / `:138` `gastep` | def | abstract step for a guarded action / action list |
| `:147` | `is_gbound_inv` | def | **post-fixpoint certificate for guarded actions** |
| `:150` | `gbound_inv_sound` | theorem | `is_gbound_inv v0 acts E \<Longrightarrow> greach v0 acts \<subseteq> \<gamma>_env E` |
| `:177` | `ginfer` | def | fixpoint inference over guarded actions |
| `:191` | `ginfer_sound` | theorem | `ginfer acts v0 = Some E \<Longrightarrow> greach \<subseteq> \<gamma>_env E` |
| `:202` | `ginfer_thr` | def | **threshold** inference over guarded actions (the compute-side entry point) |
| `:216` | `ginfer_thr_sound` | theorem | `ginfer_thr T acts v0 = Some E \<Longrightarrow> greach v0 (set acts) \<subseteq> \<gamma>_env E` |
| `:237`–`:271` | `gcomp_fluent`, `gcomp_const`, `guard_consts(_on)`, `signed_offset`, `landing_cs`, `nexp_thr_consts`, `gaction_thr` | fun/def | threshold-constant extraction (guard bounds + update "landing" values) |
| `:278` | `thr_set` | def | the full threshold set (init values + guard + landing constants) fed to `ginfer_thr` |
| `:295`–`:327` | `ctr_*` + `ctr_reachable_bounded`, `value` demos | def/lemma/theorem/value | worked example: guarded counter `[0,1]` |

### 1d. Finite-box extraction (`\<infinity> \<Rightarrow> reject`) — `Numeric_Bound_Inference_Extract.thy`

The reduction needs **finite** `int` bounds; a genuinely unbounded fluent must be rejected.

| file:line | change | kind | purpose |
|---|---|---|---|
| `Numeric_Bound_Inference_Extract.thy:28` | `bounds_rep` | def | rep-level extractor: `(Fin i, Fin j), i\<le>j \<mapsto> Some (i,j)`, else `None` |
| `:37` | `ivl_bounds` | lift_def | `ivl \<Rightarrow> (int \<times> int) option` (finite endpoints or `None`) |
| `:40` | `finite_ivl` | def | interval has finite endpoints |
| `:49` | `ivl_bounds_gamma` | lemma | `ivl_bounds iv = Some (lo,hi) \<Longrightarrow> \<gamma>_ivl iv = {lo..hi}` |
| `:58` | `extract_box` | def | extract a finite box for a fluent list, or `None` if any is infinite |
| `:62` | **`infer_fluent_bounds`** | def | **the interface**: `ginfer_thr` box → finite `int` box; `None` = "bound inference failed" |
| `:70` | **`infer_fluent_bounds_sound`** | theorem | `infer_fluent_bounds T fs acts v0 = Some b \<Longrightarrow> reachable fluents ⊆ b` (per tracked fluent) |
| `:95` | `infer_fluent_bounds_greach_subset` | corollary | `\<gamma>_env`-level restatement (whole reachable set ⊆ box) |
| `:104`–`:138` | `ivl_bounds_num_ivl`, `finite_ivl_num_ivl`, `ivl_bounds_top`, `not_finite_ivl_top`, `value` demos | lemma/value | sanity + demos: guarded counter → `Some (0,1)`; unguarded increment → `None` |

---

## 2. Reduction-native certificate + bridge — `TA_Network/TP_NTA_Reduction_Numeric_Bounds.thy`

Everything the correctness proof consumes, on the reduction heap (finite `int`). Two halves: (A) the
semantic certificate `num_bound_inv` and the bridge to `num_seq_in_bounds`; (B) the eval-decidable
interval check `is_gbound_inv'` and its soundness `is_gbound_inv'_imp_num_bound_inv`.

| file:line | change | kind | purpose |
|---|---|---|---|
| `TP_NTA_Reduction_Numeric_Bounds.thy:18` | `all_snaps` | def | the relaxed snap set (start ∪ end snaps of all actions) the cert quantifies over |
| `:27` | **`num_bound_inv`** | def | reduction-native finite-`int` certificate: init in box **and** every relaxed snap update RHS lands in `[fluent_lo f, fluent_hi f]` on in-bounds guard-satisfying valuations |
| `:44`/`:50`/`:58` | `num_bound_inv_initD` / `_stepD` / `_I` | lemma | intro/dest rules for the bundled certificate (avoid `unfolding` + `blast` at call sites) |
| `:75` | **`numeric_tp_nta_reduction_bounds`** | locale | the discharge locale: assumes the checkable `num_bound_inv` **instead of** `num_seq_in_bounds` |
| `:122`–`:224` | `happ_at_index_decomp_bnd`, `happening_subseteq_all_snaps`, `happening_finite_bnd`, `upds_functional_set_bnd`, `happening_upds_functional_bnd`, `num_mutex_valid_plan_bnd`, `happening_num_noninterfere_bnd` | lemma | S-property re-exports (proved from `num_valid` + static wf only, no reachability invariant) |
| `:285` | `sat_comp_unchanged_by_write` | lemma | guard persistence under a non-interfering write |
| `:308` | **`happening_preserves_fib`** | lemma | KERNEL: one happening preserves `fluent_in_bounds` (given `num_bound_inv`) |
| `:407`–`:419` | `rat_impl_*_eq_bnd` | lemma | namespace bridges (`rat_impl` ↔ `planning_sem` on `plan_happ_seq`/`htps`/`htpl`/`time_index`/`happ_at`) |
| `:427` | **`num_seq_in_bounds_derived`** | lemma | THE BRIDGE: `num_bound_inv \<Longrightarrow> num_seq_in_bounds` (per-happening induction on `i`, via the kernel) |
| `:485` | `sublocale numeric_tp_nta_reduction_correctness` | sublocale | re-derive the whole numeric-net capstone from the certificate (`_correctness` untouched) |
| `:512` | `map_ibnd2` | def | lift a binary `int\<times>int` op through `option` (interval eval plumbing) |
| `:516` | **`aeval`** | fun | interval evaluation of a reduction `('n,'r) nexp` in the `const_to_int` encoding (`NDiv \<mapsto> None`, fail-closed) |
| `:532` | `refine_comp` / `:541` `refine_box` | fun/def | tighten the box by var-vs-const numeric preconditions |
| `:544` | `box` | def | the declared box `\<lambda>f. (fluent_lo f, fluent_hi f)` |
| `:549` | **`is_gbound_inv'`** | def | the **eval-decidable certificate**: init in box, and every relaxed snap update RHS `aeval`'d over the guard-refined box lands in `[fluent_lo f, fluent_hi f]` |
| `:559`–`:596` | `const_to_int_round_trip`, `const_to_int_add`/`_diff`/`_mult`/`_mono` | lemma | `const_to_int` is a ring hom / monotone on integers (interval-eval algebra) |
| `:611`/`:630` | `mult_between`, `mult_in_corners` | lemma | interval multiplication lands between the corner products |
| `:656` | `Ints_div_exact_bnd` | lemma | exact integer division stays integer-valued |
| `:672`/`:718` | `nexp_ok_eval_bnd`, `nexp_ok_fluents_bnd` | lemma | an `nexp_ok` expression evaluates to a defined integer / reads only declared fluents |
| `:728` | **`aeval_sound`** | lemma | the interval eval over-approximates the concrete `eval_nexp` on in-box valuations |
| `:830`/`:839`/`:975` | `in_refine_box`, `refine_comp_pres`, `refine_box_fold_pres` | def/lemma | the guard-refinement fold preserves the in-box invariant |
| `:995` | **`refine_box_sound`** | lemma | an in-box valuation satisfying the guards inhabits the guard-refined box |
| `:1020` | **`is_gbound_inv'_imp_num_bound_inv`** | theorem | `is_gbound_inv' \<Longrightarrow> num_bound_inv` (eval cert ⟹ semantic cert) |

---

## 3. Supporting boundedness predicates + encoding parameters

The predicates the certificate is stated against, and the encoding maps.

| file:line | change | kind | purpose |
|---|---|---|---|
| `TP_NTA_Reduction_Numeric_Defs.thy:39–41` | `fluent_lo` / `fluent_hi` / `const_to_int` | locale fixes | per-fluent `int` bounds + the `'r \<Rightarrow> int` encoding map (`numeric_tp_nta_reduction_defs`) |
| `TP_NTA_Reduction_Numeric_Defs.thy:98` | `num_val_ok` | def | valuation is integer-valued on all declared fluents |
| `:101` | `fluent_in_bounds` | def | valuation is integer-valued **and in `[lo,hi]`** on all declared fluents |
| `:106` | `fluent_in_bounds_imp_num_val_ok` | lemma | in-bounds ⟹ integer-OK |
| `:244` | `const_to_int_of_int` | locale assm | `const_to_int (of_int m) = m` (round-trip; a base-locale assumption, discharged at ground by `= floor`) |
| `TP_NTA_Reduction_Numeric_Model_Checking.thy:68` | **`num_seq_in_bounds`** | locale assm | THE assumption being discharged: along every valid numeric state sequence each fluent stays in `[lo,hi]` |

---

## 4. Ground integration — `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Bounds.thy`

Discharge `num_seq_in_bounds` at the *ground* problem from the static `is_gbound_inv'` cert; the ground
plan predicate no longer bundles a per-plan boundedness obligation.

| file:line | change | kind | purpose |
|---|---|---|---|
| `Ground_PDDL_Numeric_NTA_Reduction_Bounds.thy:31` | **`numeric_ground_ast_problem_cert`** | locale | plan-free: `numeric_ground_ast_problem` + `assumes nred.is_gbound_inv'` |
| `:41` | `num_bound_inv` | lemma | derives `nred.num_bound_inv` from the cert (via `nred.is_gbound_inv'_imp_num_bound_inv`) |
| `:55` | **`numeric_valid_ground_plan_cert`** | locale | plan-carrying twin of `numeric_valid_ground_plan`, **without** the `num_seq_in_bounds` assumption |
| `:78` | `sublocale nbnd: numeric_tp_nta_reduction_bounds` | sublocale | interpret the discharge locale (3 goals: `num_valid` / `num_bound_inv` / `num_goal_comp_ok`) |
| `:89` | `num_valid_plan_imp_form_holds` | lemmas | re-export the abstract capstone at the ground interpretation |
| `:103` | `num_valid_ground_plan_imp_num_form_holds` | lemma | `\<exists>\<pi>. numeric_valid_ground_plan_cert \<dots> \<Longrightarrow> num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula` |
| `:115` | **`num_net_form_not_sat_imp_no_valid_ground_plan`** | corollary | numeric-net capstone (bounds discharged): net unreachable ⟹ `\<not>\<exists>\<pi>. numeric_valid_ground_plan_cert` |

---

## 5. Cert-level executable soundness — `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl.thy`

Compose the WP-C executable-net refinement with the §4 cert capstone: the **executable** numeric-net
result, with **no per-plan bounds** in the conclusion. (Imports the WP-C exec-net theory + §4.)

| file:line | change | kind | purpose |
|---|---|---|---|
| `Ground_PDDL_Numeric_NTA_Reduction_Cert_Impl.thy:34` | **`num_model_checking_problem_refine_cert`** | lemma | executable numeric net unreachable ⟹ `\<not>\<exists>\<pi>. numeric_valid_ground_plan_cert` (fires the §4 capstone) |
| `:57` | **`check_and_make_numeric_network_and_plan_cert`** | lemma | given the check result + `numeric_ground_ast_problem_cert` (leaf + `is_gbound_inv'`), a Munta-unreachable exec net ⟹ **no valid numeric plan** — no residual `num_seq_in_bounds` |

---

## 6. Status, commits, what's left

- **Compute side + reduction-native certificate: COMMITTED & green** (`ea1e9e1` soundness backbone,
  `aeaba18` "WP-E numeric bound inference COMPLETE", 0 sorries). Sessions: `Numeric_Bound_Inference = "HOL-IMP"`
  and `TP_NTA_Reduction` in the main `ROOT`.
- **Ground integration (§4): COMMITTED & green** (`cf3c0f0`).
- **Cert-level executable soundness (§5): green, UNCOMMITTED** (2026-07-12).
- **Locked facts (don't re-litigate):** HOL-IMP is **not** importable into the reduction (`option`-arity
  clash) — the inferred box crosses as data; `int` is **forced** by Munta (`Simple_Network_Impl`); the
  compute-side **termination proof is skipped by design**; `NDiv` is fail-closed (`aeval \<mapsto> None`).

### Not yet done — the fully runnable tail

`is_gbound_inv'` is currently either an eval target (reduction side) or a **locale assumption**
(`numeric_ground_ast_problem_cert`). To make the pipeline *runnable* end-to-end:

1. an **executable `is_gbound_inv'`** (code-generatable over the ground reduction data), and
2. the **`infer_fluent_bounds` cross-session ML bridge** (compute `fluent_lo/hi` from `P`, eval-check the
   cert) — needed because the compute side (HOL-IMP) and the reduction cannot be one theory;

so that `check_and_make_numeric_network(_cert)` **discharges** the `numeric_ground_ast_problem_cert`
hypothesis by evaluation instead of assuming it. Then `export_code` (deferring the
`proper_interval`/`Abs_literal` `String.literal` code-gen instances).

*Line anchors current as of 2026-07-12; re-anchor if files move.*

## 7. SML bound-inference glue — built & running (2026-07-13, UNCOMMITTED)

Both halves of the ML bridge from §6.2 are now emitted and **linked into one MLton binary**, with a
standalone smoke test passing.

**Two Isabelle code exports (they cannot share a heap):**

- **Compute side** — `code/Numeric_Bound_Inference.ML` (`structure NumericBoundInference`), from session
  `Numeric_Bound_Inference = "HOL-IMP"` (`isabelle build -e`). Entry points `infer_fluent_bounds` /
  `thr_set` are polymorphic in the fluent type. *Post-gen fixup:* the `'a equal` / `'a enum` / `'a finite`
  dictionary records are emitted with an **opaque** signature; widened by hand to expose them (the struct
  body already defines them transparently) so SML can build a dict. `String.literal` has no Isabelle `enum`
  instance, so the compute side is **only** usable via a runtime-list-backed dict — fabricated in SML,
  correct because the fixpoint stability check only inspects fluents in the carrier list. *(Fold this
  widening into a `Code_Compile` sed step when productionizing.)*
- **Reduction side** — `code/Numeric_Projection.ML` (`structure NumericProjection`), from theory
  `Ground_PDDL_Exec_Imp/Ground_PDDL_Numeric_Code_Export.thy`. Exports `numeric_draft_actions P` (the
  INT-ified `(fluents, snaps, init)` projection, fluent names as SML `string`), `check_gbounds_opt P B`
  (the name-keyed trusted gate = `is_gbound_inv_exec`, **no** net builder so it code-generates), and the
  `g_int` / `e_int` constructors. Emitted via the `export_code … file "../code/Numeric_Projection.ML"`
  side-effect during jEdit processing (the network builder still can't code-gen — the deferred
  `finite'` / `String.literal` block — so a full session build is not yet possible).

**Glue** — `ML/plan_cert/src/numeric_glue/` : `numeric_bound_glue.sml` (`structure NumericBoundGlue`) maps
`NumericProjection`'s `g_int`/`e_int` → `NumericBoundInference`'s `gcomp`/`nexp` (strict comparisons
collapse to non-strict on integers), bridges the two distinct `int` datatypes through `IntInf.int`,
fabricates the fluent-list dicts, and returns a box shaped for `check_gbounds_opt`. `numeric_code.mlb`
isolates the two generated modules (`local … in structure … end`, hiding their overlapping top-level
helpers). The projection is **untrusted** — a wrong box is rejected by `check_gbounds_opt`, never unsound.

**Smoke test** (`glue_demo.sml`, `mlton … glue_demo.mlb`): the guarded counter
(`counter := counter+1` guarded by `counter ≤ 0`, init 0) infers `counter ∈ [0, 1]` — matching the
Isabelle `value` demo — and the unguarded counter is correctly rejected (`NONE`, out of scope).

**Co-linked into `plan_cert`.** All three Isabelle code exports — `Converter`
(`ML/Check_Unsolvability.ML`), `NumericBoundInference`, `NumericProjection` — now link into the one
`plan_cert` binary (`numeric_glue/numeric_code.mlb` isolates the two numeric modules' overlapping
top-level helpers).  `plan_cert -certify numeric-selftest` runs the counter demo in-binary and prints
`counter in [0,1]`, retiring the "two exports in one binary" risk (no basic-type clash).

## 8. Part B — external tchecker/muntac certification (2026-07-13, UNCOMMITTED)

`ML/plan_cert/src/tchecker_certify.sml` (`structure TCheckerCertify`) drives the repo's `run.sh`
recipe from SML, replacing the non-terminating in-process MLunta path:
`python3 -m convert_models.convert` (muntax→tck) → `tck-reach -a covreach -C graph -s dfs` (tck→dot) →
`python3 -m convert_models.convert_certificate -m …` (dot→cert) → `muntac -m -r -c -i 3|4`, parsing
stdout for `Certificate was accepted`/`rejected`.  Wired as `plan_cert -certify tchecker` (writes muntax +
renaming, then certifies); tool paths are env-overridable (`TCHECKER_PKG_ROOT`, `TCK_REACH_BIN`,
`MUNTAC_BIN`, repo-relative defaults).  **Verified end-to-end** on a hyphen-free blocks instance →
`Verdict: accepted`.

**Identifier sanitisation (fixed).** `tck-reach`'s grammar rejects `-` in identifiers, but muntax
variable names carry PDDL predicate hyphens verbatim (`lock_on-table_a`), and the cert conversion matches
variables *by name* — so sanitising only `convert.py` would desync it.  `TCheckerCertify.sanitize_file`
rewrites the muntax in place, replacing `-` with `_` only where it sits between two identifier characters
(operators and negative numbers untouched), *before* the renaming is derived from it — so muntax +
renaming + tck stay name-consistent.  Verified: the unmodified hyphenated `ground-blocks` problem
(`on-table`, `arm-empty`) now certifies end-to-end → `Verdict: accepted`.

**Still open for a full `plan_cert -numeric` mode:** a `Converter → NumericProjection` AST coercion
(`PddlParser.get_prob` yields a `Converter`-typed problem; same Isabelle AST, two distinct SML types — the
clean "emit the numeric fns into `Converter`" route is blocked by the broken `Check_Unsolvability`), and
the numeric muntax **net** builder code-gen (the deferred `finite'` / `String.literal` block).
