# HANDOVER — temporal-planning-certification

Living inventory + handover for this repository: per-session contents, the `sorry` inventory,
environment/gotchas, and the ordered next-steps list. Design docs:
[ARCHITECTURE_pipeline.md](ARCHITECTURE_pipeline.md),
[ARCHITECTURE_grounding.md](ARCHITECTURE_grounding.md); plans:
[GROUNDING_PLAN.md](GROUNDING_PLAN.md), [NUMERIC_PLAN.md](NUMERIC_PLAN.md). The ROOT files are
authoritative. Last updated 2026-06-23.

## Session handover — 2026-06-23 (cont.: run-lift ENGINE started -- projection relocated + urgency-transfer + delay-lift green; single-step "network combination" validated with the user; the run-lift core `num_happening_steps_possible` is still the one `sorry`, now at :2218)

File PIDE-verified **0 err / 1 sorry / 2333 cmds, fully_processed + consolidated**. Built the first
engine pieces for the run-lift, under the user's framing: lifting the propositional happening run to a
numeric run **is** a run-level *"combine two nets that share locations/clocks but have disjoint
guards/updates"* theorem.

**DESIGN validated with the user (the combination-theorem framing).** The numeric net = the prop net
with each edge `augment_edge`'d (same `l,l',g,r,a`; guard `b -> bexp.and b gn`; updates `f -> f@fn`;
`gn`/`fn` over the FRESH fluent vars, disjoint from prop vars by `fluent_vars_fresh`). Forward
composition is sound and is ALREADY the single-step lemma `num_int_step_lift` (:1592) + keystone
`num_step_int_lift` (:1492): a prop internal step + a `num_data` provider -> the augmented-net step with
`v \<subseteq>\<^sub>m vn`. The store split `v = (v|`pv) ++ (v|`nv)` is the projection infra
(`store_decomp`/`prop_proj_bounded`). TWO caveats recorded: (a) the augmented net admits STRICTLY FEWER
transitions (the conjoined guard `bexp.and b gn` can BLOCK), so the lift stays conditional on
`num_valid_state_sequence` (which supplies `sat_comps (snd (M i)) (n_pre s)` to discharge `gn`) -- there
is NO free structural simulation "prop run => numeric run". (b) The combination theorem organises the
Munta plumbing but does NOT discharge the three abstract obligations (the fold/threading, intra-happening
non-interference, the \<section>B bounds) -- that is where the real remaining work lives.

**Mutex clarification (user Q -- "is numeric mutex a counter, like propositional?"):** NO. Propositional
mutex IS counter-based -- per-proposition lock counters `prop_to_lock p` (bounded `[0, length actions]`,
`Defs:365`) + global `acts_active`, incremented/read on start/end edges (`inc_prop_lock_ab`/
`is_prop_lock_ab`) -- because a lock is held across an action's whole [start,end) DURATION (stateful,
spans happenings). The numeric augmentation adds ONLY fluent value-vars
(`num_all_vars = all_vars @ num_fluent_vars`); `num_mutex_snap_action` NEVER appears in the net. Numeric
interference is enforced ABSTRACTLY by \<epsilon>-separation (`num_mutex_valid_plan`, `Temporal_Plans:1529`):
interfering numeric snaps are forced \<ge>\<epsilon> apart so they never co-occur in a happening => the
happening's snaps commute => `happening_num_update_set` is order-independent. Numeric interference is only
intra-happening (instantaneous), already excluded by \<epsilon>-sep, so no counter is needed. (This is
exactly the non-interference `sat_comps_happening_num_update_set` :1835 exploits.)

**LANDED green this session:**
- **Projection infra RELOCATED** (`dom_map_of_num_net_bounds`, `fluent_var_notin_net_bounds`,
  `map_of_num_net_bounds_eq_on_props`, `prop_proj_bounded`, `store_decomp`) from file END to a new
  subsection BEFORE the run-lift (:2022 area) -- the prerequisite move (the lift's proof needs them and
  Isabelle is linear). Pure relocation; nothing between depended on them (verified via grep).
- **`num_urgent_eq`** (:2117) -- `urgent (fst (snd num_net_impl.sem) ! p) = urgent (fst (snd net_impl.sem) ! p)`
  for `p < Suc (length actions)`. `augment_edge` leaves the urgent component untouched; case-split `p`,
  both sides compute to `{init_loc,goal_loc}` / `{starting_loc,ending_loc}` (mirrors `num_no_urgent`).
- **`num_step_t_lift`** (:2155) -- lift a prop `Del` step to the numeric net (same delay, store untouched).
  Invert the prop Del (`step_u_elims(1)`), transfer urgency via `num_urgent_eq` + the lengths, re-issue a
  numeric `step_t` (invariants via `num_no_invs`, caller supplies `bounded num_net_bounds vn`). This is the
  DELAY HALF of the single-step `step_u'` combination.
- **`num_int_step_lift` STRENGTHENED** (:1592) -- the conclusion now ALSO exposes
  `bounded (map_of num_net_bounds) vn'` (was dropped internally as `BND`; the run-lift must thread it
  config-by-config). Only referenced in comments, so safe; re-proved green by adding `BND` to the last `using`.

**NEXT (ordered) -- the remaining run-lift build:**
1. **`net_step_internal`** (a non-`Del` step of `net_impl.sem` is `Internal`): every edge uses `Sil ''''`
   (8 occ, 0 `In`/`Out` in `Defs`) and `net_broadcast = []`, so `step_bin`/`step_broad` are vacuous. Needs a
   `net_trans_Sil` helper (every edge of `trans (automaton_of (net_automata ! p))` has a `Sil` label):
   `main_auto_trans` (`Edges:1441`) computes `p=0`; a PROP `action_auto_trans` does NOT exist as a named
   lemma (only `num_action_auto_trans` :1375), so compute it (mirror the numeric one). This unblocks using
   the `Internal`-keyed `num_int_step_lift` on an INVERTED run step.
2. **`num_step_u'_lift`** (single `step_u'` lift = delay + internal): invert the prop `step_u'`
   (`step_u'_elims` -> a `Del` then a non-`Del`; the Del gives `Lm=L, sm=vp, um = c \<oplus> t`; the non-Del is
   `Internal` by (1)), then `num_step_t_lift` for the Del + `num_int_step_lift` for the Internal, recombined
   via `step_u'.intros`. Threads `vp \<subseteq>\<^sub>m vn`, `num_tracks`, `bounded`.
3. **`num_run_lift`** (the generic engine): induct over the prop run list `cp # delay_and_apply i cp`,
   applying `num_step_u'_lift` per step, threading an aligned tracking-witness list `ws` (`ws ! 0 = snd (M i)`,
   advanced per step). Pure list-induction plumbing once (2) exists -- THIS is the reusable "combination
   theorem at run level".
4. **Instantiate in `num_happening_steps_possible`** (:2193; the `sorry` :2218) -- the DEEP CORE: (i) the
   per-step `num_data` discharge picks `num_data_upd_edge` (start/end -> snap `s`, advancing `ws` by
   `apply_upds (set (upds s))`) vs `num_data_no_write_edge` (edge_2/edge_3/loop) by the source loc `L ! p`;
   intra-happening guards reduce to `snd (M i)` via `sat_comps_happening_num_update_set`. (ii) prove
   `last ws = snd (M (Suc i))` -- i.e. the fired snaps along the run = `S = happ_at B (t i)` and the
   run-order left-fold of `apply_upds` = the set-fold `happening_num_update_set S` (order-independence,
   Layer A) = `snd (M (Suc i))` (from `num_valid_state_sequence`). (ii) is the snap-identification + fold
   connection -- the genuinely hard, likely multi-session part. \<section>B `INV` bounds + discreteness stay hypothesized.

**Gotchas (this session):** the new step lemmas carry the benign `step_u`/`step_sn` "Ambiguous input" parse
warnings (same class as elsewhere; 41 warns total). The `(fst o snd)` form in `length_net_impl`/
`length_num_net_impl` vs `fst (snd \<dots>)` is bridged by `simp add: comp_def`. The stray
`TP_NTA_Reduction_Correctness.thy~` editor backup (~109 KB, not in any ROOT) is still present -- delete in
the cleanup pass.

## Session handover — 2026-06-23 (run-lifting scaffold: prop + numeric transfers + `num_plan_steps_possible` green; the run-lift core `num_happening_steps_possible` is the one isolated `sorry`)

Built the **outer run-lifting structure** in `TA_Network/TP_NTA_Reduction_Correctness.thy` (appended after
`num_no_urgent`; file ~2094 cmds, PIDE-verified **0 err / 1 sorry**, fully_processed). The entire numeric
**plan** run is now green; the single remaining obligation is the per-happening run-lift core.

**DESIGN locked in — the numeric run is EXISTENTIAL and SHADOWS the propositional run** (same
locations/clocks, store extended with tracked fluent vars), built by lifting each prop step via the keystone
bricks. KEY REALIZATION: the `num_*` twins are stated on a SINGLE combined store `vn` that does double duty --
it satisfies the propositional invariant (which is guarded to prop vars, keystone localization) AND tracks the
numeric valuation (fluent vars, fresh). So a numeric run over combined configs `(L,vn,c)` IS a prop run (the
prop edges fire on `vn`, reading/writing only prop vars), which `happening_steps_possible`/`plan_steps_possible`
already give -- then lift step-by-step. The combinator `ext_seq'_induct_list_prop_and_post` can NOT be reused
for the existential numeric run (its `fs` would have to be a concrete `num_delay_and_apply`, the closed-form
we're avoiding), so `num_plan_steps_possible` is a bespoke chaining induction instead.

**Landed (all green):**
- **4 propositional transfers** `pp_post_imp_pre_pre_delay_Suc` / `pp_init_imp_pre_pre_delay_0` /
  `pp_post_last_imp_goal_trans_pre` / `pp_init_imp_goal_trans_pre` -- extracted config-generic from
  `plan_steps_possible`'s cases 3/5/6/4 (verbatim copies of the `c2..c8` chains, `s` -> `HOL.refl`).
  **Cleanup owed:** these duplicate the still-inline derivations in `plan_steps_possible` -- fold
  `plan_steps_possible` onto them in the refactor.
- **4 numeric twins** `num_post_imp_pre_pre_delay_Suc` / `num_init_imp_pre_pre_delay_0` /
  `num_post_last_imp_goal_trans_pre` / `num_init_imp_goal_trans_pre` -- each = prop transfer + the (identity,
  modulo `Suc(len-1)=len` / `len=0`) tracking transfer via the twin I/propD/trackD rules. ALL tracking
  transfers across happenings are IDENTITIES (the post twin at `i` and the pre twin at `Suc i` both track
  `snd (M (Suc i))`) -- only the run-lift core advances `w`.
- **`num_plan_steps_possible`** (the structural milestone): `num_init_planning_state_props' M cfg ==>
  \<exists>ms. num_graph_impl.steps (cfg#ms) \<and> num_goal_trans_pre M (last (cfg#ms))`. Proof: `len=0` ->
  `num_init_imp_goal_trans_pre`, run `[]` (`steps.Single`). `len>0` -> `num_init_imp_pre_pre_delay_0` then an
  inner `chain` induction (on the measure `len-1-j`) running happenings `j..len-1`: each step extends via
  `num_happening_steps_possible`, transfers post->pre(Suc) via `num_post_imp_pre_pre_delay_Suc`, splices runs
  with `num_graph_impl.steps_append`; then `num_post_last_imp_goal_trans_pre`.
- **`num_happening_steps_possible`** re-stated EXISTENTIALLY over a general `cfg` (the SINGLE `sorry`):
  `i<len ==> num_valid_state_sequence M ==> num_happening_pre_pre_delay M i cfg ==> \<exists>ns.
  num_graph_impl.steps (cfg#ns) \<and> num_happening_post M i (last (cfg#ns))`.

**NEXT -- `num_happening_steps_possible` (the run-lift core, the only real remaining content):** instantiate
`happening_steps_possible` at `cfg=(L,vn,c)` to get the prop run `(L,vn,c) # delay_and_apply i (L,vn,c)`; lift
it step-by-step -- leading delay via `num_steps_delay_replace[OF _ delay_non_negative num_no_urgent[...]]`,
each internal step via `num_int_step_lift` + `num_data_no_write_edge`/`num_data_upd_edge` (the source loc
`L_k!p` pins which edge fired -> which abstract snap), threading `num_tracks` to the running
`happening_num_update_set` partial fold; intra-happening guards checked at the partial store reduce to
`snd (M i)` via `sat_comps_happening_num_update_set` (non-interference). The abstract per-`i` facts
(`sat_comps (snd(M i)) (n_pre s)`, `happening_num_update_set S (snd(M i)) = snd(M(Suc i))`, active `n_inv`)
come from `num_valid_state_sequence M`. The \<section>B `INV` bounds + discreteness side-conditions stay
hypothesized (Layer C). Then the **capstone chain**: `num_initial_step_possible` (init edge, upd) /
`num_final_step_possible` (goal edge, no-write) / `num_goal_run_is_run` (goal-loop coinduction) /
`num_valid_plan_imp_form_holds : num_net_impl.sem, num_a\<^sub>0 \<Turnstile> reach_formula` -- each a single-step
lift; obtain `M` from `num_valid` once. NB the numeric initial config `num_a\<^sub>0` carries fluent vars set
to `num_init` (\<noteq> prop `a\<^sub>0`).

**Dev-loop notes (this session):** jEdit only auto-processes the band around the caret, so a far-from-caret
append idles at the tail -- force tail processing with a BOUNDED
`get_diagnostics ... wait_until_processed=true timeout<=40000` (warm prefix is cached, so it returns in
seconds; do NOT use a 6-min timeout -- it looks hung). The I/R REPL backend won't start on the
`Temporal_Planning_Base` heap (no `iq` import). GOTCHA: a `write_file` whose PERMISSION is rejected can still
have written the buffer -- a rejected-then-reissued insert DUPLICATED a block (caught via "Duplicate fact
declaration"). GOTCHA: `num_*I[OF \<dots>]` with the higher-order `snd (?M ?i)` premise gives "OF: multiple
unifiers" -- pin with `[where M = M and i = \<dots>]`.

**Cleanup flag:** stray `TA_Network/TP_NTA_Reduction_Correctness.thy~` editor backup (not in any ROOT) --
delete in the cleanup pass.

### CRITICAL design finding + course-correction (2026-06-23, later): the `num_*` twins are UNSATISFIABLE -- `num_plan_steps_possible` above is valid but VACUOUS. FIXED via Option A (projection): the projection infra + projection-form twins + bound-threaded transfers + `num_plan_steps_possible` are now GREEN & NON-VACUOUS (re-verified 2218 cmds / 0 err / 1 sorry); only the run-lift core + capstone remain.

The twins bundle `happening_pre_pre_delay i (L,v,c) \<and> num_tracks v (snd (M i))` on ONE store `v`. But
`happening_pre_pre_delay` ==> `Lv_conds` (Happenings:41) ==> `bounded (map_of net_bounds) v`, and Munta's
`bounded` is DOMAIN-EXACT (`dom v = dom bounds`, `Simple_Network_Language.thy:45`), forcing
`dom v = fst\`set all_vars` (= `net_bounds`, NO fluent vars); meanwhile `num_tracks v w` forces
`fluent_to_var f \<in> dom v`, and `fluent_vars_fresh` (Defs:609) puts fluent vars OUTSIDE `all_vars`.
Contradiction whenever `nfluents \<noteq> []`. So the twins cannot hold for a real numeric store, their hypotheses
are undischargeable, and the whole `num_plan_steps_possible` chain -- though green -- proves nothing about
non-empty-numeric problems. (It compiled because vacuous implications are valid; the gap only surfaces when
the capstone tries to INSTANTIATE the initial config.)

ROOT CAUSE: single-store twins conflate the propositional store (`net_bounds`-bounded, no fluent vars) with
the numeric store (`num_net_bounds`-bounded, has fluent vars). The keystone brick `num_int_step_lift` (:1564)
is ALREADY correct -- it carries prop `v` and numeric `vn` SEPARATELY (`v \<subseteq>\<^sub>m vn \<and> num_tracks vn w`).

FIX = **Option A (relational), user-directed, realized via the PROJECTION decomposition** (`vp = v|`pv`,
`vn = v|`nv`, `v = vp ++ vn`): keep ONE Munta store `v` (`num_net_bounds`-bounded); the prop predicate lives
on its projection `v |` dom (map_of net_bounds)` (which IS `net_bounds`-bounded), tracking on `v` (the fluent
part); `v = (v|`pv) ++ (v|`nv)` since `pv`/`nv` partition `dom v` by freshness. An edge = split its updates
into prop/numeric, apply to the two projections separately, re-unite.

**PROJECTION INFRASTRUCTURE -- DONE (green, new subsection at file end ~:2250; 1 sorry overall, unchanged):**
- `dom_map_of_num_net_bounds` (`dom num_net_bounds = dom net_bounds \<union> fluent_to_var\`set nfluents`),
  `fluent_var_notin_net_bounds`, `map_of_num_net_bounds_eq_on_props` (the bounds agree on prop vars).
- **`prop_proj_bounded`** (the key enabler): `bounded num_net_bounds v ==> bounded net_bounds (v |` dom (map_of net_bounds))`.
- **`store_decomp`**: `bounded num_net_bounds v ==> v = (v|`dom net_bounds) ++ (v|`(fluent_to_var\`set nfluents))`.

**Twin rework + transfers + `num_plan_steps_possible` -- DONE green (only the core + capstone remain); recipe followed (with a `boundD` rule added to each twin):** redefine the 5 twins to
`happening_X i (L, v|`dom(map_of net_bounds), c) \<and> num_tracks v (snd (M ?)) [\<and> bounded num_net_bounds v]`,
re-prove their I/propD/trackD rules, then rework the 4 numeric transfers + `num_plan_steps_possible` (the
`pp_*` PROP transfers + the chaining survive -- apply `pp_*` to the projection config `(L, v|`pv, c)`), THEN
the core `num_happening_steps_possible` (the run-lift, now genuinely dischargeable). The 4 `pp_*` prop
transfers and the projection infra are sound and reused as-is.

**Proof gotchas (this session, for the rework):** (a) `simp add: map_add_def` does NOT unfold `++` cleanly
here -- use `map_add_dom_app_simps(3)` (`m \<notin> dom l2 ==> (l1++l2) m = l1 m`) and `simp only:` to dodge
`map_add_None [iff]` interference. (b) Parser precedence: `v |` fluent_to_var\`set nfluents` mis-parses as
`(v |` fluent_to_var)\`...` -- always write `v |` (fluent_to_var\`set nfluents)`. (c) `num_*I[OF \<dots>]` with
the higher-order `snd (?M ?i)` premise gives "OF: multiple unifiers" -- pin with `[where M = M and i = \<dots>]`.
(d) A `write_file` whose PERMISSION is rejected can still have written the buffer -- this session a stray
edit corrupted line 1703 (`num_tracks_pres_unwritten` -> `t`); caught only by a full re-process
(undefined-fact error). Always re-verify the WHOLE file after a rejected/re-issued edit.

**Run-lift core (`num_happening_steps_possible`) -- SETUP green; the lift is the one remaining `sorry`.** The
proof now extracts the propositional happening run over the PROJECTION store `v|`dom(map_of net_bounds)` (via
`happening_steps_possible[OF i ppd]`, `ppd = num_happening_pre_pre_delay_propD`, yielding `prun`/`ppost`) --
confirming the projection approach end-to-end at the run level. The remaining `sorry` lifts `prun` to a numeric run.

- **PREREQUISITE for the lift -- a clean block move:** the "Projection infrastructure" subsection
  (`prop_proj_bounded`, `store_decomp`, `dom_map_of_num_net_bounds`, ...) currently sits at the file END (after
  `num_plan_steps_possible`), but the lift's proof needs it and Isabelle is linear -- so move that subsection UP to
  BEFORE `num_happening_steps_possible` (just before the "Run-lifting" subsection). Nothing between depends on it,
  so it is a pure relocation. NB read_file renders `\<dots>` escapes as Unicode glyphs, so reconstruct the block in
  ASCII escapes (from this session's writes) rather than str_replace-matching the read_file output.
- **The lift -- design (engine + discharge):** a generic engine `num_run_lift`, provable by induction on the
  list `prun`, takes a per-step discharge + an aligned tracking-witness list `ws` (`ws!k` = the running
  `happening_num_update_set` partial fold after k steps; `last ws = snd (M (Suc i))`) and yields the numeric run
  with `num_lifts (last) (last prun) (last ws)`, where
  `num_lifts (L,vn,c) (L,v,c) w \<equiv> v \<subseteq>\<^sub>m vn \<and> num_tracks vn w \<and> bounded num_net_bounds vn`.
  KEY: `v \<subseteq>\<^sub>m vn` + `dom v = dom(map_of net_bounds)` give `vn |` dom(map_of net_bounds) = v` EXACTLY, so the prop
  `happening_post` (on the prop last store) transfers to `num_happening_post`'s projection conjunct, and the bound
  conjunct comes from `num_lifts`; only the tracking needs `last ws = snd (M (Suc i))`.
- **The per-step discharge = the snap-ID (the hard content):** invert the prop step (`prop_int_step_invert`),
  case-split on `L ! p` to match the fired prop edge to its augmented numeric edge, discharge
  `num_data_{no_write,upd}_edge`, apply `num_int_step_lift`; intra-happening guards reduce to `snd (M i)` via
  `sat_comps_happening_num_update_set` + the `num_valid_state_sequence M` facts; the leading delay lifts via
  `num_steps_delay_replace[OF _ delay_non_negative num_no_urgent[...]]`. Then the capstone chain.

## Session handover — 2026-06-22 (Task 6: numeric forward-direction foundation + keystone per-step lifting, all green)

Worked **Task 6 (numeric capstone + lifting)** in `TA_Network/TP_NTA_Reduction_Correctness.thy`
(appended after the existing empty-numeric collapse; 619 -> 1512 lines, PIDE-verified **1458 cmds / 0
err / 25 warns**, consolidated, **0 sorry**). Got everything up to and including the **keystone generic
per-step lifting `num_step_int_lift`** (the hardest single Munta lemma); what remains is lower-risk
plumbing (inversion workhorse, per-edge wrappers, run-lifting, capstone). **Forward direction only**
(per the user: the reduction is *not* a bisimulation — only `valid_plan => form_holds` is proved and
needed; the converse is a separate, much larger effort — dropped).

**New locale `numeric_tp_nta_reduction_correctness`** (DONE): a triple merge at the *same*
propositional params — `tp_nta_reduction_correctness` (the prop bisimulation + `\<pi>`) +
`numeric_tp_nta_reduction` (the numeric net + wf) + `numeric_temp_plan_for_problem_list_impl_int` at
the `set o`-projection of the list numeric data (giving `num_plan.num_rat_impl.num_valid_plan`, the
rat-level numeric plan validity, where the abstract `num_valid_plan` lives). Shared ancestors
(`tp_nta_reduction_defs`, `temp_plan_for_problem_list_impl_int`) dedup. Two `assumes`: `num_valid`
(the numeric plan is valid) and `const_to_int_of_int` (`const_to_int (Int.of_int m) = m` — the
integer-encoding round-trip; **NB** `of_int` is shadowed by Munta's JSON parser, so qualify `Int.of_int`).

**Task 2 — numeric tracking foundation (DONE, all green) in `context numeric_tp_nta_reduction_correctness`:**
- `num_tracks v w` (+ I/`definedD`/`varD`) — *"v assigns the correct numeric values"*:
  `\<forall>f\<in>set nfluents. \<exists>r. w f = Some r \<and> v (fluent_to_var f) = Some (const_to_int r)`.
- Integer-encoding faithfulness algebra: `const_to_int_{add,diff,mult,div}` (div needs `dvd` — the
  documented `NDiv\<mapsto>div` gap), `const_to_int_{eq,le,lt}_iff`, `Ints_div_exact`. Uses HOL `\<int>`/`Ints`.
- `nexp_ok`/`comp_ok` — discrete-fragment side-conditions (every leaf an integer-valued declared
  fluent/const; `NDiv` divides exactly). `nexp_ok_fluents` (reads `\<subseteq>` nfluents).
- `nexp_ok_is_val` — one induction: `nexp_ok` => `eval_nexp` defined + `\<in>\<int>` + Munta `is_val` agrees.
- `check_bexp_comp_to_bexp` + `check_bexp_comps_guard` — `sat_comps w cs` => Munta `bexp_and_all
  (comp_to_bexp..)` holds `True` (the guard correspondence; explicit 5-way `cmp_op` case-split via
  `check_bexp_is_val.intros(6..10)`).
- `is_val_nexp_to_exp_cong` — Munta value depends only on read vars.
- **`is_upds_num_upd_aux`** (the hard one) — sequential Munta `is_upds` fold = simultaneous abstract
  override; `upds_no_cross_read` lets each later RHS ignore earlier writes. `kv`-parametrised induction;
  apply with `[where kv = ..., OF ...]` to avoid a higher-order-unification `?f` artifact.
- **`is_upds_num_upd`** — per-snap interface: applying `num_upd s` via `is_upds` preserves `num_tracks`,
  landing on abstract `apply_upds (set us) w` (= `snap_num_update`), prop vars untouched. Needs
  `upds_functional_set` (`distinct (map fst us)` => `upds_functional (set us)`).

**Task 3 — STARTED (per the user's methodology): stronger invariant twins + rules (DONE, green).**
The propositional per-step invariants `happening_pre`/`happening_post`/`happening_pre_pre_delay`/
`init_planning_state_props'`/`goal_trans_pre` (all in `..._Correctness_Happenings.thy`, `let`-destructured
over the Munta config `(L,v,c)`) each get a STRONGER twin `num_*` = the propositional pred `\<and>
num_tracks v (snd (M _))`, parametrised by the abstract numeric state sequence `M` (from
`num_valid_plan`): `snd (M i)` = valuation before happening `i`, `snd (M (Suc i))` = after; init twin
tracks `snd (M 0)`, goal twin tracks `snd (M (length htpl))`. Each twin has `I`/`propD`/`trackD` rules.
Each twin **implies** its propositional original, so the projection direction reuses the existing proof
verbatim.

**Numeric net semantics — DONE (green).** Added `sublocale num_net_impl: Simple_Network_Impl
num_timed_automaton_net net_broadcast num_net_bounds` and `sublocale num_graph_impl: Graph_Defs
(step_u' num_net_impl.sem ...)` — mirrors the propositional `net_impl`/`graph_impl`
(`tp_nta_reduction_model_checking:151-152`). `Simple_Network_Impl` is assumption-free, so bare `.`
interpretations. So `num_net_impl.sem` / `num_graph_impl.steps` are now in scope.

**Numeric step infrastructure (FIRST BATCH) — DONE (green).** Mirrored the propositional `Edges`-layer
structural facts onto `num_timed_automaton_net` (subsection "Numeric network step infrastructure"):
`num_no_committed`, `num_no_invs'`, `num_conv_invs` (the long `conv_invs` proof is automata-agnostic —
copied verbatim with `net_automata -> num_timed_automaton_net`), `num_no_invs`, `num_step_t_possible`
(the length-0 delay step), and `lemmas num_single_step_intro`/`num_non_t_step_intro`. KEY REUSE:
`conv_trans` and `conv_committed` are already stated generically over the automata list, so they apply
to the numeric net with NO re-proof. **Per-automaton trans/urgent (SECOND BATCH) — DONE (green):**
`num_main_auto_trans` (mirrors `schematic_goal main_auto_trans` at `Edges:1441`), `num_action_auto_trans`,
`num_action_auto_urg` (mirrors `action_auto_urg` at `Steps:234`) — these compute `trans`/`urgent` of the
numeric main/action automata. So the numeric net's `step_u`-firing inputs are all in place.

**EDGE-EFFECT + LIFTING-GLUE LAYER — DONE (green, ~1374 cmds).** Built the foundations that make the
per-step lifting a *generic* lemma rather than 8 mirrored apply-scripts:
- Numeric edge-effects (`num_start_edge_effect`/`num_end_edge_effect`/`num_edge_2_effect`/
  `num_main_auto_init_edge_effect`/`num_main_auto_goal_edge_effect`) — just the @{emph generic}
  `edge_effect` applied to the `augment_edge`'d edges (`edge_effect` applies updates/loc/reset, no guard
  check; `edge_3`/`instant_trans` reuse the propositional effects, no numeric data).
- `edge_effect_augment_loc`/`edge_effect_augment_clk` (GENERIC over any edge) + the 10 per-edge
  `num_*_effect_loc`/`_clk` corollaries: the augmented edge-effect has the SAME location and clocks as
  the propositional one (only fluent vars differ). => the numeric run's locations/clocks coincide with
  the propositional run's.
- `length_num_net_automata`; and **`check_bexp_is_val_mono`** (Munta `check_bexp`/`is_val` are monotone
  under store extension `\<subseteq>\<^sub>m`, by mutual `check_bexp_is_val.inducts`). Since the numeric store agrees
  with the propositional store on prop vars and only ADDS fluent vars (`v \<subseteq>\<^sub>m vn`), this transfers every
  propositional guard/value verbatim to the numeric store — NO `vars_of` apparatus needed.

**DESIGN — the GENERIC per-step lifting (inversion-reconstruction), NOT 8 mirrored scripts.** (Realized
as the keystone `num_step_int_lift` below; this paragraph records the design + the edge-matching table
the per-edge wrappers still need.) KEY INSIGHT: invert the propositional internal step (`step_u` is
`step_int` here, `Simple_Network_Language.thy:80`) to extract the fired edge `e` + `check_bexp v b True`
+ `is_upds v f v'`; then RECONSTRUCT the numeric `step_int` for the augmented edge `augment_edge gn fn e`
at the same automaton `p`. This REUSES the prop step entirely (so the `check_bexp` monsters in
`final_step_possible`/`...Steps.thy` are NOT re-proved):
transfer `check_bexp vn b True` via `check_bexp_is_val_mono` (`v \<subseteq>\<^sub>m vn`); conjoin the numeric guard
`check_bexp vn gn True` (via `check_bexp_Cons` + `check_bexp_comps_guard`); for updates, `is_upds vn (f @
fn)` via `is_upds_appendI` + `is_upds_map_le` (prop `f`) + `is_upds_num_upd` (numeric `fn`);
committed/invs via `num_no_committed`/`num_no_invs`; trans-membership of
the augmented edge via `num_main_auto_trans`/`num_action_auto_trans` + the generic `conv_trans`. The only
edge-dependent part is matching `e` to its `(gn,fn)` (start->`num_pre_guard(at_start a)`,`num_upd(...)`;
end->at_end; edge_2->`num_inv_guard`,`[]`; goal->`num_goal_guard`,`[]`; init->`true`,`num_init_upd`;
edge_3/instant/loop->`true`,`[]` i.e. reused unchanged) — a bounded case split.

**ALL LIFTING GLUE IS NOW PROVEN (green):** `check_bexp_is_val_mono` (guard transfer), **`is_upds_map_le`**
(update transfer: `is_upds v f v' \<Longrightarrow> v \<subseteq>\<^sub>m vn \<Longrightarrow> \<exists>vn'. is_upds vn f vn' \<and> v' \<subseteq>\<^sub>m vn' \<and> vn' = vn off the
written vars` — clean induction on `f` using the mono lemma), `is_upds_appendI` (Munta), `num_no_committed`/
`num_no_invs`/`num_non_t_step_intro`, `num_main_auto_trans`/`num_action_auto_trans`/`conv_trans`,
`edge_effect_augment_loc`/`_clk`, `length_num_net_automata`, `check_bexp_comps_guard`, `is_upds_num_upd`.

**KEYSTONE `num_step_int_lift` — DONE (green, ~1458 cmds).** The generic numeric internal step:
@{prop "p < length num_timed_automaton_net"}, the augmented edge @{prop "(l, bg, g, Sil a, fu, r, l')
\<in> trans (automaton_of (num_timed_automaton_net ! p))"}, @{prop "check_bexp vn bg True"}, @{prop "c \<turnstile>
conv_cc g"}, @{prop "L ! p = l"}, the length match, @{prop "is_upds vn fu vn'"}, numeric @{text bounded}
=> @{text "num_net_impl.sem \<turnstile> \<langle>L,vn,c\<rangle> \<rightarrow>Internal a \<langle>L[p:=l'],vn',[r\<rightarrow>0]c\<rangle>"}. Proof = `rule
step_u.step_int[where p=p]` then discharge each tagged premise (TRANS via `conv_trans`+`image_eqI`;
committed via a local `committed_empty` = `conv_committed`+`num_no_committed`; bexp/guard/loc/is_upd/bounded
from the assumptions; invariant via `rule allI,impI,subst num_no_invs,assumption,simp`; new-loc/valuation
by `refl`). GOTCHAS that cost iterations: do NOT use `subgoal` (it fixes the rule's schematic edge vars
before they unify against `conv_edge` — use a flat `apply`-chain so proving TRANS first instantiates
`?l/?b/?g/?f`); and `simp` normalises `(map f xs)!p` to `f (xs!p)`, after which `num_no_committed`/
`num_no_invs` (stated in the `map` form) no longer match — so `subst` them BEFORE any `simp`.

**NEXT (the keystone is proven; what remains is plumbing, not deep Munta):** (1) per-edge wrappers
matching each prop edge to its `(bg, g, fu)` and discharging the numeric guard/update — for an edge
fired by `edge_effect`, `bg = bexp.and b gn`, `fu = f @ fn`; `check_bexp vn bg True` from
`check_bexp_Cons` + `check_bexp_is_val_mono` (prop `b`) + `check_bexp_comps_guard` (numeric `gn`);
`is_upds vn fu vn'` from `is_upds_appendI` + `is_upds_map_le` (prop `f`) + `is_upds_num_upd` (numeric `fn`).
INVERSION TOOL: to extract the prop edge + `check_bexp`/`is_upds` facts from a propositional internal
step, use Munta's `step_u_elims'(2)` (`Simple_Network_Language_Impl.thy:893`, the
`(broadcast, N, B) \<turnstile> \<langle>L,s,u\<rangle> \<rightarrow>Internal a \<langle>L',s',u'\<rangle>` case) — the edge it yields is the CONV edge (guard
`conv_cc g`), so un-conv via `conv_trans` to recover the plain edge for matching to the augmented one.
(2) run-lifting over `plan_steps` (locations/clocks already coincide via `edge_effect_augment_loc`/`_clk`),
threading the `num_*` twins' `num_tracks` config-by-config. (3) `num_plan_steps_possible` + capstone +
upgrade the empty-collapse `numeric_valid_temp_plan_imp_form_holds`. The §B `INV` bounds are still owed
(take as hypothesis). This avoids mirroring `delay_and_apply` and the heaviest `...Steps.thy` apply-scripts
entirely.

(For (3) above: `num_plan_steps_possible` mirrors `plan_steps_possible`'s 6-case
`steps_seq.ext_seq'_induct_list_prop_and_post` with the `num_*` twins as `P`/`Q`/`R`/`S`; each twin
implies its prop original, so each invariant-transfer case reuses the prop case and adds only the
`num_tracks` transfer at the matching index. `M` comes from `num_valid` =
`num_plan.num_rat_impl.num_valid_plan = \<exists>M. num_valid_state_sequence M \<and> snd (M 0) = num_init \<and>
sat_comps (snd (M len)) num_goal \<and> ...`. The §B `INV` bounds meta-theorem — every plan-reachable abstract
state in bounds, so Munta's `bounded` side-condition never blocks a numeric step — is owed; take as a
hypothesis at this layer.)

**Update (later 2026-06-22) — the per-step internal-lift layer AND the full per-edge `num_data` discharge
layer landed (green, consolidated, 1601 cmds / 0 err / 0 sorry; file ~1733 lines). Task-6 NEXT-(1) is
DONE: every internal edge of the propositional net lifts to the numeric net, via a generic layer:**
- `prop_int_step_invert` (`:1516`) — the inversion workhorse: a propositional internal step of
  `net_impl.sem` inverts (Munta `step_u_elims'(2)` + `conv_trans` to un-`conv_automaton` the edge) to the
  fired plain edge `(l,b,g,Sil a,f,r,l') \<in> trans (automaton_of (net_automata ! p))` + `check_bexp v b
  True` + `c \<turnstile> conv_cc g` + `L!p=l` + `L'=L[p:=l']` + `c'=[r\<rightarrow>0]c` + `is_upds v f v'`. **NB it needs the
  extra hypothesis `length L = length net_automata`** — `step_int` only exposes `p < length L`; the
  net-length bound is the `L \<in> states` invariant, threaded exactly as the keystone's `L_len` is (every
  reachable caller has it).
- `num_int_step_lift` (`:1562`) — the GENERIC per-step lift = `prop_int_step_invert` + keystone
  `num_step_int_lift`. Takes a propositional internal step (+ `length L = length net_automata`) and a
  `num_data` provider: for the inverted fired edge the provider exhibits the augmented numeric edge in
  `num_timed_automaton_net`, `check_bexp vn bg True`, `is_upds vn fu vn'`, numeric `bounded`, and
  `v' \<subseteq>\<^sub>m vn'`; it yields `\<exists>vn'. num_net_impl.sem \<turnstile> \<langle>L,vn,c\<rangle> \<rightarrow>Internal a \<langle>L',vn',c'\<rangle> \<and> v' \<subseteq>\<^sub>m vn'`.
  **Design decision realized here:** the numeric run is *existential* (threaded through the induction),
  NOT a closed-form `num_delay_and_apply` — that is what "avoids mirroring delay_and_apply entirely"
  means concretely.
- `num_data_no_write_edge` (was `num_data_unchanged_edge`, now generalised + tracking-threaded) —
  discharges `num_data` for any edge with NO numeric update (`fu = f`): the unchanged edges
  (`edge_3`/`instant_trans_edge`/`main_auto_loop`) AND the guard-only augmented edges (`num_edge_2`/
  `num_main_auto_goal_edge`, whose `augment_edge` appends `[]`). Caller supplies the assembled combined
  guard `check_bexp vn bg True` + edge membership + `f`-freshness + boundedness; outputs `num_tracks vn' w`.
- `is_upds_unchanged` / `num_tracks_pres_unwritten` — freshness bricks: a Munta update leaves unwritten
  vars alone; numeric tracking survives a prop update writing no fluent var (via `fluent_vars_fresh`).
- `num_int_step_lift` was revised to THREAD TRACKING — its `num_data` existential and conclusion now also
  carry `num_tracks vn' w'` (the run-lifting threads the numeric valuation config-by-config; the `num_*`
  twins only pin tracking at happening boundaries).
- `num_data_upd_edge` (start/end/init — the only discharge that CONSUMES numeric data) — GREEN:
  `fu = f @ num_upd s`; guard-and-intro + `is_upds_map_le` -> `num_tracks_pres_unwritten` ->
  `is_upds_num_upd` -> `is_upds_appendI`, plus a `v' \<subseteq>\<^sub>m vn'` freshness argument; outputs
  `num_tracks vn' (apply_upds (set us) w)`.

**Discreteness is owed as a hypothesis (NEW finding).** The locale `numeric_tp_nta_reduction` carries NO
discreteness assumption (its 7 assumes are `upds_functional_*` / `upds_no_cross_read_*` /
`fluent_bounds_valid` / `fluent_to_var_inj` / `fluent_vars_fresh`). But the guard/update correspondences
need `comp_ok w c` / `nexp_ok w e` (every leaf an integer-valued declared fluent; `NDiv` divides exactly)
at the reachable valuations -- NOT supplied by `num_valid_state_sequence`. So, exactly like the §B `INV`
bounds, the discrete-fragment side-conditions (§A.3, the "reject transcendentals" boundary) are threaded as
hypotheses at this layer and discharged later (Layer C / a problem-level discreteness guarantee).
`num_data_upd_edge` takes `nexp_ok w e` as `fn_ok`; the run-lifting carries `comp_ok`/`nexp_ok` likewise.

**NEXT — Task 2 (run-lifting) is now the main remaining work.** All per-edge `num_data` discharge bricks
exist (no-write + upd). Run-lifting: mirror `plan_steps_possible`'s `ext_seq'_induct_list_prop_and_post`
with the `num_*` twins as P/Q/R/S; at each internal micro-step apply `num_int_step_lift`, discharging
`num_data` via `num_data_no_write_edge` / `num_data_upd_edge` -- the source location `L!p` pins which edge
fired (resolving the case-split), and `num_valid_state_sequence` (from `num_valid`) supplies the
`sat_comps`/well-formedness; tracking threads config-by-config via the per-step `num_tracks vn' w'`.
**The heart of the numeric content:** intra-happening guards are checked at the partially-updated Munta
store but read only fluents un-written by co-occurring snaps (numeric non-interference,
`num_mutex_snap_action`), so `sat_comps w (n_pre s)` at the pre-happening `w` suffices. Delays via a
numeric `steps_delay_replace`-analog. Then (3) capstone + upgrade `numeric_valid_temp_plan_imp_form_holds`.
§B `INV` bounds + discreteness stay hypothesized.

**Task 2 STARTED — non-interference foundation landed (green, file ~1766 lines / 1622 cmds / 0 err / 0
sorry):** `sat_comp_cong` / `sat_comps_cong` (end of the numeric context) -- a guard's truth depends only
on the fluents it reads (`comp_fluents`), lifting `eval_nexp_cong` to `sat_comp`/`sat_comps`. (NB general
`sat_comp` facts -- flagged in-file to move to the abstract `Temporal_Plans` layer in the refactor. Proof
gotcha: `sat_comp_def` unfolds to `case c of Comp p a b ...` which rebinds `a`/`b`, so reduce the case
first -- `unfolding sat_comp_def Comp by (simp only: comp.case ea eb)`, not a bare `simp`.) **Immediately
next brick:** guard-invariance under a partial happening update by non-interfering snaps --
`sat_comps w (set (n_pre s)) \<Longrightarrow> sat_comps (happening_num_update_set S w) (set (n_pre s))` when every
`s' \<in> S` has `\<not> num_mutex_snap_action s s'` (so `S`'s writes miss `snap_reads s`, which contains the
guard's read fluents); proof = `sat_comps_cong` + `snap_num_update_unwritten` over the finite
`happening_num_update_set` insert law.

**Task 2 brick DONE — guard invariance under a partial happening update landed (green, file ~1833 lines /
1669 cmds / 0 err / 31 warns / 0 sorry):** two lemmas at the end of `numeric_tp_nta_reduction_correctness`:
- `happening_num_update_set_unwritten` — the set-level happening update agrees with the pre-happening
  valuation off the fluents the happening writes: `finite S`, functional + pairwise-non-interfering `S`,
  and `f \<notin> (\<Union>s\<in>S. snap_writes s)` => `happening_num_update_set S w f = w f`. Finite induction (`induction
  arbitrary: w rule: finite_induct`) over `happening_num_update_set_insert`, each peeled snap left alone by
  `snap_num_update_unwritten`.
- `sat_comps_happening_num_update_set` (the brick) — if the guard set `C` reads only `snap_reads s` and
  every `s' \<in> S` has `\<not> num_mutex_snap_action s s'`, then `sat_comps (happening_num_update_set S w) C =
  sat_comps w C`. Proof = `sat_comps_cong` reduces to per-read-fluent agreement; the third disjunct of
  `num_mutex_snap_action_def` puts each read fluent outside `S`'s writes; `happening_num_update_set_unwritten`
  finishes.

**RESOLVED the next-session gotcha (qualified names):** in `numeric_tp_nta_reduction_correctness` the
abstract `numeric_action_defs` *definitions* (`happening_num_update_set`, `snap_writes`, `snap_reads`,
`num_mutex_snap_action`, `snap_num_update`, and their `_def`/`_empty`/`_insert`/`_unwritten` lemmas) ARE
reached as `num_plan.num_rat_impl.*` (confirmed). BUT the *parameter* `upds` is NOT a constant — it has no
`num_plan.num_rat_impl.upds`; the locale instantiates it to `set o upds`, so write the term directly as
`(set \<circ> upds) x` (the LIST-valued `upds` is the correctness-locale parameter at `:662`). The theory-level
numerics (`apply_upds`, `upds_functional`, `nexp_fluents`, `sat_comp`/`sat_comps`/`comp_fluents`,
`eval_nexp`) stay UNQUALIFIED. **`set o upds` vs `\<lambda>a. set (upds a)` friction (cost iterations):** `induct`/
`induction` normalises hypotheses/`?case` goals to the `\<lambda>a. set (upds a)` (comp-applied) form, while my
folded `num_plan.num_rat_impl.X` statements and the interpreted `_def`/`_empty`/`_insert` rules keep
`set o upds`; these differ only by `comp_def` and are NOT bridged by plain `simp`/`auto`. Fixes used: add
`comp_def` to discharging `simp`/`auto` (`by (auto simp: comp_def)`); pre-normalise a *rewrite rule* whose
LHS carries `set o upds` with `[unfolded comp_def]` (plain `simp add: comp_def` does NOT rewrite a rule's
own LHS — e.g. `happening_num_update_set_empty[unfolded comp_def]`); keep `have` STATEMENTS in the folded
`num_plan.num_rat_impl.X` form so `rule`/`[OF \<dots>]` chains unify folded-to-folded; and discharge the last
premise of `happening_num_update_set_unwritten` via a named fact passed as the 4th `[OF \<dots>]` arg, not via
`thus \<dots> by (rule \<dots>)` chaining (the chained-fact resolution failed to unify the schematic `?w`). Also:
`induct` does NOT bind `.IH` — use the `induction` method.

**Numeric delay primitives DONE (green, file ~1922 lines / 1744 cmds / 0 err / 34 warns / 0 sorry):** two
lemmas in a new subsection "Numeric delay primitives for the run-lifting" at the end of the numeric context,
1:1 mirrors of the propositional delay machinery with `graph_impl`->`num_graph_impl`,
`net_impl`->`num_net_impl`, `net_automata`->`num_timed_automaton_net`:
- `num_steps_replace_Cons_hd` — head-replacement for the numeric graph (mirror of `steps_replace_Cons_hd`);
  pure `Graph_Defs` plumbing via `num_graph_impl.steps_ConsD`/`steps_append`.
- `num_steps_delay_replace` — absorb a leading delay on the numeric run (mirror of `steps_delay_replace`,
  the primitive `happening_steps_possible` uses at its delay): invert the first `Del` step
  (`step_u_elims(1)`), re-issue a longer one via `step_u.step_t` (numeric invariants empty via `num_no_invs`,
  bounded carried), splice via `num_steps_replace_Cons_hd` + `num_single_step_intro`. **`not_urgent` is a
  HYPOTHESIS** (the caller/run-lifting discharges it from `num_happening_pre_pre_delay`'s pinned locations),
  so no numeric-urgent computation is needed here. Compiled green first try; the 3 new warnings are the
  benign `step_u` vs `step_sn` "Ambiguous input" parse warnings (same class as the dozens already present on
  the step notation).

**Numeric sem-structure + no-urgent DONE (green, file ~1997 lines / 1820 cmds / 0 err / 34 warns / 0 sorry):**
three more lemmas appended after the delay primitives, all 1:1 mirrors of propositional facts and all green
first try:
- `num_sem_alt_def` (schematic, mirror of `sem_alt_def` in `TP_NTA_Reduction_Model_Checking.thy:163`) —
  exposes the structure of `num_net_impl.sem`; and `length_num_net_impl` (mirror of `length_net_impl`) —
  `length ((fst o snd) num_net_impl.sem) = Suc (length actions)` via `length_num_net_automata`.
- `num_no_urgent` — `happening_pre_pre_delay i (L,v,c) ==> \<forall>p<length (fst (snd num_net_impl.sem)).
  L!p \<notin> urgent (fst (snd num_net_impl.sem) ! p)`, the exact `not_urgent` hypothesis `num_steps_delay_replace`
  needs. It is the inline `no_urgent` block of `happening_steps_possible` (`:38-90`) re-stated as a standalone
  lemma with `num_` structure facts (`num_sem_alt_def`/`length_num_net_impl`/`num_main_auto_def`/
  `num_action_auto_urg`): the numeric net carries the SAME locations (shared `happening_pre_pre_delay`) and
  the SAME urgent sets (`augment_edge` leaves the urgent component untouched — main `{init_loc,goal_loc}`,
  action `{starting_loc,ending_loc}`) as the propositional net. So the leading-delay discharge for the numeric
  run is now turnkey: `num_steps_delay_replace[OF _ delay_non_negative num_no_urgent[...]]`.

**NEXT — the run-lifting proper (the remaining bulk):** mirror `plan_steps_possible`'s
`ext_seq'_induct_list_prop_and_post` (the 6 goal cases at `TP_NTA_Reduction_Correctness.thy:194`; cases
1/3/4/5/6 are transfer cases that reuse the prop proof + carry `num_tracks` — NB case 3 (post i -> pre Suc i)
is an IDENTITY `num_tracks` transfer since `snd (M (Suc i))` is BOTH the post-value of happening `i` and the
pre-value of happening `Suc i`; only clocks change across the delay) with the `num_*` twins as P/Q/R/S. The
hard case is 2, the numeric `happening_steps_possible`: thread `num_tracks` through `s # delay_and_apply i s`.
Bricks now ALL in place: per-internal-step lift `num_int_step_lift` + `num_data_no_write_edge`/
`num_data_upd_edge` (`L!p` pins which edge fired); the leading delay turnkey via
`num_steps_delay_replace[OF _ delay_non_negative num_no_urgent[...]]` (`num_no_urgent` discharges the
`not_urgent` side-condition); the post-delay internal tail's per-step 0-delays via `num_step_t_possible`
(length 0); and intra-happening guards at the partially-updated store via
`sat_comps_happening_num_update_set`. `M`/`num_valid_state_sequence` from `num_valid`. §B `INV` bounds +
discreteness stay hypothesized. So the ONLY remaining work is the SEQUENCING: a run-lift induction over the
propositional `graph_impl.steps (s # delay_and_apply i s)` that applies these per-step bricks and threads
`num_tracks` config-by-config (each internal micro-step lands on the partially-updated abstract valuation, a
running `happening_num_update_set` fold) -- assembling `num_happening_steps_possible`, then
`num_plan_steps_possible`, then the capstone upgrade `numeric_valid_temp_plan_imp_form_holds`.

**REFACTOR OWED — split the numeric block out of `TP_NTA_Reduction_Correctness.thy` into its own
theory chain, mirroring the propositional split (`_Prelims`/`_Edges`/`_Happenings`/`_Steps`/`_Correctness`).**
All the numeric Task-2/3 work was appended into the single `TP_NTA_Reduction_Correctness.thy` (now ~1512
lines / 1458 cmds) to keep the warm-jEdit iteration fast; once the capstone is green, do an `isabelle-refactor` pass
to move it into parallel files, e.g.: a numeric **Defs/Prelims** (`numeric_tp_nta_reduction_correctness`
locale + `num_net_impl`/`num_graph_impl` sublocales + `num_tracks` + the `const_to_int_*` faithfulness
algebra + `nexp_ok`/`comp_ok` + the `is_val`/guard/`is_upds_num_upd` correspondences), a numeric **Edges**
(`num_no_committed`/`num_no_invs`/`num_step_t_possible`/intros + per-automaton `trans`/`urgent` +
numeric edge-effects + `edge_effect_augment_loc`/`_clk` + the lifting glue `check_bexp_is_val_mono`/
`is_upds_map_le`/`length_num_net_automata` + the keystone `num_step_int_lift` + the per-edge wrappers),
a numeric **Happenings** (the `num_*` invariant twins + rules + `num_happening_steps_possible`),
and a numeric **Steps/Correctness** (`num_plan_steps_possible` + the capstone). Keep each re-opening
`context numeric_tp_nta_reduction_correctness`. This is the same shape as the 2026-06-21 split of the
456 KB file.

**Cleanup owed:** ~5 "duplicate rewrite rule" warnings from naming default-simp lemmas (`of_int_mult`,
`Ints_add`, `nonzero_mult_div_cancel_left`, ...) in the `const_to_int_*` helpers; and the benign
"Ambiguous input" (`step_u` vs `step_sn`) parse warning on `num_step_t_possible` (the propositional
`step_t_possible` has it too).

**Confusing pure-rename `abbreviation`s owed for cleanup (flagged by the user 2026-06-22) -- do in the
refactor pass, not now.** Several Isabelle `abbreviation`s in `TP_NTA_Reduction_Defs.thy` are pure
renames of an existing constant, so one object travels under two names and a reader must keep the
alias <-> definition pairing in mind across proofs:
- `net_automata \<equiv> timed_automaton_net` (`:391`)
- `net_bounds :: ... \<equiv> all_vars` (`:390`)
- `num_net_bounds :: ... \<equiv> num_all_vars` (`:542`)
- `urge \<equiv> urge_clock` (`:392`)
Collapse each to a single canonical name in the refactor (rename the underlying `definition` and drop the
alias) so there is one name per concept. NB keep the genuine-shorthand abbreviations
(`var_is`/`inc_var`/`set_var` `:94-96`, `mutex_effects` `:134`) -- those abbreviate a *compound
expression*, they do not just rename a def.

## Session handover — 2026-06-21

### Refactor pass — 2026-06-21 (structural cleanup, all PIDE-verified green)

Three refactors landed to make the (former) 456 KB correctness file tractable for the remaining numeric
work:

1. **`plan_steps_possible` case 3 -> structured Isar** (in `TP_NTA_Reduction_Correctness`). The
   post->pre invariant-transfer case now surfaces each invariant conjunct as a named `have` (`c2`..`c8`)
   from `happening_post_dests` via its transfer lemma, threading the index bounds `ib1`/`ib2` (the
   conditional transfer lemmas + the index-guarded `prop_state` defs need them), assembled through
   `happening_pre_pre_delayI`. **Cases 5 and 6 (init->pre0, post->goal) are now converted too** (same
   pattern; case 5 extracts the init conjuncts via `init_planning_state_props'E`, case 6 via
   `happening_post_dests`), so **`plan_steps_possible` is now fully structured Isar** -- the next-step-5
   "convert the ones you touch to Isar first" prep for the numeric `num_plan_steps_possible` mirror is
   DONE. (The codebase now has **zero `rule_tac`**: the one `rule_tac exI` a subagent left in case 6's
   `c5` was restructured to `rule exI[of _ w]` with the facts chained inside the `show`, per the new
   `isabelle.md` rule "prefer the modern method over its `*_tac` variant".)

2. **Split `TP_NTA_Reduction_Correctness.thy` (8792 lines) -> 5 theories** along section seams, each
   re-opening `context tp_nta_reduction_correctness`: `..._Prelims` (defs + the nested per-index context),
   `..._Edges`, `..._Happenings`, `..._Steps` (the five per-edge `*_possible` lemmas), and
   `TP_NTA_Reduction_Correctness` (`happening_steps_possible` + `plan_steps_possible` + capstone + tail
   contexts, ~600 lines -- kept the name, so downstream imports are untouched). Gotcha fixed: a local
   `interpretation steps_seq` does NOT persist across context re-openings -> converted to a persistent
   **`sublocale steps_seq`** (in `..._Happenings`), the correct form anyway.

3. **`_Spec` -> `_Defs` rename + dropped `_spec` on net-construction constants.** Theory
   `TP_NTA_Reduction_Spec` -> `TP_NTA_Reduction_Defs`; locales `tp_nta_reduction_spec`/`'`/`numeric_...`
   -> `..._defs`. The 40 net-construction `*_spec` constants dropped the suffix (`all_vars_spec`->`all_vars`,
   the edges, etc.), **except the Munta-name colliders**, renamed descriptively:
   `automata_spec`->`net_automata`, `broadcast_spec`->`net_broadcast`, `bounds_spec`->`net_bounds`,
   `int_clocks_spec`->`net_int_clocks`, `num_bounds_spec`->`num_net_bounds`, `formula_spec`->`reach_formula`
   (plus the primed executable `'` versions). The **grounding-layer problem-data `_spec` family**
   (`actions_spec`, `at_start_spec`, `pre_spec`, `goal_spec`, ... defined in `Ground_PDDL_Problem_Defs`,
   e.g. `actions_spec == actions D`) was **kept `_spec`** -- different layer, and dropping collides with
   the PDDL accessors (`actions D`, `pre`, ...). Verified green: TA_Network (Defs 114, final correctness
   619) + Ground_PDDL (Impl 1019, Check_Unsolvability 742, NTA_Reduction_Correctness 25).
   `Unsolvability_Code_Compile` (final codegen) is unchanged by the rename (codegen is by-reference) and
   was not re-run. **Spec-cleanup follow-up (also green):** the `\<`-anchored rename initially missed
   mid-token compound lemma names -- `map_of_bounds_spec_*` / `map_of_all_vars_spec_exact` /
   `dom_map_of_bounds_spec_exact` were renamed to `map_of_net_bounds_*` / `map_of_all_vars_exact` /
   `dom_map_of_net_bounds_exact`. The grounding-layer problem-data `_spec` family
   (`actions_spec == actions D`, `at_start_spec`, `pre_spec`, ... in `Ground_PDDL_Problem_Defs`) is
   **kept** -- a suitable use of "spec" (the PDDL problem is a specification) and bare names would
   collide with the accessors (`actions D`, `pre`, ...).

NB: the numeric-status notes below predate this rename, so they still cite the old `*_spec` names
(`all_vars_spec`, `bounds_spec`, `formula_spec`, ...); read them through the mapping above.

### Numeric reduction status (pre-rename names)

Started **Layer B (numeric NTA reduction)** on the abstract reduction layer, **ahead of P0** (decided
with the user: do the P0-independent reduction core now, enforce the grounder-match at the *contract*
level — NUMERIC_PLAN §A.6). **The entire numeric reduction is now defined and well-formed** — the
projection lemma + keystone (PASS) + §A.3 match (items 1–3 below), the full numeric net (P4), and the
wf locale (P5), all green. The one piece left is the numeric **correctness capstone + lifting**
(**Task 6**); its concrete plan + first step is at the end of this note (**Next (Task 6 …)**).

1. **Projection lemma — green.** `Temporal_Plans.thy` (locale `numeric_temp_plan_defs`):
   `num_valid_plan_imp_valid_plan` (§A.6 step 1) + helpers `num_valid_state_sequence_imp_valid`,
   `num_mutex_valid_plan_imp_mutex`. The projection `num_valid_plan ⟹ valid_plan` is **unconditional**
   (the propositional conjuncts of `num_valid_state_sequence` are literally `valid_state_sequence` on
   `fst ∘ M`; `num_mutex_valid_plan = mutex_valid_plan ∧ …`). File fully processed, 0 errors. This is
   the lemma the numeric capstone reuses.

2. **Keystone (§5.5) — static PASS, risk localized** ([[layer-b-keystone-localized]]). Extra bounded
   int vars in `all_vars_spec`/`bounds_spec` do **not** disturb the core bisimulation —
   `happening_pre/post`, `goal_state_conds`, `init_planning_state_props'` are all guarded
   (`∀p. p ∈ set props ∧ prop_to_var p ∈ dom (map_of bounds_spec) ⟶ …`). Only touch-points: the
   `undef_vars` clause in `init_state_props` (`TP_NTA_Reduction_Correctness.thy:3645/3652`) /
   `init_planning_state_props` (3661/3671) + dests, and the exact-set schematics `set_init_vars_exact`
   (5355) / `dom_map_of_bounds_spec_exact` (5363). Confirms §A.6 "few lemmas, not a 456 KB rewrite."

3. **§A.3 boundary map confirmed** vs Formal-PDDL-Semantics ([[numeric-boundary-map-confirmed]]).
   `numeric_expression`/comparison atoms/`numeric_effect`/`duration_constraint` map 1:1 to the abstract
   `nexp`/`comp`/`upds`; `action_numeric_update_function_simplified` gives one assignment per fluent
   (⇒ `upds_functional` by construction). **Grounder-match flag:** `wf_numeric_expression` accepts
   transcendentals, so our Layer-C boundary must reject them via `is_globally_safe` (fail-closed).

**P4 — Layer-B spec augmentation DONE (the full numeric NTA-reduction net is constructed and green in `TP_NTA_Reduction_Spec.thy`):**
- `nexp ⇒ exp` / `comp ⇒ bexp` encoders (`nexp_to_exp`/`comp_to_bexp`, theory-level, parameterised by
  `fluent_to_var` + a value-to-int map `const_to_int`; `NMul`→`times`, `NDiv`→`div` = documented
  integer-division gap).
- locale **`numeric_tp_nta_reduction_spec`** = `tp_nta_reduction_spec` + LIST-based numeric data
  (`n_pre`/`n_inv`/`upds`/`num_goal` as lists like propositional `pre`/`adds`; the set view is derived
  via `set ∘` at correctness, mirroring `set_impl.pre`) + `num_init` + `nfluents` + `fluent_to_var` +
  `fluent_lo`/`fluent_hi` + `const_to_int`. Merge unifies by name (numeric fields sidestep the
  list-vs-set split) — verified.
- `num_fluent_vars_spec` (one bounded int var per fluent) + `num_all_vars_spec = all_vars_spec @
  num_fluent_vars_spec` (the §A.5 var-set augmentation, reusing the propositional `all_vars_spec`).
- **guards** `num_pre_guard`/`num_inv_guard`/`num_goal_guard` (`bexp_and_all` of `comp_to_bexp` over
  `n_pre`/`n_inv`/`num_goal`); **updates** `num_upd` (`(fluent_to_var f, nexp_to_exp … e)` from `upds`)
  and `num_init_upd`; a generic `augment_edge` conjoins a numeric guard and appends numeric updates,
  keeping locations/clocks/resets.
- **edges + net** (all reuse the propositional defs): `num_start_edge_spec`/`num_end_edge_spec` (n_pre +
  upds on the snaps), `num_edge_2_spec` (n_inv on running-entry), `num_main_auto_init/goal_edge_spec`
  (num_init / num_goal) → `num_action_to_automaton_spec` → `num_main_auto_spec` →
  **`num_timed_automaton_net_spec`**, plus `num_bounds_spec`/`num_init_vars_spec`. The numeric net's
  propositional projection IS the propositional net by construction (`augment_edge` only conjoins/appends).

**Architecture (in [[layer-b-keystone-localized]]):** separate additive net; propositional projection =
the propositional net; 456 KB proof untouched; numeric capstone = projection (done) + existing capstone
+ lifting lemma.

**Naming decision — DONE (2026-06-21, see Refactor pass at top; executed as `_Defs`, not `_Def`).**
Original deferred plan: `_Spec` is a misnomer (file header: "Abstract definition of
reduction"). Rename `TP_NTA_Reduction_Spec`/`tp_nta_reduction_spec*` → `_Def`, and DROP the `*_spec`
const suffixes (NOT `*_def` — collides with Isabelle's `X_def` unfolding lemmas), as ONE
`isabelle-refactor` pass over spec + the 456 KB correctness file, AFTER the numeric build (kept `_spec`
meanwhile for consistency).

**P5 — wf locale DONE (green in `TP_NTA_Reduction_Spec.thy`):** `numeric_tp_nta_reduction` =
`numeric_tp_nta_reduction_spec` + 7 grounder-match `assumes` — `upds_functional`, `upds_no_cross_read`
(the corrected `∩ (writes − {f})` form), `fluent_bounds_valid`, `fluent_to_var_inj`, and
`fluent_vars_fresh` (the keystone disjointness of fluent var names from the propositional ones) — plus
theory-level predicates `upds_functional_list`/`upds_no_cross_read_list` and the dest rule
`upds_no_cross_read_listD`. (Deferred to correctness: the §B `INV` bounded-values meta-theorem and
definedness-as-rejection.)

**Next (Task 6 — numeric capstone + lifting; the remaining major effort). Recon complete:**
- Capstone lives in `context tp_nta_reduction_model_checking'` (`TP_NTA_Reduction_Correctness.thy:8773`,
  beside the empty-case `numeric_valid_temp_plan_imp_form_holds`, which is `by blast` via
  `numeric_temp_plan_for_problem_list_impl_int'_imp_prop` + the propositional capstone).
- Propositional capstone `valid_plan_imp_form_holds` (8685, **already structured Isar**) builds the run
  `plan_steps @- goal_run (last plan_steps)` and rests on `all_steps_possible` (8614) =
  **`plan_steps_possible`** (8383 — the bisimulation core, the heavy apply-script) ∧
  `goal_state_conds (last plan_steps)`. Net = `Simple_Network_Impl automata_spec broadcast_spec
  bounds_spec`, `a0 = (init_locs_spec, map_of init_vars_spec, λ_. 0)`.
- **Lifting approach:** numeric net edges are `augment_edge`'d propositional edges (same
  src/tgt/clocks/resets; guard conjoined, updates appended), so a propositional transition lifts to a
  numeric one IFF the numeric guard holds and the numeric updates stay in bounds. So
  `num_plan_steps_possible` = `plan_steps_possible`'s structure + (a) **tracking**: along plan_steps the
  numeric vars equal the abstract valuation `snd (M i)` (Munta `mk_upds` = abstract
  `happening_num_update_set`); (b) numeric guards hold (from `num_valid_state_sequence`'s `sat_comps
  n_pre/n_inv` + `num_goal`); (c) bounds (§B `INV`). Then mirror `valid_plan_imp_form_holds` on
  `Simple_Network_Impl num_timed_automaton_net_spec [] num_all_vars_spec`. `num_valid_plan` from
  `numeric_temp_plan_for_problem_list_impl_int'` instantiated with `set ∘` of the list data.
- **Methodology (per the user, 2026-06-21):** the intermediate states of `plan_steps_possible` are the
  per-step `happening_pre`/`happening_post` invariants relating each config to the abstract state.
  *Before* extending it, **note those states and refactor `plan_steps_possible` into structured Isar**
  (consult the states, surface them as named `have`s) so the numeric tracking threads in cleanly —
  rather than through a brittle apply-chain. This is HANDOVER next-step 5 ("convert the ones you touch
  to Isar first"); `plan_steps_possible` is the first to convert.

Also pending: the deferred `_Spec`→`_Def` rename, and extending the `text`-block comment cleanup (done in
`TP_NTA_Reduction_Spec.thy`) to the other reduction files. jEdit up on `Temporal_Planning_Base` (pid in
`/tmp/jedit-launch.pid`).

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
| `TP_NTA_Reduction` | `TA_Network/` | `Temporal_Planning_Semantics` | `NTA_Temp_Planning_Sem`, `TP_NTA_Reduction_Defs`, `TP_NTA_Reduction_Model_Checking`, `TP_NTA_Reduction_Correctness_{Prelims,Edges,Happenings,Steps}`, `TP_NTA_Reduction_Correctness` (`tp_nta_reduction_correctness`, Thm 1 `valid_plan_imp_form_holds`; also carries the **in-progress numeric forward direction** — locale `numeric_tp_nta_reduction_correctness`; the full per-step run-lifting toolkit is green (keystone `num_step_int_lift`, per-edge `num_data_*_edge`, guard-invariance `sat_comps_happening_num_update_set`, delay/structure `num_steps_delay_replace`/`num_no_urgent`); remaining = the sequencing into `num_plan_steps_possible` + capstone, see the 2026-06-22 handover) | green |
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

- **None — 0 real `sorry`s in the build** (`grep -rn sorry` across `Temporal_Planning_Semantics/`,
  `Temporal_Planning_Common/`, `TA_Network/`, and `Ground_PDDL_Exec_Imp/` returns no matches). The one
  `sorry` token previously listed here sat inside a dead `(* … *)` comment block — an abandoned example
  `global_interpretation` in `Temporal_Plans_Instances.thy`, never kernel-processed — and was deleted
  2026-06-21. The stale `*.thy~` editor backups were removed earlier.

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
2. **Numeric Layers A → C** ([NUMERIC_PLAN.md](NUMERIC_PLAN.md)): **Layer A DONE** (abstract state +
   snap numerics + happening semantics + migration twins, green); the §5 spikes and the §5.5 keystone
   are confirmed. **Layer B (NTA reduction + forward-direction correctness) IN PROGRESS** — net + wf
   locale built, the whole per-step run-lifting toolkit green; remaining = the run-lifting *sequencing*
   (`num_plan_steps_possible`) + capstone (see the 2026-06-22 session note and NUMERIC_PLAN §7 P4).
   **Layer C** (ground-task shape / the grounder's output contract, the §A.3 boundary map, §B bounds,
   §D time-rescaling) is still owed — and is where the hypothesized `INV` bounds + discreteness get
   discharged. NB the reduction is **forward-direction only**, *not* a bisimulation (per the user).
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
