theory Numeric_Bound_Inference_Code_Export
  imports Numeric_Bound_Inference_Extract
begin

text \<open>\<^bold>\<open>A2 -- compute-side code export.\<close> Emit the threshold interval bound-inference entry points to
  SML (module @{text NumericBoundInference}) for the @{text plan_cert} bound-inference glue. The inferred
  box crosses to the reduction as plain @{typ int} data; the reduction re-checks it with @{text \<open>is_gbound_inv'\<close>}.

  Entry points: @{const infer_fluent_bounds} (threshold interval AI \<rightarrow> finite @{typ int} box, or @{term None}
  on an infinite endpoint) and @{const thr_set} (the threshold constant set fed to it). The SML glue
  constructs the gaction-list / valuation / fluent-list inputs (instantiating the fluent type @{text \<open>'n\<close>}
  to @{text \<open>String.literal\<close>}, the func name) by projecting the reduction's @{text numeric_draft_actions}
  export, calls @{const infer_fluent_bounds}, and reads back the box.\<close>

export_code
  infer_fluent_bounds
  thr_set
  ginfer_thr
  NConst NVar NAdd NSub NMul NDiv
  GCmp CEq CLe CGe CLt CGt
  nat_of_integer integer_of_nat int_of_integer integer_of_int
  in SML module_name NumericBoundInference file_prefix Numeric_Bound_Inference

end
