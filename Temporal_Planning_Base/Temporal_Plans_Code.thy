theory Temporal_Plans_Code
imports Temporal_Plans
begin

lemma [code]: "action_defs.mutex_snap_action = (\<lambda> pre adds dels a b. 
  (pre a \<inter> (adds b \<union> dels b) \<noteq> {} \<or> 
  adds a \<inter> dels b \<noteq> {} \<or> 
  pre b \<inter> (adds a \<union> dels a) \<noteq> {} \<or> 
  adds b \<inter> dels a \<noteq> {}))"
  apply (intro ext)
  apply (subst action_defs.mutex_snap_action_def)
  by blast

(* in some cases code theorems need to be pure lambda expressions on the RHS *)
code_thms "action_defs.mutex_snap_action"
end