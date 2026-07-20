(* VENDORED from Formal-PDDL-Semantics/Continuous_Planning/PDDL_Checker_Common.thy.
   Only change vs upstream: the leading import is re-pointed from the Analysis-tainted
   Preservation_Of_Well_Formedness (-> continuous Happening_Semantics -> ODE/Product_Order) to the
   Analysis-free Analysis_Free_Base.Happening_Semantics_Discrete, so the wf-checker the net builder
   uses stays Product_Order-free (this file's body is already Analysis-free -- no euclidean/ODE).
   TODO: trim to the wf-checker slice / upstream into an Analysis-free FPS session. *)
theory PDDL_Checker_Common
  imports
    "Analysis_Free_Base.Happening_Semantics_Discrete"
    Error_Monad_Add
    "HOL-Library.While_Combinator"
    "HOL-Library.Mapping"
    "HOL-Library.Tree"
begin

lemma show_law_literal: "show_law shows_prec (x :: String.literal)"
  unfolding show_law_def Show.shows_prec_literal_def
  by (simp add: shows_string_def)

local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ String.literal}
    @{term "\<lambda>(p :: nat) (s :: String.literal). shows_prec p s"}
    @{thm show_law_literal}
\<close>

derive "show" func object formula  numeric_effect_op 

definition pshowsp_primitive_numeric_expression :: "nat \<Rightarrow> shows primitive_numeric_expression \<Rightarrow> shows" where
"pshowsp_primitive_numeric_expression p x \<equiv> shows ''('' o shows (primitive_numeric_expression.func x) o shows_space 
    o pshowsp_list 0 (primitive_numeric_expression.arguments x) o shows '')''"

definition showsp_primitive_numeric_expression :: 
  "'a showsp \<Rightarrow> nat \<Rightarrow> 'a primitive_numeric_expression \<Rightarrow>  shows"
where
  "showsp_primitive_numeric_expression s p = pshowsp_primitive_numeric_expression p 
    \<circ> (map_primitive_numeric_expression (s p))"

lemma show_law_primitive_numeric_expression[show_law_intros]:
  "(\<And>y. y \<in> set_primitive_numeric_expression x \<Longrightarrow> show_law s y)
   \<Longrightarrow> show_law (showsp_primitive_numeric_expression s) x"
  apply(cases x)
  by (auto simp add: show_law_def showsp_primitive_numeric_expression_def pshowsp_primitive_numeric_expression_def 
      show_law_simps pshowsp_list_def)
  
local_setup \<open>
  Show_Generator.register_foreign_partial_and_full_showsp @{type_name "primitive_numeric_expression"} 0
    @{term "pshowsp_primitive_numeric_expression"}
    @{term "showsp_primitive_numeric_expression"} (SOME @{thm showsp_primitive_numeric_expression_def})
    @{term "map_primitive_numeric_expression"} (SOME @{thm primitive_numeric_expression.map_comp}) 
    [true] @{thm show_law_primitive_numeric_expression}
\<close>

derive "show" primitive_numeric_expression numeric_expression predicate variable type function_decl predicate_decl 


definition pshowsp_atom :: "nat \<Rightarrow> shows atom \<Rightarrow> shows" where
"pshowsp_atom p x \<equiv> shows ''('' o (case x of 
  (predAtm pre args) \<Rightarrow> shows pre o pshowsp_list 0 args
  | (eqAtm l r) \<Rightarrow> shows ''= '' o  l o shows_space o r
  | (numericEqAtm l r) \<Rightarrow> shows ''= '' o  pshowsp_numeric_expression 0 l o shows_space o pshowsp_numeric_expression 0 r
  | (numericLessAtm l r) \<Rightarrow> shows ''< '' o  pshowsp_numeric_expression 0 l o shows_space o pshowsp_numeric_expression 0 r
  | (numericLEAtm l r) \<Rightarrow> shows ''<= '' o  pshowsp_numeric_expression 0 l o shows_space o pshowsp_numeric_expression 0 r
  | (numericGreaterAtm l r) \<Rightarrow> shows ''> '' o  pshowsp_numeric_expression 0 l o shows_space o pshowsp_numeric_expression 0 r
  | (numericGEAtm l r) \<Rightarrow> shows ''>= '' o  pshowsp_numeric_expression 0 l o shows_space o pshowsp_numeric_expression 0 r)  o shows '')''"

definition showsp_atom :: 
  "'a showsp \<Rightarrow> nat \<Rightarrow> 'a atom \<Rightarrow>  shows"
where
  "showsp_atom s p = pshowsp_atom p \<circ> (map_atom (s p))"

lemma show_law_primitive_numeric_expression_p[show_law_intros]:
  "(\<And>y z w. y \<in> set_primitive_numeric_expression x \<Longrightarrow> y (z @ w) = y z @ w) \<Longrightarrow> show_law (pshowsp_primitive_numeric_expression ) x"
  apply(cases x)
  by(auto simp: show_law_def show_law_simps pshowsp_primitive_numeric_expression_def pshowsp_list_def)

lemma show_law_numeric_expression_p[show_law_intros]:
  "(\<And>y z w. y \<in> set_numeric_expression x \<Longrightarrow> y (z @ w) = y z @ w) \<Longrightarrow> show_law (pshowsp_numeric_expression ) x"
  using show_law_primitive_numeric_expression_p
  apply (induction x)
  by(auto simp: show_law_def show_law_simps primitive_numeric_expression.map_ident )


lemma show_law_atom[show_law_intros]:
  "(\<And>y. y \<in> set_atom x \<Longrightarrow> show_law s y)
   \<Longrightarrow> show_law (showsp_atom s) x"
  using show_law_numeric_expression_p[of "map_numeric_expression (s _) _"]
  apply(cases x)
        apply (auto simp add: show_law_def showsp_atom_def pshowsp_atom_def numeric_expression.set_map image_iff 
      show_law_simps pshowsp_list_def )
  by (smt (z3)  shows_prec_append shows_space_append)+

local_setup \<open>
  Show_Generator.register_foreign_partial_and_full_showsp @{type_name "atom"} 0
    @{term "pshowsp_atom"}
    @{term "showsp_atom"} (SOME @{thm showsp_atom_def})
    @{term "map_atom"} (SOME @{thm atom.map_comp}) 
    [true] @{thm show_law_atom}
\<close>

derive "show" atom   numeric_effect ast_effect "term" temporal_annotation  duration_op duration_constraint continuous_effect_op ast_continuous_effect 

definition showsp_ground_action :: 
  "ground_action showsp"
where
  "showsp_ground_action p x = shows ''(GroundAction '' o shows (precondition x) o shows_space o shows (effect x) o shows '')''"

lemma show_law_ground_action[show_law_intros]:
  "show_law showsp_ground_action x"
  by (auto simp add: show_law_def showsp_ground_action_def  show_law_simps)
  
local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ ground_action} @{term "showsp_ground_action"} @{thm show_law_ground_action}
\<close>

derive "show" ground_action

definition showsp_ast_cont_action_schema :: 
  "ast_cont_action_schema showsp"
where
  "showsp_ast_cont_action_schema p x = (case x of 
    (SimpleActionSchema (ActionHead a b) (SimpleActionBody c d)) \<Rightarrow> shows ''(SimpleActionSchema '' o shows a o shows_space o shows b o shows_space o shows c o shows_space o shows d o shows '')'' |
    (ContChangeActionSchema (ActionHead a b) (ContChangeActionBody c d e f)) \<Rightarrow> shows ''(ContChangeActionSchema '' o shows a o shows_space o shows b o shows_space o shows c o shows_space o shows d o shows_space o shows e o shows_space o shows f o shows '')'')"

lemma show_law_ast_cont_action_schema[show_law_intros]:
  "show_law showsp_ast_cont_action_schema x"
  apply(cases x)
  by (auto simp add: show_law_def showsp_ast_cont_action_schema_def  show_law_simps
            split: ast_action_head.splits ast_simple_action_body.splits
                   ast_cont_change_action_body.splits)

local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ ast_cont_action_schema} @{term "showsp_ast_cont_action_schema"} @{thm show_law_ast_cont_action_schema}
\<close>

derive "show" ast_cont_action_schema

definition showsp_ast_cont_domain :: 
  "ast_cont_domain showsp"
where
  "showsp_ast_cont_domain p x = (case x of 
    (Domain a b c d e) \<Rightarrow> shows ''(Domain '' o shows a o shows_space o shows b o shows_space o shows c o shows_space o shows d o shows_space o shows e o shows '')'')"

lemma show_law_ast_cont_domain[show_law_intros]:
  "show_law showsp_ast_cont_domain x"
  apply(cases x)
  by (auto simp add: show_law_def showsp_ast_cont_domain_def show_law_simps)

(*TODO:
local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ ast_cont_domain} @{term "showsp_ast_cont_domain"} @{thm show_law_ast_cont_domain}
\<close>

derive "show" "ast_cont_action_schema ast_domain"

definition showsp_ast_problem :: 
  "ast_problem showsp"
where
  "showsp_ast_problem p x = (case x of 
    (Problem a b c d) \<Rightarrow> shows ''(DurativeActionSchema '' o shows a o shows_space o shows b o shows_space o shows c o shows_space o shows d o shows '')'')"

lemma show_law_ast_problem[show_law_intros]:
  "show_law showsp_ast_problem x"
  apply(cases x)
  by (auto simp add: show_law_def showsp_ast_problem_def  show_law_simps)

local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ ast_problem} @{term "showsp_ast_problem"} @{thm show_law_ast_problem}
\<close>
derive "show"   ast_problem *)

subsection \<open>Generic DFS Reachability Checker\<close>
text \<open>Used for subtype checks\<close>

definition "E_of_succ succ \<equiv> { (u,v). v\<in>set (succ u) }"
lemma succ_as_E: "set (succ x) = E_of_succ succ `` {x}"
  unfolding E_of_succ_def by auto

context
  fixes succ :: "'a \<Rightarrow> 'a list"
begin

  private abbreviation (input) "E \<equiv> E_of_succ succ"


definition "dfs_reachable D w \<equiv>
  let (V,w,brk) = while (\<lambda>(V,w,brk). \<not>brk \<and> w\<noteq>[]) (\<lambda>(V,w,_).
    case w of v#w \<Rightarrow>
    if D v then (V,v#w,True)
    else if v\<in>V then (V,w,False)
    else
      let V = insert v V in
      let w = succ v @ w in
      (V,w,False)
    ) ({},w,False)
  in brk"


context
  fixes w\<^sub>0 :: "'a list"
  assumes finite_dfs_reachable[simp, intro!]: "finite (E\<^sup>* `` set w\<^sub>0)"
begin

  private abbreviation (input) "W\<^sub>0 \<equiv> set w\<^sub>0"

definition "dfs_reachable_invar D V W brk \<longleftrightarrow>
    W\<^sub>0 \<subseteq> W \<union> V
  \<and> W \<union> V \<subseteq> E\<^sup>* `` W\<^sub>0
  \<and> E``V \<subseteq> W \<union> V
  \<and> Collect D \<inter> V = {}
  \<and> (brk \<longrightarrow> Collect D \<inter> E\<^sup>* `` W\<^sub>0 \<noteq> {})"

lemma card_decreases: "
   \<lbrakk>finite V; y \<notin> V; dfs_reachable_invar D V (Set.insert y W) brk \<rbrakk>
   \<Longrightarrow> card (E\<^sup>* `` W\<^sub>0 - Set.insert y V) < card (E\<^sup>* `` W\<^sub>0 - V)"
  apply (rule psubset_card_mono)
  apply (auto simp: dfs_reachable_invar_def)
  done

lemma all_neq_Cons_is_Nil[simp]: (* Odd term remaining in goal \<dots> *)
  "(\<forall>y ys. x2 \<noteq> y # ys) \<longleftrightarrow> x2 = []" by (cases x2) auto

lemma dfs_reachable_correct: "dfs_reachable D w\<^sub>0 \<longleftrightarrow> Collect D \<inter> E\<^sup>* `` set w\<^sub>0 \<noteq> {}"
  unfolding dfs_reachable_def
  apply (rule while_rule[where
    P="\<lambda>(V,w,brk). dfs_reachable_invar D V (set w) brk \<and> finite V"
    and r="Wellfounded.measure (\<lambda>V. card (E\<^sup>* `` (set w\<^sub>0) - V)) <*lex*> Wellfounded.measure length <*lex*> Wellfounded.measure (\<lambda>True\<Rightarrow>0 | False\<Rightarrow>1)"
    ])
  subgoal by (auto simp: dfs_reachable_invar_def)
  subgoal
    apply (auto simp: neq_Nil_conv succ_as_E[of succ] split: if_splits)
    by (auto simp: dfs_reachable_invar_def Image_iff intro: rtrancl.rtrancl_into_rtrancl)
  subgoal by (fastforce simp: dfs_reachable_invar_def dest: Image_closed_trancl)
  subgoal by blast
  subgoal by (auto simp: neq_Nil_conv card_decreases)
  done

end

definition "tab_succ l \<equiv> Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l Mapping.empty)"

lemma Some_eq_map_option [iff]: "(Some y = map_option f xo) = (\<exists>z. xo = Some z \<and> f z = y)"
  by (auto simp add: map_option_case split: option.split)


lemma tab_succ_correct: "E_of_succ (tab_succ l) = set l"
proof -
  have "set (Mapping.lookup_default [] (fold (\<lambda>(u,v). Mapping.map_default u [] (Cons v)) l m) u) = set l `` {u} \<union> set (Mapping.lookup_default [] m u)"
    for m u
    apply (induction l arbitrary: m)
    by (auto
      simp: Mapping.lookup_default_def Mapping.map_default_def Mapping.default_def
      simp: lookup_map_entry' lookup_update' keys_is_none_rep Option.is_none_def
      split: if_splits
    )
  from this[where m=Mapping.empty] show ?thesis
    by (auto simp: E_of_succ_def tab_succ_def lookup_default_empty)
qed

end

lemma finite_imp_finite_dfs_reachable:
  "\<lbrakk>finite E; finite S\<rbrakk> \<Longrightarrow> finite (E\<^sup>*``S)"
  apply (rule finite_subset[where B="S \<union> (Relation.Domain E \<union> Relation.Range E)"])
  apply (auto simp: intro: finite_Domain finite_Range elim: rtranclE)
  done

lemma dfs_reachable_tab_succ_correct: "dfs_reachable (tab_succ l) D vs\<^sub>0 \<longleftrightarrow> Collect D \<inter> (set l)\<^sup>*``set vs\<^sub>0 \<noteq> {}"
  apply (subst dfs_reachable_correct)
  by (simp_all add: tab_succ_correct finite_imp_finite_dfs_reachable)

subsection \<open>Implementation Refinements\<close>

subsubsection \<open>Of-Type\<close>

definition "of_type_impl G oT T \<equiv> (\<forall>pt\<in>set (primitives oT). dfs_reachable G ((=) pt) (primitives T))"


fun ty_term' where
  "ty_term' varT objT (term.VAR v) = varT v"
| "ty_term' varT objT (term.CONST c) = Mapping.lookup objT c"

lemma ty_term'_correct_aux: "ty_term' varT objT t = ty_term varT (Mapping.lookup objT) t"
  by (cases t) auto

lemma ty_term'_correct[simp]: "ty_term' varT objT = ty_term varT (Mapping.lookup objT)"
  using ty_term'_correct_aux by auto

context ast_cont_domain begin

  definition "of_type1 pt T \<longleftrightarrow> pt \<in> subtype_rel\<^sup>* `` set (primitives T)"

  lemma of_type_refine1: "of_type oT T \<longleftrightarrow> (\<forall>pt\<in>set (primitives oT). of_type1 pt T)"
    unfolding of_type_def of_type1_def by auto

  definition "STG \<equiv> (tab_succ (map subtype_edge (types D)))"

  lemma subtype_rel_impl: "subtype_rel = E_of_succ (tab_succ (map subtype_edge (types D)))"
    by (simp add: tab_succ_correct subtype_rel_def)

  lemma of_type1_impl: "of_type1 pt T \<longleftrightarrow> dfs_reachable (tab_succ (map subtype_edge (types D))) ((=)pt) (primitives T)"
    by (simp add: subtype_rel_impl of_type1_def dfs_reachable_tab_succ_correct tab_succ_correct)

  lemma of_type_impl_correct: "of_type_impl STG oT T \<longleftrightarrow> of_type oT T"
    unfolding of_type1_impl STG_def of_type_impl_def of_type_refine1 ..

  definition mp_constT :: "(object, type) mapping" where
    "mp_constT = Mapping.of_alist (consts D)"

  lemma mp_constT_correct[simp]: "Mapping.lookup mp_constT = constT"
    unfolding mp_constT_def constT_def
    by (auto simp: Mapping.lookup_of_alist)


  text \<open>Lifting the subtype-graph through wf-checker\<close>
  context
    fixes ty_ent :: "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
  begin

    definition "is_of_type' stg v T \<longleftrightarrow> (
      case ty_ent v of
        Some vT \<Rightarrow> of_type_impl stg vT T
      | None \<Rightarrow> False)"

    lemma is_of_type'_correct: "is_of_type' STG v T = is_of_type ty_ent v T"
      unfolding is_of_type'_def is_of_type_def of_type_impl_correct ..

    fun wf_pred_atom' where "wf_pred_atom' stg (p,vs) \<longleftrightarrow> 
      (case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) vs Ts)"

    lemma wf_pred_atom'_correct: "wf_pred_atom' STG pvs = wf_pred_atom ty_ent pvs"
      by (cases pvs) (auto simp: is_of_type'_correct[abs_def] split:option.split)

    fun wf_func_args' where "wf_func_args' stg (f,args) \<longleftrightarrow> 
      (case func_sig f of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 (is_of_type' stg) args Ts)"

    lemma wf_func_args'_correct: "wf_func_args' STG fargs = wf_func_args ty_ent fargs"
      by (cases fargs) (auto simp: is_of_type'_correct[abs_def] split:option.split)

fun wf_primitive_numeric_expression' where
"wf_primitive_numeric_expression' stg (PNE f args) \<longleftrightarrow> wf_func_args' stg (f, args)"

lemma wf_primitive_numeric_expression'_correct:
  "wf_primitive_numeric_expression' STG x \<longleftrightarrow> wf_primitive_numeric_expression ty_ent x"
  apply(cases x)
  by (auto simp: is_of_type'_correct[abs_def] split: option.splits)

fun wf_numeric_expression' where
"wf_numeric_expression' stg (ConstantExpr _) \<longleftrightarrow> True" |
"wf_numeric_expression' stg DurationExpr \<longleftrightarrow> True" |
"wf_numeric_expression' stg (AddExpr x y) \<longleftrightarrow> wf_numeric_expression' stg x \<and> wf_numeric_expression' stg y" |
"wf_numeric_expression' stg (SubExpr x y) \<longleftrightarrow> wf_numeric_expression' stg x \<and> wf_numeric_expression' stg y" |
"wf_numeric_expression' stg (MulExpr x y) \<longleftrightarrow> wf_numeric_expression' stg x \<and> wf_numeric_expression' stg y" |
"wf_numeric_expression' stg (DivExpr x y) \<longleftrightarrow> wf_numeric_expression' stg x \<and> wf_numeric_expression' stg y" |
"wf_numeric_expression' stg (SinExpr x) \<longleftrightarrow> wf_numeric_expression' stg x" |
"wf_numeric_expression' stg (CosExpr x) \<longleftrightarrow> wf_numeric_expression' stg x" |
"wf_numeric_expression' stg (ExpExpr x) \<longleftrightarrow> wf_numeric_expression' stg x" |
"wf_numeric_expression' stg PiExpr \<longleftrightarrow> True" |
"wf_numeric_expression' stg (FunctionExpr p) \<longleftrightarrow> wf_primitive_numeric_expression' stg p"

lemma wf_numeric_expression'_correct:
  "wf_numeric_expression' STG e \<longleftrightarrow> wf_numeric_expression ty_ent e"
  apply(induction e)
  by (auto simp: wf_primitive_numeric_expression'_correct)


    fun wf_atom' :: "_ \<Rightarrow> 'ent atom \<Rightarrow> bool" where
      "wf_atom' stg (atom.predAtm p vs) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_atom' stg (atom.eqAtm a b) = (ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None)"
    | "wf_atom' stg (numericEqAtm a b) \<longleftrightarrow> wf_numeric_expression' stg a \<and> wf_numeric_expression' stg b"
    | "wf_atom' stg (numericLessAtm a b) \<longleftrightarrow> wf_numeric_expression' stg a \<and> wf_numeric_expression' stg b"
    | "wf_atom' stg (numericLEAtm a b) \<longleftrightarrow> wf_numeric_expression' stg a \<and> wf_numeric_expression' stg b"
    | "wf_atom' stg (numericGreaterAtm a b) \<longleftrightarrow> wf_numeric_expression' stg a \<and> wf_numeric_expression' stg b"
    | "wf_atom' stg (numericGEAtm a b) \<longleftrightarrow> wf_numeric_expression' stg a \<and> wf_numeric_expression' stg b"

    lemma wf_atom'_correct: "wf_atom' STG a = wf_atom ty_ent a"
      by (cases a) (auto simp: wf_pred_atom'_correct is_of_type'_correct[abs_def] wf_numeric_expression'_correct 
                         split: option.splits)

    fun wf_fmla' :: "_ \<Rightarrow> ('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla' stg (Atom a) \<longleftrightarrow> wf_atom' stg a"
    | "wf_fmla' stg \<bottom> \<longleftrightarrow> True"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla' stg \<phi>1 \<and> wf_fmla' stg \<phi>2)"
    | "wf_fmla' stg (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla' stg \<phi>"

    lemma wf_fmla'_correct: "wf_fmla' STG \<phi> \<longleftrightarrow> wf_fmla ty_ent \<phi>"
      by (induction \<phi> rule: wf_fmla.induct) (auto simp: wf_atom'_correct)

    fun wf_fmla_atom1' where
      "wf_fmla_atom1' stg (Atom (predAtm p vs)) \<longleftrightarrow> wf_pred_atom' stg (p,vs)"
    | "wf_fmla_atom1' stg _ \<longleftrightarrow> False"

    lemma wf_fmla_atom1'_correct: "wf_fmla_atom1' STG \<phi> = wf_fmla_atom ty_ent \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) (auto
        simp: wf_atom'_correct is_of_type'_correct[abs_def] split: option.splits)



fun wf_numeric_effect' where
    "wf_numeric_effect' stg (NumericEffect _ l r) \<longleftrightarrow>
      wf_primitive_numeric_expression' stg l \<and>
      wf_numeric_expression' stg r"

lemma wf_numeric_effect'_correct:
  "wf_numeric_effect' STG ne \<longleftrightarrow> wf_numeric_effect ty_ent ne"
  apply(cases ne)
  by (auto simp: wf_primitive_numeric_expression'_correct wf_numeric_expression'_correct)

    fun wf_effect' where
      "wf_effect' stg (Effect a d nes) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom1' stg ae)
        \<and> (\<forall>de\<in>set d.  wf_fmla_atom1' stg de)
        \<and> (\<forall>ne\<in>set nes. wf_numeric_effect' stg ne)"

    lemma wf_effect'_correct: "wf_effect' STG e = wf_effect ty_ent e"
      by (cases e) (auto simp: wf_fmla_atom1'_correct wf_numeric_effect'_correct)

fun wf_continuous_effect' where
"wf_continuous_effect' stg (ContinuousEffect cop l r) \<longleftrightarrow>
  wf_primitive_numeric_expression' stg l \<and> wf_numeric_expression' stg r" 

lemma wf_continuous_effect'_correct:
  "wf_continuous_effect' STG e \<longleftrightarrow> wf_continuous_effect ty_ent e"
  apply(cases e)
  by (auto simp: wf_primitive_numeric_expression'_correct wf_numeric_expression'_correct)

fun wf_duration_const' :: "_ \<Rightarrow> 'ent duration_constraint \<Rightarrow> bool" where
      "wf_duration_const' stg (DurationConstraint operator r) \<longleftrightarrow> wf_numeric_expression' stg r"

    lemma wf_duration_const'_correct: "wf_duration_const' STG d = wf_duration_const ty_ent d"
      by (cases d) (auto simp: wf_numeric_expression'_correct[abs_def] split:option.split)

  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>

fun wf_cont_action_schema' :: "_ \<Rightarrow> _ \<Rightarrow> ast_cont_action_schema \<Rightarrow> bool" where
    "wf_cont_action_schema' stg conT (SimpleActionSchema (ActionHead n params) (SimpleActionBody pre eff)) \<longleftrightarrow> (
      let
        tyv = ty_term' (map_of params) conT
      in
        distinct (map fst params)
      \<and> wf_fmla' tyv stg pre
      \<and> wf_effect' tyv stg eff)"
  | "wf_cont_action_schema' stg conT (ContChangeActionSchema (ActionHead n params) (ContChangeActionBody d cond eff cont_eff)) \<longleftrightarrow> (
      let
        tyv = ty_term' (map_of params) conT
      in
        distinct (map fst params)
      \<and> (\<forall>(t,c) \<in> set cond. wf_fmla' tyv stg c)
      \<and> (\<forall>(t,e) \<in> set eff. wf_effect' tyv stg e \<and> t \<noteq> Over_All)
      \<and> (\<forall>e \<in> set cont_eff. wf_continuous_effect' tyv stg e)
      \<and> (\<forall>(t, c) \<in> set d.  (t = At_Start \<or> t = At_End) \<and> wf_duration_const' tyv stg c))"

lemma wf_cont_action_schema'_correct: "wf_cont_action_schema' STG mp_constT s = wf_cont_action_schema s"
proof(cases s)
  case (SimpleActionSchema x11 x12)
  then show ?thesis
    by (cases x11; cases x12) 
        (auto simp: wf_fmla'_correct wf_effect'_correct wf_duration_const'_correct Let_def 
                    wf_continuous_effect'_correct 
             split: option.splits)
next
  case (ContChangeActionSchema x21 x22)
  then show ?thesis
    by (cases x21; cases x22) 
        (auto simp: wf_fmla'_correct wf_effect'_correct wf_duration_const'_correct Let_def 
                    wf_continuous_effect'_correct 
             split: option.splits)
qed

  definition wf_cont_domain' :: "_ \<Rightarrow> _ \<Rightarrow> bool" where
    "wf_cont_domain' stg conT \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map (function_decl.func) (functions D))
    \<and> (\<forall>f\<in>set (functions D). wf_function_decl f)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type T)
    \<and> distinct (map ast_cont_action_schema_name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_cont_action_schema' stg conT a)
    "

  lemma wf_domain'_correct: "wf_cont_domain' STG mp_constT = wf_cont_domain"
    unfolding wf_cont_domain_def wf_cont_domain'_def
    by (auto simp: wf_cont_action_schema'_correct wf_domain_signature_def)

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>

subsubsection \<open>Ground Action Interference \& Application of Effects\<close>

lemma fold_set_remove: "fold Set.remove xs s = s - set xs"
    by (induction xs arbitrary: s) auto

lemma fold_set_insert: "fold Set.insert xs s = s \<union> set xs"
  by (induction xs arbitrary: s) auto

context ast_cont_problem begin

  text \<open>Implementation of executable refinements for @{const acts_non_intrf} 
  \& @{const apply_ground_actions}\<close>

  text \<open>a list of simulataneous \& non-interfering grounded actions are all applied at once\<close>
  fun apply_ground_actions_exec :: "ground_action list \<Rightarrow> world_model \<Rightarrow> world_model" where
    "apply_ground_actions_exec A\<^sub>i s = 
      ((let 
        adds = (concat o (map (adds o effect))) A\<^sub>i; 
        dels = (concat o (map (dels o effect))) A\<^sub>i in 
        fold Set.insert adds (fold Set.remove dels (fst s))),
        action_list_numeric_update_function A\<^sub>i (snd s))"

  text \<open>Justification of refinement for @{const apply_ground_actions}\<close>
  lemma apply_happ_exec_refine: "apply_ground_actions_exec h s = apply_ground_actions h s"
    by (auto simp: fold_set_remove fold_set_insert)
end

subsubsection \<open>Well-Formedness\<close>

context ast_cont_problem begin

  text \<open> We start by defining a mapping from objects to types. The container
    framework will generate efficient, red-black tree based code for that
    later. \<close>

  type_synonym objT = "(object, type) mapping"

  definition mp_objT :: "(object, type) mapping" where
    "mp_objT = Mapping.of_alist (consts D @ objects P)"

  lemma mp_objT_correct[simp]: "Mapping.lookup mp_objT = objT"
    unfolding mp_objT_def objT_alt
    by (auto simp: Mapping.lookup_of_alist)

  text \<open>We refine the typecheck to use the mapping\<close>

  definition "is_obj_of_type_impl stg mp n T = (
    case Mapping.lookup mp n of None \<Rightarrow> False | Some oT \<Rightarrow> of_type_impl stg oT T
  )"

  lemma is_obj_of_type_impl_correct[simp]:
    "is_obj_of_type_impl STG mp_objT = is_obj_of_type"
    apply (intro ext)
    apply (auto simp: is_obj_of_type_impl_def is_obj_of_type_def of_type_impl_correct split: option.split)
    done

fun wf_func_assign' :: "objT \<Rightarrow> _ \<Rightarrow> object atom formula \<Rightarrow> bool" where
    "wf_func_assign' ot stg (Atom (numericEqAtm (FunctionExpr (PNE f args)) (ConstantExpr r))) 
      \<longleftrightarrow> wf_func_args' (Mapping.lookup ot) stg (f,args)"
  | "wf_func_assign' ot stg _ \<longleftrightarrow> False"

lemma wf_func_asign'_correct[simp]: "wf_func_assign' mp_objT STG f = wf_func_assign f"
    apply (cases   f rule: wf_func_assign.cases) 
                      apply(auto simp: wf_func_args'_correct[abs_def])
  subgoal for l r
    apply(cases l)
    by(auto simp: wf_func_args'_correct[abs_def] 
            simp del: wf_func_args.simps wf_func_args'.simps 
            split: option.splits)
  subgoal for l r
    apply(cases l)
    by(auto simp: wf_func_args'_correct[abs_def] 
            simp del: wf_func_args.simps wf_func_args'.simps 
            split: option.splits)
  done

  text \<open>We refine the well-formedness checks to use the mapping\<close>

  definition wf_fact' :: "objT \<Rightarrow> _ \<Rightarrow> fact \<Rightarrow> bool" where
    "wf_fact' ot stg \<equiv> wf_pred_atom' (Mapping.lookup ot) stg"

  lemma wf_fact'_correct[simp]: "wf_fact' mp_objT STG = wf_fact"
    by (auto simp: wf_fact'_def wf_fact_def wf_pred_atom'_correct[abs_def])


  definition "wf_fmla_atom2' mp stg f
    = (case f of formula.Atom (predAtm p vs) \<Rightarrow> (wf_fact' mp stg (p,vs)) | _ \<Rightarrow> False)"

  lemma wf_fmla_atom2'_correct[simp]:
    "wf_fmla_atom2' mp_objT STG \<phi> = wf_fmla_atom objT \<phi>"
    apply (cases \<phi> rule: wf_fmla_atom.cases)
    by (auto simp: wf_fmla_atom2'_def wf_fact_def split: option.splits)

  definition "wf_cont_problem' stg conT mp \<equiv>
      wf_cont_domain' stg conT
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> (\<forall>f\<in>set (init P). wf_fmla_atom2' mp stg f \<or> wf_func_assign' mp stg f)
    \<and> wf_fmla' (Mapping.lookup mp) stg (goal P)"

  lemma wf_cont_problem'_correct:
    "wf_cont_problem' STG mp_constT mp_objT = wf_cont_problem"
    unfolding wf_cont_problem_def wf_cont_problem'_def wf_problem_signature_def
    by (auto simp: wf_domain'_correct wf_fmla'_correct wf_cont_domain_def)

  text \<open>Instantiating actions will yield well-founded effects.
    Corollary of @{thm wf_inst_simple_action_schema} 
             and @{thm wf_inst_cont_change_action_schema}.\<close>

  lemma wf_effect_inst_weak:
    fixes h b
    defines "a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a \<equiv> SimpleActionSchema h b"  
    assumes "a = instantiate_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a args" 
        and "action_params_match h args" 
        and "wf_cont_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
    shows "wf_effect_inst (effect a)"
    using assms wf_inst_simple_action_schema[of h args b]
    by (cases h; cases b)
       (auto simp: wf_effect_inst_alt Let_def)

  lemma wf_effect_durative_inst_weak:
    fixes h b
    defines "a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a \<equiv> ContChangeActionSchema h b"  
    assumes "a = inst_snap_action a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a dur args ta" 
        and "action_params_match h args" 
        and "wf_cont_action_schema a\<^sub>s\<^sub>c\<^sub>h\<^sub>e\<^sub>m\<^sub>a"
    shows "wf_effect_inst (effect a)"
    using assms wf_inst_cont_change_action_schema[of h args b]
    by  (cases h; cases b) (auto simp: wf_effect_inst_alt Let_def)

end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

text \<open>[vendored slice] The happening-execution / induced-sequence PLAN-VALIDATION lemmas and the
  numeric PNE-enumeration lemmas (upstream PDDL_Checker_Common lines ~621-2837, which depend on
  Preservation_Of_Well_Formedness) are omitted here: the net builder needs only the well-formedness
  checker below, not the plan-validation checker.\<close>

definition "check_all_list P l msg msgf \<equiv>
  forallM (\<lambda>x. check (P x) (\<lambda>_::unit. shows msg o shows '': '' o msgf x) ) l <+? snd"

lemma check_all_list_return_iff[return_iff]: "check_all_list P l msg msgf = Inr () \<longleftrightarrow> (\<forall>x\<in>set l. P x)"
  unfolding check_all_list_def by (induction l) (auto)

definition "check_wf_types D \<equiv> do {
  check_all_list (\<lambda>(_,t). t=STR ''object'' \<or> t\<in>fst`set (types D)) (types D) ''Undeclared supertype'' (shows o snd)
}"



lemma  check_wf_types_return_iff[return_iff]: "check_wf_types D = Inr () \<longleftrightarrow> domain_signature.wf_types (types D)"
  unfolding domain_signature.wf_types_def check_wf_types_def by (force simp: return_iff)

definition "check_wf_cont_domain D stg conT \<equiv> do {
  check_wf_types D;
  check (distinct (map (predicate_decl.pred) (predicates D))) (ERRS ''Duplicate predicate declaration'');
  check_all_list (domain_signature.wf_predicate_decl (types D)) (predicates D) ''Malformed predicate declaration'' (shows o predicate.name o predicate_decl.pred);
  check (distinct (map (function_decl.func) (functions D))) (ERRS ''Duplicate function declaration'');
  check_all_list (domain_signature.wf_function_decl (types D)) (functions D) ''Malformed function declaration'' (shows o func.name o function_decl.func);
  check (distinct (map fst (consts D))) (ERRS ''Duplicate constant declaration'');
  check (\<forall>(n,T)\<in>set (consts D). domain_signature.wf_type (types D) T) (ERRS ''Malformed type'');
  check (distinct (map ast_cont_action_schema_name (actions D))  ) (ERRS ''Duplicate action name'');
  check_all_list (ast_cont_domain.wf_cont_action_schema' D stg conT) (actions D) ''Malformed action'' (shows o ast_cont_action_schema_name)
}"

lemma check_wf_cont_domain_return_iff[return_iff]:
  "check_wf_cont_domain D stg conT = Inr () \<longleftrightarrow> ast_cont_domain.wf_cont_domain' D stg conT"
proof -
  interpret ast_cont_domain D .
  show ?thesis
    unfolding check_wf_cont_domain_def wf_cont_domain'_def by (auto simp: return_iff)
qed

definition "prepend_err_msg msg e \<equiv> \<lambda>_::unit. shows msg o shows '': '' o e ()"

definition "check_wf_cont_problem P \<equiv> do {
  let D = ast_problem.domain P;
  let stg = ast_cont_problem.STG P;
  let conT = ast_cont_problem.mp_constT P;
  let mp = ast_cont_problem.mp_objT P;
  check_wf_cont_domain D stg conT <+? prepend_err_msg ''Domain not well-formed'';
  check (distinct (map fst (objects P) @ map fst (consts D))) (ERRS ''Duplicate object declaration'');
  check ((\<forall>(n,T)\<in>set (objects P). domain_signature.wf_type (types D) T)) (ERRS ''Malformed type'');
  check (distinct (init P)) (ERRS ''Duplicate fact in initial state'');
  check (\<forall>f\<in>set (init P). ast_cont_problem.wf_fmla_atom2' P mp stg f \<or> ast_cont_problem.wf_func_assign' P mp stg f) (ERRS ''Malformed formula in initial state'');
  check (ast_cont_domain.wf_fmla' D (Mapping.lookup mp) stg (goal P)) (ERRS ''Malformed goal formula'')
}"

lemma check_wf_problem_return_iff[return_iff]:
  "check_wf_cont_problem P = Inr () \<longleftrightarrow> ast_cont_problem.wf_cont_problem P"
proof -
  interpret ast_cont_problem P .
  show ?thesis
    using wf_cont_problem'_correct
    by (auto simp: return_iff wf_cont_problem'_def wf_cont_problem_def check_wf_cont_problem_def Let_def)  
qed


lemmas wf_domain_code =
  domain_signature.sig_def
  domain_signature.wf_types_def
  domain_signature.wf_type.simps
  domain_signature.wf_predicate_decl.simps
  ast_cont_domain.STG_def
  ast_cont_domain.is_of_type'_def
  ast_cont_domain.wf_atom'.simps
  ast_cont_domain.wf_pred_atom'.simps
  ast_cont_domain.wf_fmla'.simps
  ast_cont_domain.wf_fmla_atom1'.simps
  ast_cont_domain.wf_effect'.simps
  ast_cont_domain.wf_cont_action_schema'.simps
  ast_cont_domain.wf_cont_domain'_def
  subst_term.simps
  ast_cont_domain.mp_constT_def
  (* my new function *)
  domain_signature.wf_function_decl.simps
  domain_signature.func_sig_def
  ast_cont_domain.wf_func_args'.simps
  ast_cont_domain.wf_duration_const'.simps
  ast_cont_domain.wf_numeric_expression'.simps
  ast_cont_domain.wf_continuous_effect'.simps 
  ast_cont_domain.wf_numeric_effect'.simps
  ast_cont_domain.wf_primitive_numeric_expression'.simps
  inst_duration_in_ast_effect.simps
  inst_duration_in_atom.simps
  inst_duration_in_numeric_expression.simps
  inst_duration_in_numeric_effect.simps
  inst_duration_in_continuous_effect.simps
  acts_non_intrf_def
  (*ast_domain.apply_happ.simps*)

declare wf_domain_code[code]

lemmas wf_problem_code =
  ast_cont_problem.wf_cont_problem'_def
  ast_cont_problem.wf_fact'_def
  problem_signature.is_obj_of_type_alt
  problem_signature.wf_fact_def
  action_instantiations.wf_plan_action.simps
  ast_cont_domain.subtype_edge.simps


declare wf_problem_code[code]

text \<open>[vendored slice] The \<open>check_code_common\<close> [code] bundle (plan-validation code equations:
  res_inst / htps_exec / simplify_plan / AVL-tree ops / PNE enumeration) is omitted with the
  validation checker above -- only the well-formedness [code] bundles (wf_domain_code / wf_problem_code)
  are kept, which is all the net builder's check_and_make_network needs.\<close>

subsubsection \<open>More Efficient Distinctness Check for Linorders\<close>
(* TODO: Can probably be optimized even more. *)
fun no_stutter :: "'a list \<Rightarrow> bool" where
  "no_stutter [] = True"
| "no_stutter [_] = True"
| "no_stutter (a#b#l) = (a\<noteq>b \<and> no_stutter (b#l))"

lemma sorted_no_stutter_eq_distinct: "sorted l \<Longrightarrow> no_stutter l \<longleftrightarrow> distinct l"
  apply (induction l rule: no_stutter.induct)
  apply (auto simp: )
  done

definition distinct_ds :: "'a::linorder list \<Rightarrow> bool"
  where "distinct_ds l \<equiv> no_stutter (quicksort l)"

lemma [code_unfold]: "distinct = distinct_ds"
  apply (intro ext)
  unfolding distinct_ds_def
  using sorted_no_stutter_eq_distinct[OF linorder_class.sorted_quicksort]
  by (metis distinct_sort sort_quicksort)

subsubsection \<open>Parsing Rational Numbers\<close>

type_synonym digit = nat

text\<open>Well-formedness conditions for a digit and a sequence of digits.\<close>
definition "wf_digit d \<longleftrightarrow> d < 10" 
text\<open>A sequence of digits is well-formed iff it is normalized and only contains well-formed digits.\<close>
definition "wf_digits ds \<longleftrightarrow> (\<forall>d \<in> set ds. wf_digit d)"

text\<open>Functions to trim leading and trailing zeros.\<close>

fun trim_ld_zs :: "digit list \<Rightarrow> digit list" where
  "trim_ld_zs [] = []"
| "trim_ld_zs (d#ds) = 
  (if d = 0 then trim_ld_zs ds else d#ds)"

lemma tlz_hd_neq_z: "trim_ld_zs ds = ds' \<Longrightarrow> hd ds' \<noteq> 0 \<or> ds' = []"
  by (induction ds) auto

lemma trim_ld_zs_idem: "trim_ld_zs (trim_ld_zs ds) = trim_ld_zs ds"
  by (induction ds) auto

lemma trim_ld_zs_wf: "wf_digits ds \<Longrightarrow> wf_digits (trim_ld_zs ds)"
  unfolding wf_digits_def by (induction ds) auto

lemma trim_ld_zs_app: "trim_ld_zs (ds1 @ ds2) = (trim_ld_zs ds1) @ ds2 \<or> (\<forall>d \<in> set ds1. d = 0)"
  by (induction ds1) auto

fun trim_tr_zs' :: "digit list \<Rightarrow> digit list \<Rightarrow> digit list" where
  "trim_tr_zs' [] zs = []"
| "trim_tr_zs' (d#ds) zs = 
  (if d = 0 then trim_tr_zs' ds (0#zs)
  else zs @ d # (trim_tr_zs' ds []))"

fun trim_tr_zs :: "digit list \<Rightarrow> digit list" where
  "trim_tr_zs ds = trim_tr_zs' ds []"

lemma ttz_last_neq_z_aux: 
  assumes "trim_tr_zs' ds zs = ds'" 
  shows "last ds' \<noteq> 0 \<or> ds' = []"
  using assms
proof (induction ds arbitrary: ds' zs)
  case Nil
  then show ?case by auto
next
  case (Cons d ds)
  then show ?case
    by (cases "d = 0") force+
qed

lemma ttz_last_neq_z: "trim_tr_zs ds = ds' \<Longrightarrow> last ds' \<noteq> 0 \<or> ds' = []"
  using ttz_last_neq_z_aux by (auto simp: Let_def split: if_splits)

lemma trim_tr_zs'_wf: "wf_digits ds \<and> wf_digits zs \<Longrightarrow> wf_digits (trim_tr_zs' ds zs)"
  unfolding wf_digits_def by (induction ds zs rule: trim_tr_zs'.induct) auto

lemma trim_tr_zs_wf: "wf_digits ds \<Longrightarrow> wf_digits (trim_tr_zs ds)"
  using trim_tr_zs'_wf[where zs="[]"] by (auto simp: wf_digits_def)

text\<open>Functions to convert between integers and a sequence of digits.\<close>

fun int_of_digits :: "digit list \<Rightarrow> int \<Rightarrow> int" where
  "int_of_digits [] acc = acc"
| "int_of_digits (d#ds) acc = int_of_digits ds (acc * 10 + d)"

fun digits_of_int :: "int \<Rightarrow> digit list" where
  "digits_of_int i = 
    (if i \<le> 0 then []
    else if i < 10 then [nat i]
    else digits_of_int (i div 10) @ [nat (i mod 10)])"

value "digits_of_int (int_of_digits [1,2,3,4] 0)"
value "int_of_digits (digits_of_int 1234) 0"

value "digits_of_int (int_of_digits [1] 123)"

lemma digits_of_int_int_of_digits_aux:
  assumes "acc > 0" and "\<forall>d \<in> set ds. wf_digit d"
  shows "digits_of_int (int_of_digits ds acc) = digits_of_int acc @ ds"
  using assms
  by (induction ds acc arbitrary: acc rule: int_of_digits.induct) (auto simp: wf_digit_def)

text\<open>Proof for correctness of function @{const int_of_digits} and @{const digits_of_int}.\<close>
lemma digits_of_int_int_of_digits:
  assumes "wf_digits ds"
  shows "digits_of_int (int_of_digits ds 0) = trim_ld_zs ds"
  using assms digits_of_int_int_of_digits_aux
proof (induction ds)
  case Nil
  then show ?case by auto
next
  case (Cons d ds)
  then show ?case
    by (cases "d = 0") (auto simp: wf_digits_def wf_digit_def)
qed

text\<open>Function to convert from a sequences of digits to a rational number.\<close>
primrec rat_of_digits_pair :: "digit list \<times> digit list \<Rightarrow> rat" where
  "rat_of_digits_pair (ds\<^sub>1,ds\<^sub>2) = (
    let ds\<^sub>1' = trim_ld_zs ds\<^sub>1; ds\<^sub>2' = trim_tr_zs ds\<^sub>2 in
      Rat.Fract (int_of_digits (ds\<^sub>1' @ ds\<^sub>2') 0) (10 ^ length ds\<^sub>2')
  )"

text\<open>For proofs about the function @{const rat_of_digits_pair} see \texttt{Rat\_Parsing.thy}.\<close>
end