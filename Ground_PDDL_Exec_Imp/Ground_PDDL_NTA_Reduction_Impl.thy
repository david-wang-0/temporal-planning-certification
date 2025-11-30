theory Ground_PDDL_NTA_Reduction_Impl
  imports Ground_PDDL_NTA_Reduction_Correctness 
    "Temporal_AI_Planning_Languages_Semantics.TEMPORAL_PDDL_Checker"
begin


lemmas return_iff = return_iff check_all_list_return_iff check_wf_problem_return_iff


lemma context_bind_return_iff[return_iff]:
  "(m \<bind> f = Inr y) = (\<exists>x. m = Inr x \<and> (m = Inr x \<longrightarrow> f x = Inr y))"
  apply (subst return_iff)
  by auto

lemma context_bind_return_iff'[return_iff]:
  "(m \<bind> f = Inr y) = (\<exists>x P. m = Inr x \<and> (m = Inr x \<longleftrightarrow> P) \<and> (P \<longrightarrow> f x = Inr y))"
  apply (subst context_bind_return_iff)
  by simp

lemma mapM_return_iff[return_iff]: "mapM f xs = Inr ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = Inr y) xs ys"
proof (rule iffI)
  assume a: "mapM f xs = Inr ys"
  have len: "length xs = length ys" using a mapM_return by fastforce
  show "list_all2 (\<lambda>x y. f x = Inr y) xs ys"
  proof (rule list_all2_all_nthI[OF len])
    fix n
    assume n: "n < length xs" 
    have ys: "ys = map (projr \<circ> f) xs" 
      and xs_r: "(\<forall>x\<in>set xs. \<forall>e. f x \<noteq> Inl e)" using a[THEN mapM_return] by blast+
    obtain r where
        xs_n_inr: "f (xs ! n) = Inr r" using xs_r n apply (cases "f (xs ! n)") by auto
    have "ys ! n = r" using xs_n_inr ys unfolding comp_def using n by simp
    thus "f (xs ! n) = Inr (ys ! n)" using xs_n_inr by simp
  qed
next
  assume a: "list_all2 (\<lambda>x y. f x = Inr y) xs ys"
  thus "mapM f xs = Inr ys"
    by (induction rule: list_all2_induct) auto
qed


lemma list_all2_return_if:
  assumes "list_all P xs"
      and "\<And>x y. P x \<Longrightarrow> fM x = Inr y \<longleftrightarrow> f x = y"
    shows "list_all2 (\<lambda>x y. fM x = Inr y) xs ys = (ys = map f xs)"
  unfolding list_all2_conv_all_nth
proof (intro iffI strip conjI; (elim conjE)?)
  assume len: "length xs = length ys" 
    and i: "\<forall>i<length xs. fM (xs ! i) = Inr (ys ! i)"
  have nth_eq: "\<forall>i < length xs. ys ! i = f (xs ! i)" using i assms unfolding list_all_iff by simp
  show "ys = map f xs" apply (subst list_eq_iff_nth_eq)
    using len nth_eq by auto 
next
  show "ys = map f xs \<Longrightarrow> length xs = length ys" by simp
next
  fix i
  assume ys: "ys = map f xs"
    and i: "i < length xs"
  show "fM (xs ! i) = Inr (ys ! i)"
    using assms ys i unfolding list_all_iff by auto
qed

text \<open>We need to refine some datatypes\<close>

find_theorems "finite ?x \<Longrightarrow> inj ?f \<Longrightarrow> finite ?y"
find_theorems name: "infinite*UNIV"

lemma UNIV_predicate:
  "(UNIV::predicate set) = Pred ` (UNIV::String.literal set)"
  apply (intro equalityI subsetI UNIV_I)
  subgoal for x
    unfolding UNIV_def 
    apply (cases x)
    by blast
  done

lemma inifinite_UNIV_literalI:
  "infinite (UNIV::String.literal set)"
proof (rule notI)
  assume "finite (UNIV::String.literal set)"
  moreover
  have "inj (\<lambda>l::String.literal. (STR ''x'') + l)"
    apply (rule injI)
    apply (subst (asm) String.add_literal_code)+
    using String.Literal_eq_iff by simp
  ultimately
  have "surj (\<lambda>l::String.literal. (STR ''x'') + l)"
    using finite_UNIV_inj_surj by blast
  then obtain s where "STR '''' = STR ''x'' + s" by (rule surjE)
  thus False by (simp add: String.add_literal_code String.Literal_eq_iff)
qed


find_theorems "infinite (?f ` ?x)"

lemma range_inj_infinite:
  assumes "infinite S"
      and "inj f"
    shows "infinite (f ` S)"
proof
  assume a: "finite (f ` S)"
  have "f -` (f ` S) = S" using \<open>inj f\<close> inj_vimage_image_eq by simp
  moreover
  have "finite (f -` (f ` S))" using finite_vimageI a \<open>inj f\<close> by blast
  ultimately
  have "finite S" by auto
  with \<open>infinite S\<close>
  show False by simp
qed

lemma infinite_UNIV_predicateI:
  "infinite (UNIV::predicate set)"
  apply (subst UNIV_predicate)
  apply (rule range_inj_infinite)
   apply (rule inifinite_UNIV_literalI)
  apply (rule injI)
  by blast

instantiation predicate :: card_UNIV
begin 
definition "finite_UNIV = Phantom(predicate) False"
definition "card_UNIV = Phantom(predicate) 0"
instance by intro_classes (simp_all add: finite_UNIV_predicate_def card_UNIV card_UNIV_predicate_def infinite_UNIV_predicateI)
end

find_theorems name: "proper_int*char"

find_theorems name: "ord*list"

find_theorems name: "less*liter"

find_theorems "List.ord.lexordp"

instantiation String.literal :: proper_interval
begin
fun list_less_one::"char list \<Rightarrow> char list \<Rightarrow> bool" where
"list_less_one _ [] = False" |
"list_less_one [] (y#ys) = ((of_char (CHR 0x00)::nat) < (of_char y) \<or> length ys > 0)" |
"list_less_one (x#xs) (y#ys) = (
  if (x = y) then list_less_one xs ys
  else if ((of_char y::nat) < of_char x) then False
  else True
)"


  

lemma list_less_one_induct_cases:
  assumes "(\<And>xs. P xs [])" 
    and "(\<And>y ys. P [] (y # ys))"
    and "(\<And>x xs y ys. x = y \<Longrightarrow> P xs ys \<Longrightarrow> P (x # xs) (y # ys))" 
    and "(\<And>x xs y ys. (of_char y::nat) < of_char x \<Longrightarrow> P (x # xs) (y # ys))" 
    and "(\<And>x xs y ys. (of_char x::nat) < of_char y \<Longrightarrow> P (x # xs) (y # ys))" 
  shows "P xs ys"
  apply (induction rule: list_less_one.induct)
    apply (use assms in simp)
   apply (use assms in simp)
  subgoal for x _ y
    apply (cases "(of_char y::nat) < of_char x"; cases "(of_char x::nat) < of_char y")
    using assms by auto
  done


fun proper_interval_literal::"String.literal option \<Rightarrow> String.literal option \<Rightarrow> bool" where
"proper_interval_literal None None = True" |
"proper_interval_literal (Some s) None = True" |
"proper_interval_literal None (Some s) = (s \<noteq> (STR ''''))" |
"proper_interval_literal (Some s) (Some t) = (list_less_one (literal.explode s) (literal.explode t))"

lemma valid_char_ran: "(of_char c::nat) > of_char (CHR 0x7F) \<longleftrightarrow> digit7 c"
  apply (cases c)
  subgoal for a b c d e f g h
    apply (cases h; cases a; cases b; cases c; cases d; cases e; cases f; cases g)
    by simp_all (* 10ms per case; 128 cases; slow *)
  done

lemma of_char_7F: "of_char (CHR 0x7F) = 127"
  by simp


lemma valid_char_ran': "\<not>digit7 c \<longleftrightarrow> (of_char c::nat) \<le> 127"
  using valid_char_ran of_char_7F by force

lemma list_less_one_correct:
  assumes xs: "xs \<in> {cs. \<forall>c\<in>set cs. \<not> digit7 c}"
    and ys: "ys \<in> {cs. \<forall>c\<in>set cs. \<not> digit7 c}"
  shows "list_less_one xs ys = (\<exists>z>literal.Abs_literal xs. z < literal.Abs_literal ys)"
  using assms
proof (induction xs ys rule: list_less_one_induct_cases)
  case (1 xs)
  hence "literal.Abs_literal [] \<le> literal.Abs_literal xs" 
    apply -
    apply (induction xs) 
    apply simp
    apply (rule preorder_class.less_imp_le)
    apply (subst String.less_literal.abs_eq)
      apply (rule zero_literal.rsp)
     apply (subst eq_onp_def) 
     apply simp 
    by auto
  then show ?case by auto
next
  case (2 y ys)
  show ?case 
  proof (cases "list_less_one [] (y # ys)")
    case True
    then consider (y_ord) "of_char (CHR 0x00) < (of_char y::nat)" | (ys_len) "0 < length ys"
      apply (-, subst (asm) list_less_one.simps) by blast
    then show ?thesis
    proof cases
      case y_ord
      have "literal.Abs_literal [] < literal.Abs_literal ((CHR 0x00)#ys)"
        apply (subst String.less_literal.abs_eq)
          apply (rule zero_literal.rsp)
         apply (subst eq_onp_def)
        using 2 apply simp
        by simp
      moreover
      have "literal.Abs_literal (CHR 0x00#ys) < literal.Abs_literal (y#ys)"
        apply (subst String.less_literal.abs_eq)
        unfolding eq_onp_def using 2 y_ord by simp+
      ultimately
      show ?thesis using True by blast
    next
      case ys_len
      have "literal.Abs_literal [] < literal.Abs_literal [y]"
        apply (subst String.less_literal.abs_eq)
        unfolding eq_onp_def using 2 by simp+
      moreover
      obtain y' ys' where
        ys: "ys = y' # ys'" using ys_len by (cases ys) auto
      have "literal.Abs_literal [y] < literal.Abs_literal (y # ys)"
        apply (subst ys)
        apply (subst String.less_literal.abs_eq)
        using ys ys_len 2 unfolding eq_onp_def
        by simp+
      ultimately
      show ?thesis by auto
    qed
  next
    case False
    hence "of_char y < (1::nat)" using False 
      by auto 
    hence "of_char y = (0::nat)" by simp
    hence "y = (CHR 0x00)" using inj_of_char 
      by (auto dest: injD[of _ y "CHR 0x00"])
    {
      fix z
      assume n: "literal.Abs_literal [] < z" 
         and y: "z < literal.Abs_literal [y]"
      have ordn: "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) [] (literal.explode z)" 
        using n less_literal.rep_eq by auto
      have ordy: "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (literal.explode z) [y]" 
        using y unfolding less_literal.rep_eq 
        using literal.Abs_literal_inverse 2 by simp
      have "length (literal.explode z) = 1" 
        using \<open>of_char y = 0\<close> ord.lexordp.simps ordn ordy by fastforce
      then obtain z' where
        "literal.explode z = [z']"
        "(of_char z'::nat) < of_char y"
        using ordy apply (cases "literal.explode z")
        by auto
      hence False using \<open>of_char y = 0\<close> by auto
    }
    then show ?thesis using False by auto
  qed
next
  case (3 x xs y ys)
  have "list_less_one xs ys = (\<exists>z>literal.Abs_literal xs. z < literal.Abs_literal ys)" 
    using 3 by auto
  also
  have "... = (\<exists>z>literal.Abs_literal (x#xs). z < literal.Abs_literal (x#ys))"
  proof (rule iffI; elim exE conjE)
    fix z
    assume xz: "literal.Abs_literal xs < z" 
       and yz: "z < literal.Abs_literal ys" 

    obtain zs where
      z: "z = literal.Abs_literal zs"
      and zs_wf: "zs \<in> {cs. \<forall>c\<in>set cs. \<not> digit7 c}"
      using literal.Abs_literal_cases by blast

    have xzs: "literal.Abs_literal xs < literal.Abs_literal zs"
     and yzs:"literal.Abs_literal zs < literal.Abs_literal ys" using xz yz z by simp+

    have "literal.Abs_literal (x#xs) < literal.Abs_literal (x#zs)"
      using xzs
      unfolding less_literal.rep_eq 
      using literal.Abs_literal_inverse 3 zs_wf by simp
    moreover
    have "literal.Abs_literal (x#zs) < literal.Abs_literal (x#ys)"
      using yzs
      unfolding less_literal.rep_eq 
      using literal.Abs_literal_inverse 3 zs_wf by simp
    ultimately
    show "\<exists>z>literal.Abs_literal (x # xs). z < literal.Abs_literal (x # ys)" by blast
  next
    fix z
    assume xxz: "literal.Abs_literal (x # xs) < z" 
       and yyz: "z < literal.Abs_literal (x # ys)" 
    
    obtain zs where
      z: "z = literal.Abs_literal zs"
      and zs_wf: "zs \<in> {cs. \<forall>c\<in>set cs. \<not> digit7 c}"
      using literal.Abs_literal_cases by blast

    obtain z' zs' where
      zs: "zs = z' # zs'" 
      using xxz 
      unfolding less_literal.rep_eq z
      using literal.Abs_literal_inverse 3 zs_wf by (cases zs) auto

    have xzs': "literal.Abs_literal (x # xs) < literal.Abs_literal (z' # zs')"
     and yzs': "literal.Abs_literal (z' # zs') < literal.Abs_literal (x # ys)"
     and zs'_wf: "z' # zs' \<in> {cs. \<forall>c\<in>set cs. \<not> digit7 c}" using xxz yyz zs_wf unfolding z zs by blast+

    have xzo: "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (x # xs) (z' # zs')" 
      and yzo: "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (z' # zs') (x # ys)" 
      using xzs' yzs'
      unfolding less_literal.rep_eq
      using literal.Abs_literal_inverse zs'_wf 3(3,4) 
      by simp+
    hence "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (xs) (zs')" 
          "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (zs') (ys)" 
      by auto
    hence "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (literal.explode (literal.Abs_literal xs)) (literal.explode (literal.Abs_literal zs'))" 
          "ord.lexordp (\<lambda>c d. (of_char c::nat) < of_char d) (literal.explode (literal.Abs_literal zs')) (literal.explode (literal.Abs_literal ys))"
      using literal.Abs_literal_inverse zs'_wf 3(3,4) 
      by simp+
    thus "\<exists>z>literal.Abs_literal xs. z < literal.Abs_literal ys" 
      unfolding less_literal.rep_eq
      by blast
  qed
  finally
  show ?case using \<open>x = y\<close> by auto
next
  case (4 x xs y ys)
  have "\<not>(list_less_one (x # xs) (y # ys))" using 4 by auto
  moreover
  have "\<not>literal.Abs_literal (x # xs) < literal.Abs_literal (y # ys)" 
    using 4 unfolding less_literal.rep_eq using literal.Abs_literal_inverse by simp
  ultimately
  show ?case by auto
next
  case (5 x xs y ys)
  have "literal.Abs_literal (x # xs) < literal.Abs_literal (x # xs @ [CHR 0x00])"
    unfolding less_literal.rep_eq 
    using literal.Abs_literal_inverse 5 apply (induction xs) by simp+
  moreover
  have "literal.Abs_literal (x # xs @ [CHR 0x00]) < literal.Abs_literal (y # ys)"
    unfolding less_literal.rep_eq 
    using literal.Abs_literal_inverse 5 apply (induction xs) by simp+
  ultimately
  show ?case using 5 by auto
qed

lemma proper_interval_literal_lemmas: "proper_interval None (None::String.literal option) = True"
  "\<And>y::String.literal. proper_interval None (Some y) = (\<exists>z. z < y)"
  "\<And>x::String.literal. proper_interval (Some x) None = (\<exists>z. x < z)" 
  "\<And>x y::String.literal. proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)"
proof -
show "proper_interval None (None::String.literal option) = True" by simp
  show "\<And>y::String.literal. proper_interval None (Some y) = (\<exists>z. z < y)"
  proof
    fix y::"String.literal"
    assume "proper_interval None (Some y)"
    hence yn: "y \<noteq> STR ''''" by simp
    hence "literal.explode y \<noteq> []" 
      using literal.explode_inject zero_literal.rep_eq by metis
    then obtain c cs where
      xy: "literal.explode y = c # cs" apply (cases "literal.explode y") by simp+
    have "STR '''' < y" using xy zero_literal.rep_eq 
      apply (subst less_literal.rep_eq) by auto
    thus "\<exists>z. z < y" by fast
  next
    fix y::"String.literal"
    assume "\<exists>z. z < y"
    then obtain z where
      le: "z < y" by blast
    {
      assume "y = (STR '''')"
      hence "y \<le> z"
        apply (cases "literal.explode z")
        using zero_literal.rep_eq
        using less_eq_literal.rep_eq
        by auto
      hence False using le by force
    }
    thus "proper_interval None (Some y)" by auto
  qed
  show "\<And>x::String.literal. proper_interval (Some x) None = (\<exists>z. x < z)" 
  proof -
    fix x::"String.literal"
    { have "literal.explode STR ''x'' \<noteq> []"
      proof 
        assume "literal.explode STR ''x'' = []"
        hence "literal.explode STR ''x'' = literal.explode STR ''''"
          using literal.explode_inject zero_literal.rep_eq by auto
        thus False using literal.explode_inject by auto
      qed
      hence "x < x + STR ''x''"
        apply (subst less_literal.rep_eq)
        apply (subst plus_literal.rep_eq)
        apply (rule ord.lexordp_append_rightI)
        by blast
      hence "\<exists>z. x < z" by blast
    }
    thus "proper_interval (Some x) None = (\<exists>z. x < z)" by force
  qed
  show "\<And>x y::String.literal. proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)"
    apply (subst proper_interval_literal.simps)
    apply (subst list_less_one_correct)
    using literal.explode literal.explode_inverse by simp+
qed


instance apply intro_classes 
  using proper_interval_literal_lemmas by blast+
end

find_theorems "OFCLASS(String.literal, proper_interval_class)"

find_theorems name: "proper_interval*lite"
value "STR '''' < STR ''a''"


instantiation predicate :: proper_interval
begin
fun proper_interval_predicate::"predicate option \<Rightarrow> predicate option \<Rightarrow> bool" where
"proper_interval_predicate None None = True" |
"proper_interval_predicate (Some (Pred p)) None = proper_interval (Some p) None" |
"proper_interval_predicate None (Some (Pred q)) = proper_interval None (Some q)" |
"proper_interval_predicate (Some (Pred p)) (Some (Pred q)) = proper_interval (Some p) (Some q)"


lemma predicate_proper_interval_lemmas:
   "proper_interval None (None::predicate option) = True"
    "\<And>y::predicate. proper_interval None (Some y) = (\<exists>z. z < y)" 
"\<And>x::predicate. proper_interval (Some x) None = (\<exists>z. x < z)" 
"\<And>x y::predicate. proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)" 
proof -
  show "proper_interval None (None::predicate option) = True" by simp
  show "\<And>y::predicate. proper_interval None (Some y) = (\<exists>z. z < y)" 
    subgoal for y
      apply (induction y)
      apply (subst proper_interval_predicate.simps)
      apply (subst proper_interval_literal_lemmas)
      apply (rule iffI)
       apply (erule exE)
      subgoal for z n
        apply (rule exI[of _ "Pred n"])
        unfolding less_predicate_def
        unfolding comparator_predicate_def
        unfolding partial_comparator_predicate_def
        unfolding lt_of_comp_def
        unfolding comp_def id_def
        unfolding predicate.rec predicate.case
        unfolding comparator_of_def 
        unfolding comp_lex.simps
        by auto
      apply (erule exE)
      subgoal for z n 
        apply (induction n)
        subgoal for y
          apply (rule exI[of _ y])
        apply (cases "y < z"; cases "y = z")
        unfolding less_predicate_def
        unfolding comparator_predicate_def
        unfolding partial_comparator_predicate_def
        unfolding lt_of_comp_def
        unfolding comp_def id_def
        unfolding predicate.rec predicate.case
        unfolding comparator_of_def 
        unfolding comp_lex.simps
        by simp+
      done
    done
  done
  show "\<And>x::predicate. proper_interval (Some x) None = (\<exists>z. x < z)" 
    subgoal for y
      apply (induction y)
      apply (subst proper_interval_predicate.simps)
      apply (subst proper_interval_literal_lemmas)
      apply (rule iffI)
       apply (erule exE)
      subgoal for z n
        apply (rule exI[of _ "Pred n"])
        unfolding less_predicate_def
        unfolding comparator_predicate_def
        unfolding partial_comparator_predicate_def
        unfolding lt_of_comp_def
        unfolding comp_def id_def
        unfolding predicate.rec predicate.case
        unfolding comparator_of_def 
        unfolding comp_lex.simps
        by auto
      apply (erule exE)
      subgoal for z n 
        apply (induction n)
        subgoal for y
          apply (rule exI[of _ y])
        apply (cases "z < y"; cases "y = z")
        unfolding less_predicate_def
        unfolding comparator_predicate_def
        unfolding partial_comparator_predicate_def
        unfolding lt_of_comp_def
        unfolding comp_def id_def
        unfolding predicate.rec predicate.case
        unfolding comparator_of_def 
        unfolding comp_lex.simps
        by simp+
      done
    done
  done
  show "\<And>x y::predicate. proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)" 
    subgoal for x y
      apply (induction x; induction y)
      apply (subst proper_interval_predicate.simps)
      apply (subst proper_interval_literal_lemmas)
      apply (rule iffI)
       apply (erule exE)
      subgoal for y x z
        apply (rule exI[of _ "Pred z"])
        apply (elim conjE)
        unfolding less_predicate_def
        unfolding comparator_predicate_def
        unfolding partial_comparator_predicate_def
        unfolding lt_of_comp_def
        unfolding comp_def id_def
        unfolding predicate.rec predicate.case
        unfolding comparator_of_def 
        unfolding comp_lex.simps
        by simp
     apply (erule exE)
      subgoal for y x n
        apply (induction n)
        subgoal for z
          apply (elim conjE)
          apply (rule exI[of _ z])
        unfolding less_predicate_def
        unfolding comparator_predicate_def
        unfolding partial_comparator_predicate_def
        unfolding lt_of_comp_def
        unfolding comp_def id_def
        unfolding predicate.rec predicate.case
        unfolding comparator_of_def 
        unfolding comp_lex.simps
        apply (cases "x < z"; cases "x = z"; cases "z < y"; cases "z = y")
        by auto
      done
    done
  done
qed

lemma predicate_proper_interval:
  "OFCLASS(predicate, proper_interval_class)"
  by (intro_classes; rule predicate_proper_interval_lemmas)
instance using predicate_proper_interval .
end

find_theorems name: "proper_interval*predi"

instantiation predicate :: cproper_interval
begin
definition "cproper_interval = (proper_interval :: predicate proper_interval)"
instance apply intro_classes 
  unfolding cproper_interval_predicate_def
  unfolding ccompare_predicate_def
  unfolding ID_Some option.sel
  using predicate_proper_interval
  unfolding class.proper_interval_def
  using predicate_proper_interval_lemmas
  unfolding less_predicate_def by blast
end

derive (rbt) set_impl predicate

derive (eq) ceq ast_action_schema
derive ccompare 
  "TEMPORAL_PDDL_Semantics.variable" "TEMPORAL_PDDL_Semantics.term" "TEMPORAL_PDDL_Semantics.type" 
  temporal_annotation duration_op duration_constraint ast_effect ast_action_schema

derive (rbt) set_impl ast_action_schema

definition "example_domain =
Domain [] [] [] [] []
"

definition "example_problem = 
  Problem example_domain [] [] (\<^bold>\<not>\<bottom>)
"

value "check_wf_problem example_problem"

definition "check_ground_problem P \<equiv> do {
  let D = ast_problem.domain P;
  let stg = ast_domain.STG D;
  let conT = ast_domain.mp_constT D;
  let mp = ast_problem.mp_objT P;
  check_wf_problem P stg conT mp;
  check (is_pos_conj (goal P)) (ERRS ''Goal not a conjunction of positive literals'');
  check_all_list pred_no_args (predicates D) ''Predicate not grounded (i.e. it has some argument)'' (shows o predicate.name o predicate_decl.pred);
  check_all_list act_no_params (actions D) ''Action not grounded, it has a/some parameter(s)'' (shows o ast_action_schema.name);
  check_all_list act_no_func_dcs (actions D) ''Action not grounded, it has a functional duration constraint'' (shows o ast_action_schema.name);
  check_all_list act_dcs_integers (actions D) ''Action's duration constraint is not an integer'' (shows o ast_action_schema.name);
  check_all_list act_pres_pos (actions D) ''Action has a conditions that is not a conjunction of positive literals'' (shows o ast_action_schema.name);
  check (functions D = []) (ERRS ''Domain has functions'');
  check (consts D = []) (ERRS ''Domain has constants'');
  check_all_list form_preds_no_args (init P) ''Initial literal not grounded (it refers to constants)'' 
    (\<lambda>(x::object atom Formulas.formula) (y::string). show y)
}"

lemma check_ground_problem_return_iff[return_iff]:
  "check_ground_problem P = Inr () \<longleftrightarrow> ground_ast_problem P"
proof -
  interpret ast_problem P .
  show ?thesis 
    unfolding check_ground_problem_def 
    unfolding ground_ast_problem_def
    unfolding wf_ast_problem_def
    unfolding ground_ast_problem_axioms_def
    unfolding list_all_iff
    unfolding return_iff
    by (force simp: wf_problem'_correct return_iff)
qed


definition "prop_to_var_impl prop_to_name p \<equiv> STR ''var_'' + prop_to_name p"
definition "prop_to_lock_impl prop_to_name p \<equiv> STR ''lock_'' + prop_to_name p"
definition "acts_active_impl \<equiv> STR ''acts_active''"
definition "planning_lock_impl \<equiv> STR ''planning_lock''"

definition "act_to_start_clock_impl act_to_name a \<equiv> STR ''start_'' + act_to_name a"
definition "act_to_end_clock_impl act_to_name a \<equiv> STR ''end_'' + act_to_name a"

definition "off_loc_impl \<equiv> 0::nat"
definition "starting_loc_impl \<equiv> 1::nat"
definition "running_loc_impl \<equiv> 2::nat"
definition "ending_loc_impl \<equiv> 3::nat"

definition "init_loc_impl \<equiv> 0::nat"
definition "planning_loc_impl \<equiv> 1::nat"
definition "goal_loc_impl \<equiv> 2::nat"

abbreviation "var_is n v \<equiv> bexp.eq (exp.var v) (exp.const n)"
abbreviation "inc_var n v \<equiv> (v, exp.binop (+) (exp.var v) (exp.const n))"
abbreviation "set_var n v \<equiv> (v, exp.const n)"


fun lower_spec_impl::"ast_action_schema \<Rightarrow> _" where
"lower_spec_impl (Simple_Action_Schema n ps pre eff) = Some (lower_bound.GE 0)" | (* could also be None *)
"lower_spec_impl (Durative_Action_Schema n ps d cond eff) = map_option (map_lower_bound floor) (dc_list_lower d)"

fun upper_spec_impl::"ast_action_schema \<Rightarrow> _" where
"upper_spec_impl (Simple_Action_Schema n ps pre eff) = Some (upper_bound.LE 0)" | (* could also be None *)
"upper_spec_impl (Durative_Action_Schema n ps d cond eff) = map_option (map_upper_bound floor) (dc_list_upper d)"

definition "l_dur_spec_impl a \<equiv> (case lower_spec_impl a of 
  None \<Rightarrow> [] | Some (lower_bound.GT n) \<Rightarrow> 
    [acconstraint.GT (act_to_start_clock_impl ast_action_schema.name a) n]
| Some (lower_bound.GE n) \<Rightarrow> 
    [acconstraint.GE (act_to_start_clock_impl ast_action_schema.name a) n])"


definition "u_dur_spec_impl a \<equiv> (case upper_spec_impl a of 
  None \<Rightarrow> [] | Some (upper_bound.LT n) \<Rightarrow> 
    [acconstraint.LT (act_to_start_clock_impl ast_action_schema.name a) n]
| Some (upper_bound.LE n) \<Rightarrow> 
    [acconstraint.LE (act_to_start_clock_impl ast_action_schema.name a) n])"

definition main_auto_loop_spec_impl::"(nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat)" where
"main_auto_loop_spec_impl \<equiv> (goal_loc_impl, bexp.true, [], Sil STR '''', [], [], goal_loc_impl)"


context ground_ast_problem_defs
begin

text \<open>We define the code that generates the automata\<close>

definition "mutex_snap_action' a b = 
  action_defs.mutex_snap_action (\<lambda>a. set (imp_defs.rat_impl.pre_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.add_imp_list a)) (\<lambda>a. set (imp_defs.rat_impl.del_imp_list a)) a b"

definition "int_clocks_spec' a =
    map (act_to_start_clock_impl ast_action_schema.name) (filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec) 
  @ map (act_to_end_clock_impl ast_action_schema.name) (filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec)"

definition "start_edge_spec' a = 
(let start_snap = AtStart a; guard = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' start_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' start_snap);
  not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list start_snap)) (imp_defs.rat_impl.del_imp_list start_snap)); 
  pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list start_snap);
  var_check = bexp_and_all (not_locked_check @ pre_check); 
  add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list start_snap); 
  del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list start_snap);
  upds = (inc_var 1 acts_active_impl) # del_upds @ add_upds; 
  resets = [act_to_start_clock_impl ast_action_schema.name a]
 in (off_loc_impl, var_check, guard, Sil STR '''', upds, resets, starting_loc_impl))"

definition "edge_2_spec' a =
(let 
  check_invs = bexp_and_all (map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (over_all_spec a));
  upds = map ((inc_var 1 \<circ>\<circ> prop_to_lock_impl) predicate.name) (over_all_spec a)
in (starting_loc_impl, check_invs, [], Sil STR '''', upds, [], running_loc_impl))"

definition "edge_3_spec' a =
(let 
  end_snap = AtEnd a; 
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' end_snap); 
  guard = l_dur_spec_impl a @ u_dur_spec_impl a @ int_clocks;
  upds = map ((inc_var (- 1) \<circ>\<circ> prop_to_lock_impl) predicate.name) (over_all_spec a); 
  resets = [act_to_end_clock_impl ast_action_schema.name a]
in (running_loc_impl, bexp.true, guard, Sil STR '''', upds, resets, ending_loc_impl))"

definition "end_edge_spec' a =
(let 
  end_instant = ending_loc_impl; 
  off = off_loc_impl; 
  end_snap = AtEnd a; 
  not_locked_check = map ((var_is 0 \<circ>\<circ> prop_to_lock_impl) predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list end_snap)) (imp_defs.rat_impl.del_imp_list end_snap));
  pre_check = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.pre_imp_list end_snap); 
  check = bexp_and_all (not_locked_check @ pre_check);
  add_upds = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.add_imp_list end_snap); 
  del_upds = map ((set_var 0 \<circ>\<circ> prop_to_var_impl) predicate.name) (imp_defs.rat_impl.del_imp_list end_snap);
  upds = inc_var (- 1) acts_active_impl # del_upds @ add_upds
in (end_instant, check, [], Sil STR '''', upds, [], off))"


definition "instant_trans_edge_spec' a =
(let 
  end_snap = AtEnd a; 
  start_snap = AtStart a; 
  int_clocks = map (\<lambda>x. acconstraint.GT x 0) (int_clocks_spec' end_snap) @ map (\<lambda>x. acconstraint.GE x 0) (int_clocks_spec' end_snap); 
  guard = l_dur_spec_impl a @ u_dur_spec_impl a @ int_clocks;
 resets = [act_to_end_clock_impl ast_action_schema.name a]
in (starting_loc_impl, bexp.true, guard, Sil STR '''', [], resets, ending_loc_impl))"


definition "action_to_automaton_spec' a =
(let committed_locs = []; 
  urgent_locs = [starting_loc_impl, ending_loc_impl]; 
  edges = [start_edge_spec' a, edge_2_spec' a, edge_3_spec' a, end_edge_spec' a, instant_trans_edge_spec' a];
  invs = []
in (committed_locs, urgent_locs, edges, invs))"

text \<open>We do the same for the main automaton\<close>

definition "init_spec' = (map to_predicate (filter is_predAtom (init P)))"

definition "main_auto_init_edge_spec' \<equiv>
(let can_start = var_is 0 planning_lock_impl;
  permit_planning = set_var 1 planning_lock_impl; 
  set_active = set_var 0 acts_active_impl;
  set_props = map ((set_var 1 \<circ>\<circ> prop_to_var_impl) predicate.name) init_spec'; 
  upds = permit_planning # set_active # set_props
in (init_loc_impl, can_start, [], Sil STR '''', upds, [], planning_loc_impl))
"

definition main_auto_goal_edge_spec'::"nat \<times>
   (String.literal, int) Simple_Expressions.bexp \<times>
   (String.literal, int) acconstraint list \<times>
   String.literal act \<times>
   (String.literal \<times> (String.literal, int) exp) list \<times> String.literal list \<times> nat" where
"main_auto_goal_edge_spec' \<equiv>
(let 
  can_end = [var_is 1 planning_lock_impl, var_is 0 acts_active_impl]; 
  goal_sat = map ((var_is 1 \<circ>\<circ> prop_to_var_impl) predicate.name) goal_spec;
  cond = bexp_and_all (can_end @ goal_sat); 
  lock_plan = (planning_lock_impl, exp.const 2)
in (planning_loc_impl, cond, [], Sil STR '''', [lock_plan], [], goal_loc_impl))
"

definition main_auto_spec'::"nat list \<times>
   nat list \<times>
   (nat \<times>
    (String.literal, int) Simple_Expressions.bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> nat) list \<times>
   (nat \<times> (String.literal, int) acconstraint list) list" where
"main_auto_spec' \<equiv>
(let committed_locs = []; 
  urgent_locs = [init_loc_impl, goal_loc_impl]; 
  edges = [main_auto_init_edge_spec', main_auto_goal_edge_spec', main_auto_loop_spec_impl]; 
  invs = [] 
in (committed_locs, urgent_locs, edges, invs))"

definition "automata_spec' = main_auto_spec' # map action_to_automaton_spec' actions_spec"


text \<open>Next, the broadcast channels\<close>
definition "broadcast_spec' = ([]::String.literal list)"

text \<open>We provide concrete definitions for variables\<close>

definition "inv_vars_spec' invs = (
let i = set invs
in prop_to_lock_impl predicate.name ` i \<union> prop_to_var_impl predicate.name ` i)"

definition "snap_vars_spec' snap = (
let pre_vars = map (prop_to_var_impl predicate.name) (imp_defs.rat_impl.pre_imp_list snap); 
    add_vars = map (prop_to_var_impl predicate.name) (imp_defs.rat_impl.add_imp_list snap);
    del_vars = map (prop_to_lock_impl predicate.name) (filter (\<lambda>p. p \<notin> set (imp_defs.rat_impl.add_imp_list snap)) (imp_defs.rat_impl.del_imp_list snap)) @ map (prop_to_var_impl predicate.name) (imp_defs.rat_impl.del_imp_list snap)
in set (pre_vars @ add_vars @ del_vars)
)"


definition "action_vars_spec' a = (
let inv_vars = inv_vars_spec' (over_all_spec a);
    start_vars = snap_vars_spec' (AtStart a);
    end_vars = snap_vars_spec' (AtEnd a)
in inv_vars \<union> start_vars \<union> end_vars
)"

definition "bounds_spec' = (
let action_vars = \<Union> (action_vars_spec' ` set actions_spec); 
    init_vars = prop_to_var_impl predicate.name ` set init_spec'; 
    goal_vars = prop_to_var_impl predicate.name ` set goal_spec; 
    vars_occ = action_vars \<union> init_vars \<union> goal_vars; 
    
    prop_lock_var_defs = map (\<lambda>p. (prop_to_lock_impl predicate.name p, 0, int (length actions_spec))) props_spec;
    prop_var_var_defs = map (\<lambda>p. (prop_to_var_impl predicate.name p, 0, 1)) props_spec; 
    prop_var_defs = filter (\<lambda>x. fst x \<in> vars_occ) (prop_lock_var_defs @ prop_var_var_defs); 

    acts_active_var = (acts_active_impl, 0::int, int (length actions_spec)); 
    planning_lock_var = (planning_lock_impl, 0, 2)
 in [acts_active_var, planning_lock_var] @ prop_var_defs)"

text \<open>Then, we provide the initial configuration\<close>

definition "init_locs_spec' =
init_loc_impl # map (\<lambda>x. off_loc_impl) actions_spec"

definition "init_vars_spec' =
map (map_prod id fst) bounds_spec'"

definition "init_cfg' =
  (init_locs_spec', map_of init_vars_spec', \<lambda>x::String.literal. 0::real)"

text \<open>Finally, the formula\<close>
definition formula_spec'::
  "(nat, nat, String.literal, int) Simple_Network_Language_Model_Checking.formula" 
  where
"formula_spec' = Simple_Network_Language_Model_Checking.formula.EX (sexp.loc 0 goal_loc_impl)"

text \<open>
We need to provide the model checker with the names of locations, clocks and automata.
These are typically removed in a parsing or syntax translation step.
\<close>

find_theorems name: "action*uniq"

definition "auto_names = 
  STR ''main'' # map (\<lambda>x. STR ''act_'' + ast_action_schema.name x) actions_spec
"

definition "auto_names_to_index =
  List_Index.index auto_names
"


definition "auto_loc_ids_to_names (n::nat) (m::nat) = (
  if (n = 0) then (case m of
      0 \<Rightarrow> (STR ''off'')
    | Suc 0 \<Rightarrow> (STR ''starting'')
    | Suc (Suc 0) \<Rightarrow> (STR ''running'')
    | Suc (Suc (Suc 0)) \<Rightarrow> (STR ''ending'')
  ) 
  else (case m of
      0 \<Rightarrow> (STR ''init'')
    | Suc 0 \<Rightarrow> (STR ''planning'')
    | Suc (Suc 0) \<Rightarrow> (STR ''goal'')
  )
)
"

definition "clock_names =
map (act_to_start_clock_impl ast_action_schema.name) actions_spec
@ map (act_to_end_clock_impl ast_action_schema.name) actions_spec
"

end



lemmas ground_ast_problem_code =
  ground_ast_problem_defs.props_spec_def
  ground_ast_problem_defs.ground_non_action_def
  ground_ast_problem_defs.over_all_snap.simps
  ground_ast_problem_defs.over_all_spec.simps
  ground_ast_problem_defs.goal_spec_def 
  ground_ast_problem_defs.dels_spec.simps 
  ground_ast_problem_defs.adds_spec.simps
  ground_ast_problem_defs.pre_spec.simps
  action_defs.app_snap.simps
  ground_ast_problem_defs.at_start_spec.simps
  ground_ast_problem_defs.at_end_spec.simps
  ground_ast_problem_defs.actions_spec_def
  ground_ast_problem_defs.mutex_snap_action'_def
  ground_ast_problem_defs.int_clocks_spec'_def
  ground_ast_problem_defs.start_edge_spec'_def
  ground_ast_problem_defs.edge_2_spec'_def
  ground_ast_problem_defs.edge_3_spec'_def
  ground_ast_problem_defs.end_edge_spec'_def
  ground_ast_problem_defs.instant_trans_edge_spec'_def
  ground_ast_problem_defs.action_to_automaton_spec'_def
  ground_ast_problem_defs.init_spec'_def
  ground_ast_problem_defs.main_auto_init_edge_spec'_def
  ground_ast_problem_defs.main_auto_goal_edge_spec'_def
  ground_ast_problem_defs.main_auto_spec'_def
  ground_ast_problem_defs.automata_spec'_def
  ground_ast_problem_defs.broadcast_spec'_def
  ground_ast_problem_defs.inv_vars_spec'_def
  ground_ast_problem_defs.snap_vars_spec'_def
  ground_ast_problem_defs.action_vars_spec'_def
  ground_ast_problem_defs.bounds_spec'_def
  ground_ast_problem_defs.init_locs_spec'_def
  ground_ast_problem_defs.init_vars_spec'_def
  ground_ast_problem_defs.init_cfg'_def
  ground_ast_problem_defs.formula_spec'_def
  ground_ast_problem_defs.auto_names_def
  ground_ast_problem_defs.auto_names_to_index_def
  ground_ast_problem_defs.auto_loc_ids_to_names_def
  ground_ast_problem_defs.clock_names_def

declare ground_ast_problem_code[code]


context ground_ast_problem
begin


subsection \<open>Refinement to monadic code\<close>

text \<open>Some constants need executable copies\<close>

(* tp_nta_reduction_spec.planning_loc, tp_nta_reduction_spec.set_prop_ab, tp_nta_reduction_spec.acts_active, tp_nta_reduction_spec.init_loc *)

lemma prop_to_var_refine: 
  "abstr_model_checking.reduction_ref_impl.prop_to_var \<equiv> prop_to_var_impl predicate.name"
  unfolding abstr_model_checking.reduction_ref_impl.prop_to_var_def
  unfolding prop_to_var_impl_def prop_to_name_spec_def
  by argo

lemma prop_to_lock_refine: 
  "abstr_model_checking.reduction_ref_impl.prop_to_lock \<equiv> prop_to_lock_impl predicate.name"
  unfolding abstr_model_checking.reduction_ref_impl.prop_to_lock_def
  unfolding prop_to_lock_impl_def prop_to_name_spec_def
  by argo

lemma acts_active_refine:
  "abstr_model_checking.reduction_ref_impl.acts_active = acts_active_impl"
  unfolding abstr_model_checking.reduction_ref_impl.acts_active_def
  unfolding acts_active_impl_def
  ..

lemma planning_lock_refine:
  "abstr_model_checking.reduction_ref_impl.planning_lock = planning_lock_impl"
  unfolding abstr_model_checking.reduction_ref_impl.planning_lock_def
  unfolding planning_lock_impl_def ..

lemma act_to_start_clock_refine:
  "abstr_model_checking.reduction_ref_impl.act_to_start_clock = act_to_start_clock_impl ast_action_schema.name"
  unfolding abstr_model_checking.reduction_ref_impl.act_to_start_clock_def
  unfolding act_to_name_spec_def
  unfolding act_to_start_clock_impl_def
  ..

lemma act_to_end_clock_refine:
  "abstr_model_checking.reduction_ref_impl.act_to_end_clock = act_to_end_clock_impl ast_action_schema.name"
  unfolding abstr_model_checking.reduction_ref_impl.act_to_end_clock_def
  unfolding act_to_name_spec_def
  unfolding act_to_end_clock_impl_def
  ..

lemma off_loc_refine:
  "abstr_model_checking.reduction_ref_impl.off_loc = off_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.off_loc_def
  unfolding off_loc_impl_def
  ..

lemma starting_loc_refine:
  "abstr_model_checking.reduction_ref_impl.starting_loc = starting_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.starting_loc_def
  unfolding starting_loc_impl_def
  ..

lemma running_loc_refine:
  "abstr_model_checking.reduction_ref_impl.running_loc = running_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.running_loc_def
  unfolding running_loc_impl_def
  ..

lemma ending_loc_refine:
  "abstr_model_checking.reduction_ref_impl.ending_loc = ending_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.ending_loc_def
  unfolding ending_loc_impl_def
  ..

lemma init_loc_refine:
  "abstr_model_checking.reduction_ref_impl.init_loc = init_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.init_loc_def
  unfolding init_loc_impl_def
  ..

lemma planning_loc_refine:
  "abstr_model_checking.reduction_ref_impl.planning_loc = planning_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.planning_loc_def
  unfolding planning_loc_impl_def
  ..

lemma goal_loc_refine:
  "abstr_model_checking.reduction_ref_impl.goal_loc = goal_loc_impl"
  unfolding abstr_model_checking.reduction_ref_impl.goal_loc_def
  unfolding goal_loc_impl_def
  ..

lemma set_prop_ab_refine:
  "abstr_model_checking.reduction_ref_impl.set_prop_ab n = (set_var n) o (prop_to_var_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.set_prop_ab_def
  unfolding prop_to_var_refine
  ..

lemma is_prop_ab_refine:
  "abstr_model_checking.reduction_ref_impl.is_prop_ab n = (var_is n) o (prop_to_var_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.is_prop_ab_def
  unfolding prop_to_var_refine
  ..

lemma inc_prop_ab_refine:
  "abstr_model_checking.reduction_ref_impl.inc_prop_ab n = (inc_var n) o (prop_to_var_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.inc_prop_ab_def
  unfolding prop_to_var_refine
  ..

lemma set_prop_lock_ab_refine:
  "abstr_model_checking.reduction_ref_impl.set_prop_lock_ab n = (set_var n) o (prop_to_lock_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.set_prop_lock_ab_def
  unfolding prop_to_lock_refine
  ..

lemma is_prop_lock_ab_refine:
  "abstr_model_checking.reduction_ref_impl.is_prop_lock_ab n = (var_is n) o (prop_to_lock_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.is_prop_lock_ab_def
  unfolding prop_to_lock_refine
  ..

lemma inc_prop_lock_ab_refine:
  "abstr_model_checking.reduction_ref_impl.inc_prop_lock_ab n = (inc_var n) o (prop_to_lock_impl predicate.name)"
  unfolding abstr_model_checking.reduction_ref_impl.inc_prop_lock_ab_def
  unfolding prop_to_lock_refine
  ..

lemma lower_spec_refine:
  "lower_spec = lower_spec_impl"
  apply (intro ext)
  subgoal for x
    apply (cases x)
    by simp+
  done

lemma upper_spec_refine:
  "upper_spec = upper_spec_impl"
  apply (intro ext)
  subgoal for x
    apply (cases x)
    by simp+
  done

schematic_goal l_dur_spec_refine:
  "abstr_model_checking.reduction_ref_impl.l_dur_spec = l_dur_spec_impl"
  apply (intro ext)
  unfolding abstr_model_checking.reduction_ref_impl.l_dur_spec_def
  unfolding lower_spec_refine
  unfolding act_to_start_clock_refine
  unfolding l_dur_spec_impl_def
  ..

schematic_goal u_dur_spec_refine:
  "abstr_model_checking.reduction_ref_impl.u_dur_spec = u_dur_spec_impl"
  apply (intro ext)
  unfolding abstr_model_checking.reduction_ref_impl.u_dur_spec_def
  unfolding upper_spec_refine
  unfolding act_to_start_clock_refine
  unfolding u_dur_spec_impl_def
  ..



text \<open>Now, we will refine these lemmas. Checking list intersection is inefficient
  for all actions. We do not need to, because we have proven that actions only refer to 
  propositions (predicates without arguments)
  at the level of PDDL.\<close>
lemma pre_imp_restr_equiv_pre_imp:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "imp_defs.rat_impl.pre_imp_restr_list a = imp_defs.rat_impl.pre_imp_list a"
proof -
  have "set (imp_defs.rat_impl.pre_imp_list a) \<subseteq> set props_spec"
  proof (intro subsetI)
    fix x
    assume "x \<in> set (imp_defs.rat_impl.pre_imp_list a)"
    thus "x \<in> set props_spec" 
      using assms
      apply (induction a)
      unfolding imp_defs.rat_impl.pre_imp_list_def imp_defs.rat_impl.set_impl.app_snap.simps
      using start_pre_in_props end_pre_in_props by blast+
  qed
  thus ?thesis
    unfolding imp_defs.rat_impl.pre_imp_restr_list_def
    by (force simp: filter_id_conv)
qed

lemma over_all_restr_equiv_over_all:
  assumes "a \<in> set actions_spec"
  shows "imp_defs.rat_impl.over_all_restr_list a = over_all_spec a"
proof -
  have "set (over_all_spec a) \<subseteq> set props_spec"
    using over_all_in_props assms by simp
  thus ?thesis unfolding imp_defs.rat_impl.over_all_restr_list_def
    by (force simp: filter_id_conv)
qed


lemma mutex_snap_action_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
          and "b \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
        shows "abstr_model_checking.rat_imp'.prob_list_impl.set_impl.mutex_snap_action a b = 
     mutex_snap_action' a b"
  unfolding mutex_snap_action'_def
  apply (subst abstr_model_checking.rat_imp'.prob_list_impl.set_impl.mutex_snap_action_def)
  unfolding comp_def apply (subst pre_imp_restr_equiv_pre_imp, use assms in blast)+
  apply (subst action_defs.mutex_snap_action_def[symmetric])
  by simp

lemma int_clocks_spec_refine:
  assumes "a \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.int_clocks_spec a = int_clocks_spec' a"
proof -
  have 1: "filter (\<lambda>aa. abstr_model_checking.reduction_ref_impl.mutex_effects_spec a (AtStart aa)) actions_spec =
    filter (\<lambda>b. mutex_snap_action' a (AtStart b)) actions_spec"
    apply (rule filter_eq_conv)
    using mutex_snap_action_refine[OF assms]
    by simp
  
  have 2: "filter (\<lambda>aa. abstr_model_checking.reduction_ref_impl.mutex_effects_spec a (AtEnd aa)) actions_spec =
    filter (\<lambda>aa. mutex_snap_action' a (AtEnd aa)) actions_spec"
    apply (rule filter_eq_conv)
    using mutex_snap_action_refine[OF assms]
    by simp
  
  show ?thesis
    unfolding abstr_model_checking.reduction_ref_impl.int_clocks_spec_def Let_def
    unfolding 1 2 int_clocks_spec'_def
    unfolding act_to_start_clock_refine
    unfolding act_to_end_clock_refine
    by blast
qed

lemma start_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.start_edge_spec a = start_edge_spec' a" 
  unfolding start_edge_spec'_def
  unfolding abstr_model_checking.reduction_ref_impl.start_edge_spec_def
  unfolding is_prop_lock_ab_refine
  unfolding is_prop_ab_refine
  unfolding set_prop_ab_refine
  unfolding acts_active_refine
  unfolding off_loc_refine starting_loc_refine
  unfolding act_to_start_clock_refine
  using int_clocks_spec_refine assms pre_imp_restr_equiv_pre_imp
  by simp


lemma edge_2_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_2_spec a = edge_2_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_2_spec_def 
  unfolding is_prop_ab_refine
  unfolding inc_prop_lock_ab_refine
  unfolding starting_loc_refine running_loc_refine
  unfolding edge_2_spec'_def
  using over_all_restr_equiv_over_all assms
  by simp

lemma edge_3_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.edge_3_spec a = edge_3_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.edge_3_spec_def
  unfolding edge_3_spec'_def
  unfolding running_loc_refine
  unfolding ending_loc_refine
  unfolding act_to_end_clock_refine
  unfolding inc_prop_lock_ab_refine
  unfolding l_dur_spec_refine u_dur_spec_refine
  using int_clocks_spec_refine assms over_all_restr_equiv_over_all
  by simp


lemma end_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.end_edge_spec a = end_edge_spec' a"
  unfolding abstr_model_checking.reduction_ref_impl.end_edge_spec_def
  unfolding ending_loc_refine off_loc_refine
  unfolding is_prop_ab_refine
  unfolding is_prop_lock_ab_refine
  unfolding set_prop_ab_refine
  unfolding acts_active_refine
  unfolding end_edge_spec'_def
  using pre_imp_restr_equiv_pre_imp assms
  by auto


lemma instant_trans_edge_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.instant_trans_edge_spec a = instant_trans_edge_spec' a" 
  unfolding abstr_model_checking.reduction_ref_impl.instant_trans_edge_spec_def
  unfolding instant_trans_edge_spec'_def
  unfolding starting_loc_refine ending_loc_refine
  unfolding l_dur_spec_refine u_dur_spec_refine
  unfolding act_to_end_clock_refine
  using int_clocks_spec_refine assms
  by simp


lemma action_to_automaton_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.action_to_automaton_spec a = action_to_automaton_spec' a"
  unfolding abstr_model_checking.reduction_ref_impl.action_to_automaton_spec_def
  unfolding action_to_automaton_spec'_def
  unfolding starting_loc_refine ending_loc_refine
  using start_edge_spec_refine edge_2_spec_refine edge_3_spec_refine end_edge_spec_refine instant_trans_edge_spec_refine assms
  by simp


text \<open>Now we provide an equivalent definition of the main automaton.\<close>


lemma filter_props_init:
  "(filter (\<lambda>p. p \<in> set props_spec) init_spec) = init_spec'"
  apply (subst filter_True)
  using init_in_props apply blast
  unfolding init_spec_def init_spec'_def
  apply (rule distinct_remdups_id)
  apply (rule distinct_inj_on_map)
  using wf_problem unfolding wf_problem_def apply simp
  apply (rule inj_on_subset)
   apply (rule inj_on_to_predicate)
  using init_no_args
  unfolding list_all_iff by auto
  

lemma filter_props_goal:
  "(filter (\<lambda>p. p \<in> set props_spec) goal_spec) = goal_spec"
  using goal_in_props filter_id_conv by fast

  
lemma main_auto_init_edge_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec = main_auto_init_edge_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_init_edge_spec_def
  unfolding main_auto_init_edge_spec'_def
  unfolding filter_props_init planning_lock_refine
  unfolding planning_loc_refine
  unfolding init_loc_refine
  unfolding acts_active_refine
  unfolding set_prop_ab_refine
  ..

lemma main_auto_goal_edge_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_spec = main_auto_goal_edge_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_goal_edge_spec_def
  unfolding main_auto_goal_edge_spec'_def
  unfolding filter_props_goal
  unfolding planning_loc_refine
  unfolding goal_loc_refine
  unfolding acts_active_refine
  unfolding planning_lock_refine
  unfolding is_prop_ab_refine
  ..

lemma main_auto_loop_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_loop_spec = main_auto_loop_spec_impl"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_loop_spec_def
  unfolding main_auto_loop_spec_impl_def
  unfolding goal_loc_refine ..

lemma main_auto_spec_refine:
  "abstr_model_checking.reduction_ref_impl.main_auto_spec = main_auto_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.main_auto_spec_def
  unfolding main_auto_spec'_def
  unfolding main_auto_init_edge_spec_refine main_auto_goal_edge_spec_refine
  unfolding main_auto_loop_spec_refine
  unfolding init_loc_refine goal_loc_refine
  ..


text \<open>Finally we can provide another definition of the entire network\<close>

lemma automata_spec_refine:
  shows "abstr_model_checking.reduction_ref_impl.automata_spec = automata_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.timed_automaton_net_spec_def
  unfolding automata_spec'_def
  using action_to_automaton_spec_refine main_auto_spec_refine by simp

text \<open>Next, we need to refine the set of broadcast channels (there are none)\<close>


lemma broadcast_spec_refine:
  "abstr_model_checking.reduction_ref_impl.broadcast_spec = broadcast_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.broadcast_spec_def
  unfolding broadcast_spec'_def by simp


text \<open>Then, we refine the variable bounds\<close>

lemma inv_vars_spec_refine:
  "abstr_model_checking.reduction_ref_impl.inv_vars_spec invs = inv_vars_spec' invs"
  unfolding abstr_model_checking.reduction_ref_impl.inv_vars_spec_def
  unfolding prop_to_lock_refine prop_to_var_refine
  unfolding inv_vars_spec'_def by auto

lemma snap_vars_spec_refine:
  assumes "snap \<in> AtStart ` set actions_spec \<union> AtEnd ` set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.snap_vars_spec snap = snap_vars_spec' snap"
  unfolding abstr_model_checking.reduction_ref_impl.snap_vars_spec_def
  unfolding pre_imp_restr_equiv_pre_imp[OF assms]
  unfolding prop_to_var_refine prop_to_lock_refine
  unfolding snap_vars_spec'_def 
  by presburger

lemma action_vars_spec_refine:
  assumes "a \<in> set actions_spec"
  shows "abstr_model_checking.reduction_ref_impl.action_vars_spec a = action_vars_spec' a "
  unfolding abstr_model_checking.reduction_ref_impl.action_vars_spec_def
  unfolding inv_vars_spec_refine
  using assms snap_vars_spec_refine over_all_restr_equiv_over_all
  unfolding action_vars_spec'_def 
  by auto


lemma bounds_spec_refine:
  "abstr_model_checking.reduction_ref_impl.bounds_spec = bounds_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.all_vars_spec_def
  unfolding filter_props_init filter_props_goal
  unfolding prop_to_lock_refine
  unfolding prop_to_var_refine
  unfolding acts_active_refine
  unfolding planning_lock_refine
  unfolding fold_union' set_map
  unfolding bounds_spec'_def
  using action_vars_spec_refine
  by auto


text \<open>Refinining the initial configuration and formula\<close>
lemma init_locs_spec_refine:
  "abstr_model_checking.reduction_ref_impl.init_locs_spec = init_locs_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.init_locs_spec_def
  unfolding init_loc_refine off_loc_refine
  unfolding init_locs_spec'_def by blast

lemma init_vars_spec_refine:
  "abstr_model_checking.reduction_ref_impl.init_vars_spec = init_vars_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.init_vars_spec_def
  unfolding bounds_spec_refine
  unfolding init_vars_spec'_def
  by blast

lemma init_cfg_refine:
  "(case abstr_model_checking.ref_model_checking.a\<^sub>0 of (x, y) \<Rightarrow> (x, case y of (x, y) \<Rightarrow> (x, \<lambda>x. real_of_int (y x))))
   = init_cfg'"
  unfolding abstr_model_checking.ref_model_checking.a\<^sub>0_def
  unfolding prod.case
  unfolding init_locs_spec_refine
  unfolding init_vars_spec_refine
  unfolding init_cfg'_def 
  by simp

lemma formula_refine:
  "abstr_model_checking.reduction_ref_impl.formula_spec = formula_spec'"
  unfolding abstr_model_checking.reduction_ref_impl.formula_spec_def
  unfolding goal_loc_refine
  unfolding formula_spec'_def
  by blast

text \<open>Combining all of this, we get to the alternative model checking problem\<close>

lemma model_checking_problem_refine: 
  "\<not> Simple_Network_Impl.sem automata_spec' broadcast_spec' bounds_spec', init_cfg' \<Turnstile> formula_spec'
\<Longrightarrow> \<nexists>tp. valid_ground_plan P tp"
  using form_not_sat_imp_no_valid_ground_plan
  unfolding abstr_model_checking.ref_model_checking.net_impl.sem_def 
  unfolding automata_spec_refine
  unfolding broadcast_spec_refine
  unfolding bounds_spec_refine
  unfolding init_cfg_refine
  unfolding formula_refine
  unfolding Simple_Network_Impl.sem_def
  by blast


end

value "ground_ast_problem_defs.automata_spec' example_problem"
value "ground_ast_problem_defs.broadcast_spec'"
value "ground_ast_problem_defs.bounds_spec' example_problem"
value "ground_ast_problem_defs.init_cfg' example_problem"
value "ground_ast_problem_defs.formula_spec'"

value "ground_ast_problem_defs.auto_names"
value "ground_ast_problem_defs.auto_names_to_index"
value "ground_ast_problem_defs.auto_loc_ids_to_names"
value "ground_ast_problem_defs.clock_names example_problem"

definition "make_network_impl P \<equiv> do {
  let automata = ground_ast_problem_defs.automata_spec' P;
  let broadcast = ground_ast_problem_defs.broadcast_spec';
  let bounds = ground_ast_problem_defs.bounds_spec' P;
  let init_locs = ground_ast_problem_defs.init_locs_spec' P;
  let init_vars = ground_ast_problem_defs.init_vars_spec' P;
  let formula = ground_ast_problem_defs.formula_spec';
  let clock_names = ground_ast_problem_defs.clock_names P;
  let auto_names = ground_ast_problem_defs.auto_names P;

  let clock_names = ground_ast_problem_defs.clock_names P;
  let auto_names = ground_ast_problem_defs.auto_names P;

  let ids_to_names = ground_ast_problem_defs.auto_loc_ids_to_names;
  let process_names_to_index = ground_ast_problem_defs.auto_names_to_index P;

  Error_Monad.return (clock_names, auto_names, ids_to_names, process_names_to_index,
     broadcast, automata, bounds, formula, init_locs, init_vars)
}"

lemma make_network_impl_return_iff[return_iff]:
  "make_network_impl P = Inr (
    ground_ast_problem_defs.clock_names P,
    ground_ast_problem_defs.auto_names P,
    ground_ast_problem_defs.auto_loc_ids_to_names, 
    ground_ast_problem_defs.auto_names_to_index P,
    ground_ast_problem_defs.broadcast_spec', 
    ground_ast_problem_defs.automata_spec' P, 
    ground_ast_problem_defs.bounds_spec' P, 
    ground_ast_problem_defs.formula_spec', 
    ground_ast_problem_defs.init_locs_spec' P , 
    ground_ast_problem_defs.init_vars_spec' P)" 
    unfolding make_network_impl_def ground_ast_problem_defs.init_cfg'_def
    by (auto simp: check_ground_problem_return_iff return_iff)

definition check_and_make_network where
"check_and_make_network P \<equiv> do {
  check_ground_problem P;
  make_network_impl P
}"

lemma check_and_make_network_and_plan:
  assumes "(check_and_make_network P = Inr (clocks, auto_names, ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, init_locs, init_vars))"
  shows "\<not> (Simple_Network_Impl.sem automata broadcast bounds, (init_locs, map_of init_vars, (\<lambda>_. 0)) \<Turnstile> formula) \<longrightarrow> (\<nexists>tp. valid_ground_plan P tp)"
  using assms
  unfolding check_and_make_network_def
  unfolding return_iff make_network_impl_return_iff
  using check_ground_problem_return_iff
  using ground_ast_problem.model_checking_problem_refine 
  unfolding ground_ast_problem_defs.init_cfg'_def
  find_theorems name: "a\<^sub>0"
  by force

export_code check_and_make_network
  in Eval module_name Certifier
end