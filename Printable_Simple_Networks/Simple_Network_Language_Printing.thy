theory Simple_Network_Language_Printing
  imports (* Parsing.JSON_Printing *)
    Networks.Networks 
    TA_Code.Simple_Network_Language_Export_Code
    Printable_Simple_Expressions
    "Temporal_Planning_Base.Error_List_Monad_Add"
begin

abbreviation print_list::"'b::show \<Rightarrow> ('a::show) list \<Rightarrow> string" where
"print_list sep xs \<equiv> map show xs |> intersperse (show sep) |> concat"

fun showsp_sbexp::"('n::show, 's::show, 'a::show, 'b::show) sexp \<Rightarrow> string \<Rightarrow> string" where
"showsp_sbexp sexp.true = (@) ''true''" |
"showsp_sbexp (sexp.not f) = shows ''~('' o showsp_sbexp f o shows '')''" |
"showsp_sbexp (sexp.and f g) = showsp_sbexp f o shows '' && '' o showsp_sbexp g" |
"showsp_sbexp (sexp.or f g) = shows ''('' o showsp_sbexp f o shows '' || '' o showsp_sbexp g o shows '')''" |
"showsp_sbexp (sexp.imply f g) = shows ''('' o showsp_sbexp f o shows '' -> '' o showsp_sbexp g o shows '')''" |
"showsp_sbexp (sexp.loc p s) = shows p o shows ''.'' o shows s" |
"showsp_sbexp (sexp.eq c d) = shows c o shows '' = '' o shows d" |
"showsp_sbexp (sexp.le c d) = shows c o shows '' <= '' o shows d" |
"showsp_sbexp (sexp.lt c d) = shows c o shows '' < '' o shows d" |
"showsp_sbexp (sexp.ge c d) = shows c o shows '' >= '' o shows d" |
"showsp_sbexp (sexp.gt c d) = shows c o shows '' > '' o shows d"
(*
instantiation sexp::("show", "show", "show", "show") "show" begin
  definition "shows_prec_sexp (n::nat) e \<equiv> showsp_sbexp e"
 (*  definition "shows_list_sexp xs \<equiv> showsp_list (\<lambda>n x. showsp_sbexp x) 0 xs" *)
instance sorry
end *)

fun showsp_formula::"('n::show, 's::show, 'a::show, 'b::show) formula \<Rightarrow> string \<Rightarrow> string" where
"showsp_formula (formula.EX b) = shows ''E<> '' o showsp_sbexp b" |
"showsp_formula (formula.EG b) = shows ''E[] '' o showsp_sbexp b" |
"showsp_formula (formula.AX b) = shows ''A<> '' o showsp_sbexp b" |
"showsp_formula (formula.AG b) = shows ''A[] '' o showsp_sbexp b" |
"showsp_formula (formula.Leadsto a b) = showsp_sbexp a o shows '' --> '' o showsp_sbexp b"
(*
instantiation formula::("show", "show", "show", "show") "show" begin
  definition "shows_prec_formula (n::nat) f \<equiv> showsp_formula f"
 (*  definition "shows_list_formula xs \<equiv> showsp_list (\<lambda>n x. showsp_formula x) 0 xs" *)
instance sorry
end
 *)

fun rename_automata_sexp::"
  ('n \<Rightarrow> 'm Error_List_Monad.result)
\<Rightarrow> ('n, 's, 'a, 'b) sexp
\<Rightarrow> ('m, 's, 'a, 'b) sexp Error_List_Monad.result" where
"rename_automata_sexp rnm sexp.true = Result sexp.true" |
"rename_automata_sexp rnm (sexp.not e) = (rename_automata_sexp rnm e) \<bind> (\<lambda>x. Result (sexp.not x))" |
"rename_automata_sexp rnm (sexp.and f g) = do {
  f' \<leftarrow> rename_automata_sexp rnm f;
  g' \<leftarrow> rename_automata_sexp rnm g;
  Result (sexp.and f' g')
}" |
"rename_automata_sexp rnm (sexp.or f g) = do {
  f' \<leftarrow> rename_automata_sexp rnm f;
  g' \<leftarrow> rename_automata_sexp rnm g;
  Result (sexp.or f' g')
}" |
"rename_automata_sexp rnm (sexp.imply f g) = do {
  f' \<leftarrow> rename_automata_sexp rnm f;
  g' \<leftarrow> rename_automata_sexp rnm g;
  Result (sexp.imply f' g')
}" |
"rename_automata_sexp rnm (sexp.eq a b) = Result (sexp.eq a b)" |
"rename_automata_sexp rnm (sexp.le a b) = Result (sexp.le a b)" |
"rename_automata_sexp rnm (sexp.lt a b) = Result (sexp.lt a b)" |
"rename_automata_sexp rnm (sexp.ge a b) = Result (sexp.ge a b)" |
"rename_automata_sexp rnm (sexp.gt a b) = Result (sexp.gt a b)" |
"rename_automata_sexp rnm (sexp.loc n s) = do {
  n' \<leftarrow> rnm n;
  Result (sexp.loc n' s)
}"

fun rename_automata_formula::"
  ('n \<Rightarrow> 'm Error_List_Monad.result)
\<Rightarrow> ('n, 's, 'a, 'b) formula
\<Rightarrow> ('m, 's, 'a, 'b) formula Error_List_Monad.result" where
"rename_automata_formula rnm (formula.EX e) = do {
  e' \<leftarrow> rename_automata_sexp rnm e;
  Result (formula.EX e')
}"

(* For the goal. To do: locations are not just strings. *)
definition formula_to_JSON::"
  (nat \<Rightarrow> String.literal option)
\<Rightarrow> (String.literal \<Rightarrow> nat \<Rightarrow> String.literal option)
\<Rightarrow> (nat, nat, String.literal, int) formula 
  \<Rightarrow> (string \<times> JSON) Error_List_Monad.result" where
"formula_to_JSON auto_id_to_name loc_id_to_name formula = do { 
  formula \<leftarrow> rename_automata_formula (get_or_err ''Automaton has no ID'' auto_id_to_name) formula;
  formula \<leftarrow> rename_locs_formula (\<lambda>a l. get_or_err ''Location has no ID in automaton'' (loc_id_to_name a) l) formula;
 
  Result (''formula'', String (showsp_formula formula ''''))
}
"

fun print_var::"(String.literal \<times> int \<times> int) \<Rightarrow> string" where
"print_var (v, l, u) = show v @ ''['' @ show l @ '':'' @ show u @ '']''"

(* variables are passed together with bounds *)
definition bounded_vars_to_vars_and_bounds::"(String.literal \<times> int \<times> int) list \<Rightarrow> string \<times> JSON" where
"bounded_vars_to_vars_and_bounds bv \<equiv> (''vars'', String (print_list '', '' (map print_var bv)))"


(* What do actions do? They synchronise channels, but they are always paired with another value
  in the semantics in Networks.thy. What is the other value? *)

fun showsp_act::"('a::show) act \<Rightarrow> string \<Rightarrow> string" where
"showsp_act (Sil v) = id" |
"showsp_act (In v) = (shows ''?'') o (shows v)" |
"showsp_act (Out v) = (shows ''!'') o (shows v)"

(*
instantiation act::("show") "show" begin
  
  definition shows_prec_act where
  "shows_prec_act (n::nat) a \<equiv> showsp_act a"
  
 (*  definition shows_list_act where
  "shows_list_act xs \<equiv> showsp_list (\<lambda>n x. showsp_act x) 0 xs" *)
instance sorry
end
 *)

fun showsp_exp::"(('a::show), ('b::show)) exp \<Rightarrow> string" and
  showsp_bexp::"('a, 'b::show) bexp \<Rightarrow> string" where
"showsp_exp (exp.mult a b) = showsp_exp a @ show '' * '' @ showsp_exp b" |
"showsp_exp (exp.add a b) = show ''('' @ showsp_exp a @ show '' + '' @ showsp_exp b @ show '')''" |
"showsp_exp (exp.if_then_else b x y) = show ''('' @ showsp_bexp b @ show '' ? '' @ showsp_exp x @ show '' : '' @ showsp_exp y @ show '')''" |
"showsp_exp (exp.const c) = show c" |
"showsp_exp (exp.var v) = show v" |
"showsp_bexp bexp.true = show ''True''" |
"showsp_bexp (bexp.not b) = show ''~'' @ showsp_bexp b" |
"showsp_bexp (bexp.and a b) = showsp_bexp a @ show '' && '' @ showsp_bexp b" |
"showsp_bexp (bexp.or a b) = show ''('' @ showsp_bexp a @ show '' || '' @ showsp_bexp b @ show '')''" |
"showsp_bexp (bexp.imply a b) = show ''('' @ showsp_bexp a @ show '' -> '' @ showsp_bexp b @ show '')''" |
"showsp_bexp (bexp.eq x y) =  showsp_exp x @ show '' = '' @ showsp_exp y" |
"showsp_bexp (bexp.le x y) = showsp_exp x @ show '' <= '' @ showsp_exp y" |
"showsp_bexp (bexp.lt x y) = showsp_exp x @ show '' < '' @ showsp_exp y" |
"showsp_bexp (bexp.ge x y) = showsp_exp x @ show '' >= '' @ showsp_exp y" |
"showsp_bexp (bexp.gt x y) = showsp_exp x @ show '' > '' @ showsp_exp y"

instantiation exp:: ("show", "show") "show" begin
  definition "shows_prec_exp (n::nat) e s \<equiv> (showsp_exp e) @ s"
  definition "shows_list_exp xs s \<equiv> 
    map showsp_exp xs |> intersperse '', '' |> (\<lambda>xs. ''['' @ concat xs @ '']'' @ s)"
instance 
  apply standard
  subgoal for _ e s s'
    apply (cases e)
    unfolding shows_prec_exp_def by simp+
  subgoal for xs s s'
    unfolding shows_list_exp_def by simp+
  done
end

instantiation bexp:: ("show", "show") "show" begin
  definition "shows_prec_bexp (n::nat) e s \<equiv> showsp_bexp e @ s"
  definition "shows_list_bexp xs s \<equiv> 
    map showsp_bexp xs |> intersperse '', '' |> (\<lambda>xs. ''['' @ concat xs @ '']'' @ s)"
instance 
  apply standard
  subgoal for _ e s s'
    apply (cases e)
    unfolding shows_prec_bexp_def by simp+
  subgoal for xs s s'
    unfolding shows_list_bexp_def by simp+
  done
end

fun update_to_str::"'a::show \<times> ('v::show, 'c::show) exp \<Rightarrow> string" where
"update_to_str (v, e) = show v @ show '' := '' @ show e"

fun reset_to_str::"String.literal \<Rightarrow> string" where
"reset_to_str r = show r @ show '' := '' @ show (0::int)"

(* fun showsp_acconstraint::"('c::show, 't::show) acconstraint \<Rightarrow> string \<Rightarrow> string" where
"showsp_acconstraint (acconstraint.LT c t) = shows c o shows '' < '' o shows t" |
"showsp_acconstraint (acconstraint.LE c t) = shows c o shows '' <= '' o shows t" |
"showsp_acconstraint (acconstraint.EQ c t) = shows c o shows '' = '' o shows t" |
"showsp_acconstraint (acconstraint.GT c t) = shows c o shows '' > '' o shows t" |
"showsp_acconstraint (acconstraint.GE c t) = shows c o shows '' >= '' o shows t"

instantiation acconstraint:: ("show", "show") "show" begin
  definition "shows_prec_acconstraint (n::nat) e \<equiv> showsp_acconstraint e"
 (*  definition "shows_list_acconstraint xs \<equiv> showsp_list (\<lambda>n x. showsp_acconstraint x) 0 xs" *)
instance sorry
end *)

fun print_acconstraint::"('a::show, 'b::show) acconstraint \<Rightarrow> string" where
"print_acconstraint (acconstraint.LE c t) = show c @ show '' <= '' @ show t" |
"print_acconstraint (acconstraint.LT c t) = show c @ show '' < '' @ show t" |
"print_acconstraint (acconstraint.EQ c t) = show c @ show '' = '' @ show t" |
"print_acconstraint (acconstraint.GT c t) = show c @ show '' > '' @ show t" |
"print_acconstraint (acconstraint.GE c t) = show c @ show '' >= '' @ show t" 

abbreviation "bexp_false \<equiv> bexp.not bexp.true"

fun simp_guard_bexp::"('a, 'b) bexp \<Rightarrow> ('a, 'b) bexp" where
"simp_guard_bexp bexp.true = bexp.true" |
"simp_guard_bexp (bexp.not b) = bexp.not (simp_guard_bexp b)" |
"simp_guard_bexp (bexp.and a b) = (case (simp_guard_bexp a, simp_guard_bexp b) of
  (bexp_false, _) \<Rightarrow> bexp_false
| (_, bexp_false) \<Rightarrow> bexp_false
| (bexp.true, b)  \<Rightarrow> b
| (b, bexp.true)  \<Rightarrow> b
| (b, c)          \<Rightarrow> bexp.and b c)" |
"simp_guard_bexp (bexp.or a b) = (case (simp_guard_bexp a, simp_guard_bexp b) of
  (bexp.true, _)  \<Rightarrow> bexp.true
| (_, bexp.true)  \<Rightarrow> bexp.true
| (bexp_false, b) \<Rightarrow> b
| (b, bexp_false) \<Rightarrow> b
| (b, c)          \<Rightarrow> bexp.or b c)" |
"simp_guard_bexp (bexp.imply a b) = (case (simp_guard_bexp a, simp_guard_bexp b) of
  (bexp.true, b)  \<Rightarrow> b
| (_, bexp.true)  \<Rightarrow> bexp.true
| (bexp_false, _) \<Rightarrow> bexp.true
| (_, bexp_false) \<Rightarrow> bexp_false
| (b, c)          \<Rightarrow> bexp.imply b c)" |
"simp_guard_bexp c = c"



definition guard_bexp_to_list where
"guard_bexp_to_list g \<equiv> case simp_guard_bexp g of 
  bexp.true \<Rightarrow> []
| bexp_false \<Rightarrow> [bexp_false]
| x \<Rightarrow> [x]"

(* Guards are clock constraints. Invariants are expressions on variables.

  Remove vacuously satisfied constraints *)
definition inv_to_str::"(String.literal, int) acconstraint list 
  \<Rightarrow> (String.literal, int) bexp \<Rightarrow> string" where
"inv_to_str guards invariants \<equiv>
  let 
    invariants = map showsp_bexp (guard_bexp_to_list invariants);
    guards = (map print_acconstraint guards);
    pl = invariants @ guards
  in print_list '' && '' pl"


(* Simple_Network_Language_Export_Code.convert_edge *)
definition edge_to_JSON::"
    nat \<times> 
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times> 
    String.literal act \<times>
    (String.literal \<times> (String.literal, int) exp) list \<times>
    String.literal list \<times> 
    nat 
  \<Rightarrow> JSON" where
"edge_to_JSON e \<equiv> 
  let 
    (s, check, guard, label, upds, resets, t) = e;
    source = (''source'', JSON.Int s);
    target = (''target'', JSON.Int t);
    label = (''label'', String (showsp_act label ''''));
    upds = map update_to_str upds;
    resets = map reset_to_str resets;
    guards = (''guard'', String (inv_to_str guard check));
    updates = (''update'', String (print_list '', '' (upds @ resets)))
  in Object [source, label, target, guards, updates]
"

definition node_to_JSON::"
  (nat \<Rightarrow> String.literal option) 
  \<Rightarrow> (nat \<Rightarrow> (String.literal, int) acconstraint list option)
  \<Rightarrow> nat
  \<Rightarrow> JSON Error_List_Monad.result" where
"node_to_JSON id_to_name id_to_invs i \<equiv> do {
  let id = (''id'', JSON.Int i);

  name \<leftarrow> get_or_err ''Location has no name:'' id_to_name i;
  let name = (''name'', String (show name));
  let invs = default '''' (get (map_option (\<lambda>x. print_list '' && '' (map show x))) (id_to_invs i));
  let inv = (''invariant'', String invs);
  
  Result (Object [id, name, inv])
}"

(* What do edges look like? (s, ..., label, , s')

- labels are In, Out, Sil
- resets are sets of clocks
-  *)

(* |> err_msg (STR ''Error while converting locations'') *)

(* states are string literals. Edges are nta transitions. 
More or less inverse of Simple_Network_Language_Export_Code.convert_automaton *)
(* Invariants take clocks as string literals. *)
definition automaton_to_JSON::"
  String.literal \<times>
  (nat \<Rightarrow> String.literal option) \<times> 
  nat \<times>
  nat list \<times>
  nat list \<times>
  nat list \<times>
  (nat \<times>
    (String.literal, int) bexp \<times>
    (String.literal, int) acconstraint list \<times>
    String.literal act \<times> 
    (String.literal \<times> (String.literal, int) exp) list \<times> 
    String.literal list \<times> 
    nat) list \<times>
  (nat \<times> (String.literal, int) acconstraint list) list 
\<Rightarrow> JSON Error_List_Monad.result" where
"automaton_to_JSON a \<equiv> 
  let (name, id_to_name, init, nodes, committed, urgent, edges, invs) = a
  in 
  do {
    let name = (''name'', String (show name));
  
    let id_to_invs = map_of invs;
    
    let init = (''initial'', JSON.Int init);
  
    let edges = (''edges'', JSON.Array (map edge_to_JSON edges));

    nodes \<leftarrow> combine_map (node_to_JSON id_to_name id_to_invs) nodes;
    let nodes = (''nodes'', JSON.Array nodes);

    let urgent = (''urgent'', JSON.Array (map JSON.Int urgent));
    let committed = (''committed'', JSON.Array (map JSON.Int committed));

    Result (Object [name, init, nodes, committed, urgent, edges])
  } |> err_msg (''Error while converting automaton with name: '' @ show name |> String.implode)"

abbreviation "uncurry_opt f a b \<equiv> 
(case f a of 
  Some f' \<Rightarrow> f' b
| None \<Rightarrow> None)"

definition net_to_JSON::"
    (nat \<Rightarrow> String.literal option)
\<Rightarrow>  (String.literal \<times> 
      (nat \<Rightarrow> String.literal option) \<times>
      nat \<times> 
      nat list \<times>
      nat list \<times> 
      nat list \<times>                                                           
      (nat \<times>
        (String.literal, int) bexp \<times>
        (String.literal, int) acconstraint list \<times>
        String.literal act \<times>
        (String.literal \<times> (String.literal, int) exp) list \<times>
        String.literal list \<times>
        nat) list \<times>
      (nat \<times> (String.literal, int) cconstraint) list) list \<times>
      String.literal list \<times>
      (String.literal \<times> int \<times> int) list \<times>
      (nat, nat, String.literal, int) formula
  \<Rightarrow> JSON Error_List_Monad.result" where
"net_to_JSON ids_to_names a \<equiv>
  let (automata, clocks, vars, formula) = a
  in 
  do {
    let auto_indexes = uncurry_opt (map_of (zip (map fst automata) (map (fst o snd) automata)));

    formula \<leftarrow> formula_to_JSON ids_to_names auto_indexes formula;
    
    automata \<leftarrow> combine_map automaton_to_JSON automata;
    let automata = (''automata'', JSON.Array automata);
    let clocks = (''clocks'', String (print_list '', '' clocks));
    Result (Object [automata, formula, bounded_vars_to_vars_and_bounds vars, clocks])
  }
" 

(* No information about clocks in these. Extract clocks? *)
(* The convert function extracts more information that is necessary for printing. To do: Implement
    simpler convert function for these types? *)

definition test3 where "test3 \<equiv>
 STR ''{
    \"info\": \"Derived from the Uppaal benchmarks found at https://www.it.uu.se/research/group/darts/uppaal/benchmarks/\",
    \"automata\": [
        {
            \"name\": \"ST2\",
            \"initial\": 9,
            \"nodes\": [
                {
                    \"id\": 14,
                    \"name\": \"y_idle\",
                    \"x\": 458.2894592285156,
                    \"y\": 442.4790954589844,
                    \"invariant\": \"\"
                }
            ],
            \"edges\": [
                {
                    \"source\": 9,
                    \"target\": 12,
                    \"guard\": \"\",
                    \"label\": \"tt1?\",
                    \"update\": \"y2 := 0, x2 := 0\"
                }
            ]
        }
    ],
    \"clocks\": \"x0, x1, y1, z1, x2, y2, z2\",
    \"vars\": \"id[-1:2]\",
    \"formula\": \"E<>  (ST2.y_idle)\"
}''"

definition "parse_convert s \<equiv> do {
  parse json s \<bind> convert
}
"

value [code] "parse json test3"

value [code] "do {
  json \<leftarrow> parse json test3;
  convert json
}
"

ML \<open>
  fun do_parse_convert file =
  let
    val s = file_to_string file;
  in                                                    
    @{code parse_convert} s 
  end
\<close>

ML \<open>
  (* Write string to file *)
  fun string_to_file s name = let
    val f = TextIO.openOut name
    val s = TextIO.output (f, s)
    val _ = TextIO.closeOut f
  in s end
\<close>

ML_val \<open>OS.FileSys.getDir()\<close>

(* ML_val \<open>
  do_parse_convert "certificates/planning.muntax"
\<close>
 *)
definition goal_automaton where
"goal_automaton \<equiv> (
  STR ''main'', 
  STR ''start'',
  [],
  [],
  [ (STR ''start'', 
    bexp.true, 
    [], 
    Sil (STR ''''), 
    [
      (STR ''lock'', const 1),
      (STR ''pf11'', const 1),
      (STR ''ef12'', const 1),
      (STR ''s1'', const 1)
    ],
    [],
    STR ''plan''),
    (STR ''plan'', 
    eq (var STR ''lock'') (const (1)), 
    [], 
    Sil (STR ''''), 
    [
      (STR ''lock'', const 0),
      (STR ''pf11'', const 1),
      (STR ''ef12'', const 1),
      (STR ''s1'', const 1)
    ],
    [],
    STR ''goal'')
  ],
  []
)"(* 

value [code] "automaton_to_JSON goal_automaton"


definition vars where
"vars \<equiv> [(STR ''pf11'', 0::nat, 1::nat), (STR ''ef11'', 0, 1), (STR ''s1'', 0::nat, 1::nat), (STR ''lock'', 0, 1)]"

value [code] "bounded_vars_to_vars_and_bounds vars"

definition clocks where
"clocks \<equiv> []"

definition form where
"form \<equiv> (formula.EX (loc (STR ''main'') (STR ''goal'')))"


value [code] "do {
auto \<leftarrow> automaton_to_JSON goal_automaton;
let s = show auto;
s |> Result
}"

value [code] "formula_to_JSON form"

definition [code]: "network \<equiv> (
  [goal_automaton], vars, clocks, form
)
"

definition [code]: "net_to_string net \<equiv> 
(case net_to_JSON net of 
  Result j \<Rightarrow> show j
| Error e \<Rightarrow> show e) |> String.implode"


definition "test_net \<equiv> net_to_string network"
 *)
ML_val \<open>OS.FileSys.getDir()\<close>

(* ML_val \<open>
string_to_file @{code "test_net"} "test_output/net.json"
\<close> *)



end