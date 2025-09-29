(* This is the grammar for PDDL. We tried to follow the grammar spec by Kovacs as closely as we could. *)


(* Some utility functions. *)
fun println x = print (x ^ "\n")

fun exit_fail msg = (
  println msg;
  OS.Process.exit(OS.Process.failure)
)

structure PDDL =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser
  open TEMPORAL_PDDL_Checker_Exported

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure PDDLDef :> LANGUAGE_DEF =
  struct

    type scanner = SubstringMonoStreamable.elem CharParser.charParser
    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = SOME ";"
    val nestedComments = false

    val identLetter    = alphaNum <|> oneOf (String.explode "_-,:;=") (*Idents can be separated with " " or \n and can contain [Aa-Zz], [0-9], "-", "_"*)
    val identStart     = identLetter
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart
    val reservedNames  = [":requirements", ":strips", ":equality", ":typing", ":action-costs", ":negative-preconditions", ":disjunctive-preconditions", ":durative-actions", ":duration-inequalities",
                          "define", "domain",
                          ":predicates", "either", ":functions",
                          ":types", (*"object",*)
                          ":constants",
                          ":action", ":durative-action", ":parameters", ":duration", ":precondition", ":condition", ":effect", "-",
                          ":invariant", ":name", ":vars", ":set-constraint",
                          "=", "<=", ">=", "and", "or", "not", "number",
                          "increase", "total-cost",
                          "problem", ":domain", ":init", ":objects", ":goal", ":metric", "maximize", "minimize"
                          (*"at", "over", "start", "end", "all", "duration", "()", "eof" (* mark the end of a file *)*)]
    val reservedOpNames= []
    val caseSensitive  = false

  end

  val lineComment   =
  let fun comLine _  = newLine <|> done #"\n" <|> (anyChar >> $ comLine)
  in case PDDLDef.commentLine of
         SOME s => string s >> $ comLine return ()
       | NONE   => fail "Single-line comments not supported"
  end
  val mlComment      =
  case (PDDLDef.commentStart, PDDLDef.commentEnd) of
      (SOME st, SOME ed) =>
      let
    fun bcNest _   = try (string st) >> $contNest
    and contNest _ = try (string ed return ())
                                 <|> ($bcNest <|> (anyChar return ())) >> $contNest
    val bcU = try (string st) >> repeat (not (string ed) >> anyChar) >> string ed return ()
      in if PDDLDef.nestedComments then $ bcNest else bcU
      end
    | _ => fail "Multi-line comments not supported"
  val comment        = lineComment <|> mlComment

  (*type RAT = int * int (* nomiator * denominator *)*)

  type RAT = string * string option (* nomiator * denominator *)

  datatype PDDL_OBJ_CONS = 
    PDDL_OBJ_CONS of string (* Object or constant, identified by name *)
  | Rat_Ent of RAT
  | Func_Ent of string * PDDL_OBJ_CONS list
  fun pddl_obj_name (PDDL_OBJ_CONS n) = n

  datatype PDDL_VAR = PDDL_VAR of string
  fun pddl_var_name (PDDL_VAR n) = n

  datatype PDDL_PRIM_TYPE = PDDL_PRIM_TYPE of string
  fun pddl_prim_type_name (PDDL_PRIM_TYPE n) = n

  datatype PDDL_PRED = PDDL_PRED of string
  fun pddl_pred_name (PDDL_PRED pred_name) = pred_name

  datatype PDDL_TERM = OBJ_CONS_TERM of PDDL_OBJ_CONS
                       | VAR_TERM of PDDL_VAR

  type 'a PDDL_ATOM = 'a TEMPORAL_PDDL_Checker_Exported.atom; (*string * ('a list) *)

  datatype 'a PDDL_PROP =
    Prop_atom of  'a PDDL_ATOM
  | Prop_not of 'a PDDL_PROP
  | Prop_and of 'a PDDL_PROP list
  | Prop_or of 'a PDDL_PROP list
  (* | Prop_eq of 'a  * 'a *)
  | Fluent (*This is mainly to parse and ignore action costs*) ;

  (*  *)
  type PDDL_PRE_GD = PDDL_TERM PDDL_PROP option

  type C_EFFECT = PDDL_TERM PDDL_PROP option

  datatype PDDL_TIME_SPECIFIER = at_start | at_end | over_all

  type 'a PDDL_TIMED_LIST = (PDDL_TIME_SPECIFIER * 'a) list

  datatype PDDL_D_OP = d_op_leq | d_op_eq | d_op_geq

  datatype PDDL_DURATION_CONSTRAINT = 
    No_Const_Def of unit
  | Time_Const_Def of PDDL_TIME_SPECIFIER option * (PDDL_D_OP * RAT)
  | Func_Const_Def of PDDL_TIME_SPECIFIER option * (PDDL_D_OP * (string * PDDL_TERM list))

  type PDDL_DA_GD = (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option

  type PDDL_DA_EFFECT = (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option

  datatype PDDL_ACTION_DEF_BODY = 
    Simple_Action_Def_Body of ((unit * PDDL_PRE_GD) option) * ((unit * C_EFFECT) option)
  | Durative_Action_Def_Body of PDDL_DURATION_CONSTRAINT * (PDDL_DA_GD * PDDL_DA_EFFECT)
  (*  *)

  structure RTP = TokenParser (PDDLDef)
  open RTP

  val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
        (fn (x,xs) => Int.fromString (String.implode (x::xs)))) ?? "num expression"

  val lparen = (char #"(" ) ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

  val spaces_comm = repeatSkip (space wth (fn _ => ())|| comment)

  fun in_paren p = spaces_comm >> lparen >> spaces_comm >> p << spaces_comm << rparen << spaces_comm

  val pddl_name = identifier wth (String.map Char.toLower) ?? "pddl identifier" (*First char should be a letter*)

  val pddl_obj_cons = pddl_name wth (fn name => PDDL_OBJ_CONS name) ?? "pddl object or constant"


  fun pddl_reserved wrd = (reserved wrd) ?? "resereved word"

  (* parsing exact strings, that are not keywords *)
  fun string s = try ((lexeme (letter && (repeat (letter || digit)))) suchthat (fn (x,xs) => (String.implode (x::xs)) = s)) return () ?? "exact string"

  val require_key = (pddl_reserved ":strips" || pddl_reserved ":equality" ||  pddl_reserved ":typing" ||  pddl_reserved ":action-costs"
                      ||  pddl_reserved ":disjunctive-preconditions" ||  pddl_reserved ":negative-preconditions" 
                      ||  pddl_reserved ":durative-actions" ||  pddl_reserved ":duration-inequalities") ?? "require_key"
  val require_def = (in_paren(pddl_reserved ":requirements" >> repeat1 require_key)) ?? "require_def"

  val primitive_type = (pddl_name wth (fn tp => PDDL_PRIM_TYPE tp)
                        (*|| (pddl_reserved "object") wth (fn _ => "object")*)) ?? "prim_type"

  val type_ = ( in_paren (pddl_reserved "either" >> (repeat1 primitive_type))
               || (primitive_type wth (fn tp => (tp::[])))) ?? "type"

  fun typed_list x = repeat (((repeat1 x) && (pddl_reserved "-" >> type_))
                              || (repeat1 x) wth (fn tlist => (tlist, [PDDL_PRIM_TYPE "object"]))) ?? "typed_list"

  val pddl_type = pddl_name wth (fn name => PDDL_PRIM_TYPE name) ?? "pddl type"

  val types_def = (in_paren(pddl_reserved ":types" >> typed_list pddl_type)) ?? "types def"

  val constants_def = (in_paren(pddl_reserved ":constants" >> typed_list pddl_obj_cons)) ?? "consts def"

  val pddl_var = (((char #"?" ) && pddl_name) wth (fn (c, str) => PDDL_VAR (String.implode [c] ^ str))) ?? "?var_name"

  val predicate = pddl_name wth (fn name => PDDL_PRED name) ?? "pddl type"

  fun optional_typed_list x = (opt (typed_list x)
                                wth (fn parsed_typesOPT => (case parsed_typesOPT of (SOME parsed_types) => parsed_types
                                                                                     | _ => [])))

  val atomic_formula_skeleton = (in_paren (predicate && optional_typed_list pddl_var)) ?? "predicate"

  val predicates_def = (in_paren(pddl_reserved ":predicates" >> (repeat (atomic_formula_skeleton)))) ?? "predicates def"

  val function_type = pddl_reserved "number" ?? "function type"

  fun function_typed_list x =  repeat1 ((x && (pddl_reserved "-" >> function_type))
                                        || x wth (fn tlist => (tlist, ()))) ?? "function_typed_list"

  val function_symbol = (pddl_name || pddl_reserved "total-cost" wth (fn _ => "total-cost")) ?? "function symbol"

  val atomic_function_skeleton = (in_paren ((function_symbol && optional_typed_list pddl_var)
                                          || (pddl_reserved "total-cost" wth (fn _ => ("total-cost", [])))))
                                            (*action-cost is sometimes witout arguments*)
                                 ?? "atomic function skeleton"

  val functions_def = (in_paren(pddl_reserved ":functions" >>
                                (function_typed_list atomic_function_skeleton))) ?? "functions def"

  val function_term = in_paren(function_symbol && repeat pddl_var) wth (fn (x, _) => x) ?? "Function term" (*This is only to accommodate costs*)

  val term = (pddl_obj_cons wth (fn oc => OBJ_CONS_TERM oc) 
              || pddl_var wth (fn v => VAR_TERM v) (* || function_term *)) ?? "term"

  fun atomic_formula t = (in_paren(predicate && repeat t)
                             wth (fn (pred, tlist) => Prop_atom (PredAtm ((Pred (explode (pddl_pred_name pred))), tlist))))
                         || in_paren((pddl_reserved "=") && t && t)
                               wth (fn (eq, (t1, t2)) => Prop_atom (EqAtm (t1, t2))) ?? "Atomic formula"

  fun literal t = ((atomic_formula t) || (in_paren(pddl_reserved "not" && atomic_formula t)) wth (fn (_, t) =>  Prop_not t)) ?? "literal"

  (* Done: The n is disgusting, there must be a way to remove it.
      The parser combinator library implements repetitions with the fix function. 
      I remember this worked on a version of the PDDL parser, which I adapted *)
  fun GD x = fix (fn cont => (literal x ||
                in_paren(pddl_reserved "and" && (repeat1  (cont || literal x))) wth (fn (_, gd) => Prop_and gd) ||
                in_paren(pddl_reserved "or" && (repeat1  (cont || literal x))) wth (fn (_, gd) => Prop_or gd))) ?? "GD"

  fun pre_GD x = GD x ?? "pre GD"

  val assign_op = pddl_reserved "increase" ?? "assign_op"

  val f_head = (in_paren(function_symbol && repeat term)
                || function_symbol wth (fn s => (s, []))) ?? "assign_op"

  val f_exp = num ?? "assign_op"

  val p_effect  = ((atomic_formula term)
                    || (in_paren(pddl_reserved "not" && atomic_formula term))
                          wth (fn (_, t) =>  (Prop_not t))
                    || (in_paren(assign_op && f_head && f_exp))
                          wth (fn _ => Fluent)) ?? "p_effect"

  val c_effect  = p_effect ?? "c_effect"

  val effect = (c_effect || (in_paren(pddl_reserved "and" && repeat c_effect )) wth (fn (_, ceff) => (Prop_and ceff))) ?? "effect"

  fun emptyOR x = opt x

  val action_def_body = (opt (pddl_reserved ":precondition" && emptyOR (pre_GD term))
                         && opt (pddl_reserved ":effect" && emptyOR effect)) wth Simple_Action_Def_Body ?? "Action def body"

  val action_symbol = pddl_name

  val action_def = (in_paren(pddl_reserved ":action" >>
                    action_symbol
                    && (pddl_reserved ":parameters" >> (in_paren(typed_list pddl_var)))
                    && action_def_body)) ?? "action def"

  (* extension for durative actions *)

  val d_op = (char #"<" >> pddl_reserved "=" wth (fn () => d_op_leq)) 
          || (pddl_reserved "=" wth (fn () => d_op_eq)) 
          || (char #">" >> pddl_reserved "=" wth (fn () => d_op_geq)) ?? "d-op"

  (* parsing (postive) decimals as string *)
  val dec_num = ((lexeme ((char #"-" || digit) && (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                && opt ((char #".") >> (digit && lexeme (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                ) ?? "dec_num expression"

  val d_value = dec_num (*|| f_exp*) ?? "d value"

  val time_specifier = (string "start" wth (fn () => at_start) || string "end" wth (fn () => at_end)) ?? "time specifier"

  (* val simple_duration_constraint = (d_op >> char #"?" >> string "duration" >> (d_value || f_head)) ?? "simple duration constraint" *)

  val duration_constraint = ((string "()") wth No_Const_Def 
                            || in_paren (opt (string "at" >> time_specifier) && (d_op && char #"?" >> string "duration" >> d_value)) wth Time_Const_Def
                            || in_paren (opt (string "at" >> time_specifier) && (d_op && char #"?" >> string "duration" >> f_head)) wth Func_Const_Def) ?? "duration constraint"

  val interval = string "all" wth (fn () => over_all) ?? "interval"

  val timed_GD = ((string "at" >> (time_specifier && pre_GD term)) 
                || (string "over" >> (interval && pre_GD term))) ?? "timed GD"

  val pref_timed_GD = timed_GD ?? "pref timed GD"

  val da_GD = in_paren (opt ((pref_timed_GD wth (fn (tgd) => [tgd])) 
                          || (pddl_reserved "and" >> (repeat (in_paren pref_timed_GD) (* TODO: fix repeat *))))) ?? "da-GD" (* only allowing one level of (and ...)! *)

  val timed_effect = (string "at" >> (time_specifier && effect)) ?? "timed effect"

  val da_effect = in_paren (opt ((timed_effect wth (fn (teff) => [teff])) 
                              || (pddl_reserved "and" >> (repeat (in_paren timed_effect) (* TODO: fix repeat *))))) ?? "da effect"

  val durative_action_def_body = ((pddl_reserved ":duration" >> duration_constraint)
                                  && (pddl_reserved ":condition" >> da_GD)
                                  && (pddl_reserved ":effect" >> da_effect)) wth Durative_Action_Def_Body ?? "durative action def body"

  val durative_action_symbol = pddl_name

  val durative_action_def = (in_paren (pddl_reserved ":durative-action" >> durative_action_symbol
                             && (pddl_reserved ":parameters" >> (in_paren (typed_list pddl_var)))
                             && durative_action_def_body)) ?? "durative action def"

  val structure_def = (action_def || durative_action_def (*|| derived_def*) )?? "struct def"

  val invariant_symbol = (pddl_reserved ":name" >> pddl_name) ?? "invariant symbol"

  val quantification = (pddl_reserved ":vars" >> in_paren (typed_list pddl_var)) ?? "quantification"

  val constraints = (pddl_reserved ":set-constraint" >> pre_GD term) ?? "constraint"

  (*val invariant_def = (in_paren(pddl_reserved ":invariant" >> spaces >>
                                 (invariant_symbol << spaces) &&
                                 (quantification << spaces) &&
                                 (constraints << spaces))) ?? "invariants def"*)

  val invariant_def = in_paren ((pddl_reserved ":invariant" >> invariant_symbol)
                      && quantification
                      && constraints)?? "invariants def"

  val domain = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "domain" >> pddl_name)
                                                  >> (opt require_def)
                                                  && (opt types_def)
                                                  && (opt constants_def)
                                                  && (opt predicates_def)
                                                  (* && (opt functions_def) *)
                                                  && (repeat structure_def)
                                                  (* && (repeat invariant_def) *)
                                                  ) ?? "domain"

  val object_declar = in_paren(pddl_reserved ":objects" >> (typed_list pddl_obj_cons))

  val basic_fun_term = function_symbol wth (fn (x) => (x,[])) ||
                       in_paren(function_symbol && repeat pddl_obj_cons) ?? "basic function term"

  val init_el = (literal (pddl_obj_cons)
                  || in_paren((pddl_reserved "=") && basic_fun_term && d_value)
                               wth (fn (eq, (t1, t2)) => Prop_atom (EqAtm (Func_Ent t1, Rat_Ent t2)))
                 || in_paren((pddl_reserved "=") && basic_fun_term && pddl_obj_cons)
                               wth (fn (eq, (t1, t2)) => Fluent) (*if we have x = x in the init state, it will be igonored here, and readded later in initToIsabelle*)
                 ) ?? "init element"

  val init = in_paren(pddl_reserved ":init" >> repeat (init_el))


  (* The rule for goals is exactly as the one in Kovacs. It is wrong, nonetheless, since a goal
     should be only defined on GDs over objects or constants only and not terms!! *)

  val goal = in_paren(pddl_reserved ":goal" >> pre_GD term)

  val optimisation = (pddl_reserved "maximize" || pddl_reserved "minimize") ?? "Optimisation"

  val metric_f_exp = function_symbol

  val metric_spec = in_paren(pddl_reserved ":metric" >> optimisation >> in_paren(metric_f_exp))

  val problem = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "problem" >> pddl_name)
                                                >> in_paren(pddl_reserved ":domain" >> pddl_name)
                                                >> (opt (require_def))
                                                  && (object_declar)
                                                  && init
                                                  && goal
                                                  && opt metric_spec) ?? "problem"

  (* t: (a p1 ... pn) [t'] *)
  val lbracket = (char #"[" ) ?? "lbracket"
  val rbracket = (char #"]" ) ?? "rbracket"

  fun in_brackets p = spaces_comm >> lbracket >> spaces_comm >> p << spaces_comm << rbracket << spaces_comm

  val plan_action = in_paren(pddl_name && repeat pddl_obj_cons) && opt (in_brackets dec_num) ?? "plan action"
  val plan = spaces_comm >> repeat (dec_num && ((char #":" ) >> plan_action)) << spaces_comm ?? "plan"

  val test = invariant_def ?? "test"

  val end_of_file_marker = (char #"#" ) >> (string "eof") >> (char #"#" ) ?? "end of file marker"
  fun end_of_file x = x << end_of_file_marker ?? "end of file"

end

open PDDL

  (*These are the data types of the objects parsed above.*)

  (*Types for the domain*)

  (* type PDDL_PRE_GD = PDDL_TERM PDDL_PROP option *)

  (* type C_EFFECT = PDDL_TERM PDDL_PROP option *)

  (* type PDDL_ACTION_DEF_BODY = ((unit * PDDL_PRE_GD) option) * ((unit * C_EFFECT) option) *)

  type PDDL_ACTION_SYMBOL = string

  type PDDL_TYPE = PDDL_PRIM_TYPE list

  type 'a PDDL_TYPED_LIST = (('a list) * PDDL_TYPE) list

  type PDDL_TYPES_DEF = (PDDL_PRIM_TYPE PDDL_TYPED_LIST) option

  type PDDL_ACTION = PDDL_ACTION_SYMBOL *
                          (PDDL_VAR PDDL_TYPED_LIST *
                                     (PDDL_ACTION_DEF_BODY))

  type PDDL_ACTIONS_DEF = (PDDL_ACTION list)

  type PDDL_CONSTS_DEF = (PDDL_OBJ_CONS PDDL_TYPED_LIST) option

  type ATOMIC_FORM_SKEL = PDDL_PRED * (PDDL_VAR PDDL_TYPED_LIST)

  type 'a FUN_TYPED_LIST = (('a list) * unit) list

  type ATOMIC_FUN_SKELETON = string * (PDDL_VAR PDDL_TYPED_LIST)

  type PDDL_FUNS_DEF = ATOMIC_FUN_SKELETON FUN_TYPED_LIST option

  type PDDL_PRED_DEF = PDDL_PRED list option

  type PDDL_REQUIRE_DEF = (unit list) option

  (* Types for the instance *)

  type PDDL_OBJ_DEF = PDDL_OBJ_CONS PDDL_TYPED_LIST

  type PDDL_INIT_EL = PDDL_OBJ_CONS PDDL_PROP

  type PDDL_INIT = PDDL_INIT_EL list

  type PDDL_GOAL = PDDL_TERM PDDL_PROP

  type METRIC = string option

  (*Types for the plan*)

  type PDDL_PLAN_ACTION = (string * (PDDL_OBJ_CONS list)) * RAT option 
  fun pddl_plan_action_name (tstart, name, args, tdur_opt) = name
  fun pddl_plan_action_args (tstart, name, args, tdur_opt) = args


  (* Functions that are used to convert parsed types to Isabelle type and/or strings. They
     are common between both validating plans and invariants.*)

  fun stringToString s = "''" ^ s ^ "''"

  fun pddlVarToString (v:PDDL_VAR) = "Var " ^ stringToString (pddl_var_name v)

  fun pddlObjConsToString (oc:PDDL_OBJ_CONS) = "Obj " ^ stringToString (pddl_obj_name oc)

  fun pddlVarTermToString term = 

    case term of VAR_TERM v => pddlVarToString v
             | _ => exit_fail ("Var expected, but obejct found: pddlVarTermToString " ^ (pddlObjConsTermToString term))

  and pddlObjConsTermToString term = 
    case term of OBJ_CONS_TERM oc => pddlObjConsToString oc
             | _ => exit_fail ("Object expected, but variable found: pddlObjConsTermToString " ^ (pddlVarTermToString term))

  fun pddlTypedListXTypesConv typedList cat_fn mk_pair_fn obj_v_conv_fun type_conv_fun =
    let
      fun wrap_var_with_type t = (fn v => mk_pair_fn (obj_v_conv_fun v) (type_conv_fun t))
    in
      cat_fn (map (fn (vars, type_) => (map (wrap_var_with_type type_) vars)) typedList)
    end

  fun extractFlatTypedList cat_fn str_fn mk_pair_fn (typedList :PDDL_PRIM_TYPE PDDL_TYPED_LIST) = let
    fun sng_typ [t] = str_fn (pddl_prim_type_name t)
      | sng_typ _ = exit_fail "Either-types not supported as supertypes"
  in
    cat_fn (map (fn (ts, supt) => map (fn t => mk_pair_fn (str_fn (pddl_prim_type_name t)) (sng_typ supt)) ts) typedList)
  end


(*Some utility functions*)

fun fst (x,y) = x
fun snd (x,y) = y
fun pddl_prop_map f prop =
 case prop of Prop_atom atm => Prop_atom (map_atom f atm)
           | Prop_not sub_prop => Prop_not (pddl_prop_map f sub_prop)
           | Prop_and props => Prop_and (map (pddl_prop_map f) props)
           | Prop_or props => Prop_or (map (pddl_prop_map f) props)
           (* | Prop_eq (l,r) => Prop_eq (f l, f r) *)
           | Fluent => Fluent;
