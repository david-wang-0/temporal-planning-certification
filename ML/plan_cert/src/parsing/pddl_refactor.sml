(* This is the grammar for PDDL. We tried to follow the grammar spec by Kovacs as closely as we could. *)


(* Some utility functions. *)
fun println x = print (x ^ "\n")

fun fst (x,y) = x
fun snd (x,y) = y

fun exit_fail msg = (
  println msg;
  OS.Process.exit(OS.Process.failure)
)

fun intToIsaInt x = Continuous_PDDL_Checker_Exported.Int_of_integer x

fun intToIsaNat x = Continuous_PDDL_Checker_Exported.nat_of_integer x

fun charToNat c = 
    case Int.fromString (str c) of
        SOME i => intToIsaNat i 
      | NONE => (println ("Not a number: " ^ (str c)); OS.Process.exit(OS.Process.failure))

fun stringPairToIsaRat (s1,s2) =
    case s2 of
      SOME s2' => Continuous_PDDL_Checker_Exported.rat_of_digits_pair (map charToNat (String.explode s1), map charToNat (String.explode s2'))
    | NONE => Continuous_PDDL_Checker_Exported.of_int (intToIsaInt (valOf (Int.fromString s1)))

structure PDDL =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser
  open Continuous_PDDL_Checker_Exported

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

    val identLetter    = alphaNum <|> oneOf (String.explode "_-,:;=<>*#/+") (*Idents can be separated with " " or \n and can contain [Aa-Zz], [0-9], "-", "_"*)
    val identStart     = letter <|> oneOf (String.explode "_-,:;=<>*#/+")
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart
    val reservedNames  = [":requirements", ":strips", ":equality", ":adl", ":time", ":typing", ":action-costs", ":negative-preconditions", ":disjunctive-preconditions", ":durative-actions", ":duration-inequalities", ":fluents", ":numeric-fluents", ":continuous-effects", ":conditional-effects",
                          "define", "domain",
                          ":predicates", "either", ":functions",
                          ":types", (*"object",*)
                          ":constants",
                          ":action", ":durative-action", ":parameters", ":duration", ":precondition", ":condition", ":effect", 
                          "pi", "sin", "cos", "exp", (* Not really PDDL keywords *)
                          "=", "<=", ">=", ">", "<",
                          "+", "-", "*", "/", "#t",
                          "and", "or", "not", "imply", "forall", "exists", "number",
                          "assign", "scale-up", "increase", "decrease", "total-cost",
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

  datatype PDDL_OBJ_CONS = PDDL_OBJ_CONS of string (* Object identified by name *)
  fun pddl_obj_name (PDDL_OBJ_CONS n) = n

  datatype PDDL_VAR = PDDL_VAR of string
  fun pddl_var_name (PDDL_VAR n) = n

  datatype PDDL_PRIM_TYPE = PDDL_PRIM_TYPE of string
  fun pddl_prim_type_name (PDDL_PRIM_TYPE n) = n

  datatype PDDL_PRED = PDDL_PRED of string
  fun pddl_pred_name (PDDL_PRED pred_name) = pred_name

  datatype PDDL_TERM = OBJ_CONS_TERM of PDDL_OBJ_CONS
                       | VAR_TERM of PDDL_VAR

  type 'a PDDL_PNE = 'a  Continuous_PDDL_Checker_Exported.primitive_numeric_expression;

  type 'a PDDL_FEXP = 'a Continuous_PDDL_Checker_Exported.numeric_expression;

  type 'a PDDL_ATOM = 'a Continuous_PDDL_Checker_Exported.atom; (*string * ('a list) *)

  datatype 'a PDDL_PROP =
    Prop_atom of  'a PDDL_ATOM
  | Prop_not of 'a PDDL_PROP
  | Prop_and of 'a PDDL_PROP list
  | Prop_or of 'a PDDL_PROP list
  | Prop_imply of 'a PDDL_PROP * 'a PDDL_PROP
  | Prop_all of (PDDL_VAR * PDDL_PRIM_TYPE) list * 'a PDDL_PROP
  | Prop_ex  of (PDDL_VAR * PDDL_PRIM_TYPE) list * 'a PDDL_PROP

  type PDDL_PRE_GD = PDDL_TERM PDDL_PROP option

  type PDDL_TIME_SPECIFIER = Continuous_PDDL_Checker_Exported.temporal_annotation

  datatype LOGIC_EFFECT_OR_NUMERIC_EFFECT = LOGIC_EFFECT of PDDL_TERM PDDL_PROP
                                            | NUMERIC_EFFECT of PDDL_TERM numeric_effect
                                            | FORALL_EFFECT of (PDDL_VAR * PDDL_PRIM_TYPE) list * LOGIC_EFFECT_OR_NUMERIC_EFFECT list

  datatype SNAP_EFFECT_OR_CONTINUOUS_EFFECT = SNAP_EFFECT of PDDL_TIME_SPECIFIER * LOGIC_EFFECT_OR_NUMERIC_EFFECT
                                              | CONTINUOUS_EFFECT of PDDL_TERM Continuous_PDDL_Checker_Exported.ast_continuous_effect
                                              | FORALL_SNAP of (PDDL_VAR * PDDL_PRIM_TYPE) list * SNAP_EFFECT_OR_CONTINUOUS_EFFECT list


  type 'a PDDL_TIMED_LIST = (PDDL_TIME_SPECIFIER * 'a) list

  type PDDL_DA_GD = (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option

  type PDDL_DA_EFFECT = (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option

  datatype PDDL_ACTION_DEF_BODY = 
    Simple_Action_Def_Body of ((unit * PDDL_PRE_GD) option) * (LOGIC_EFFECT_OR_NUMERIC_EFFECT list option)
  | Durative_Action_Def_Body of ((PDDL_TIME_SPECIFIER * PDDL_TERM Continuous_PDDL_Checker_Exported.duration_constraint) list) * PDDL_DA_GD * (SNAP_EFFECT_OR_CONTINUOUS_EFFECT list option)
  (*  *)

  structure RTP = TokenParser (PDDLDef)
  open RTP

  val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
        (fn (x,xs) => Int.fromString (String.implode (x::xs)))) ?? "num expression"

  (* parsing (postive) decimals as string *)
  val dec_num = (((lexeme ((char #"-" || digit) && (repeat digit)) wth (fn (x,xs) => String.implode (x::xs)))
                && opt ((char #".") >> (digit && lexeme (repeat digit) wth (fn (x,xs) => String.implode (x::xs))))
                ) wth (fn (s1, s2) => stringPairToIsaRat (s1, s2))) ?? "dec_num expression"

  val lparen = (char #"(" ) ?? "lparen"
  val rparen = (char #")" ) ?? "rparen"

  val spaces_comm = repeatSkip (space wth (fn _ => ())|| comment)

  fun in_paren p = spaces_comm >> lparen >> spaces_comm >> p << spaces_comm << rparen << spaces_comm

  val pddl_name = identifier wth (String.map Char.toLower) ?? "pddl identifier" (*First char should be a letter*)

  val pddl_obj_cons = pddl_name wth (fn name => PDDL_OBJ_CONS name) ?? "pddl object or constant"


  fun pddl_reserved wrd = (reserved wrd) ?? "reserved word"

  (* parsing exact strings, that are not keywords *)
  fun string s = try ((lexeme (letter && (repeat (letter || digit)))) suchthat (fn (x,xs) => (String.implode (x::xs)) = s)) return () ?? "exact string"

  val require_key = (pddl_reserved ":strips" || pddl_reserved ":equality" ||  pddl_reserved ":typing" ||  pddl_reserved ":action-costs"
                      ||  pddl_reserved ":disjunctive-preconditions" ||  pddl_reserved ":negative-preconditions" || pddl_reserved ":adl"
                      ||  pddl_reserved ":durative-actions" ||  pddl_reserved ":duration-inequalities" || pddl_reserved ":time" 
                      ||  pddl_reserved ":fluents" ||  pddl_reserved ":numeric-fluents" ||pddl_reserved ":continuous-effects" || pddl_reserved ":conditional-effects") ?? "require_key"
  val require_def = (in_paren(pddl_reserved ":requirements" >> repeat1 require_key)) ?? "require_def"

  val primitive_type = (pddl_name wth (fn tp => PDDL_PRIM_TYPE tp)) ?? "prim_type"

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

  (* a quantifier binder `(?x ?y - T ?z - U ...)` -> flat [(?x,T),(?y,T),(?z,U),...];
     a var with no explicit type defaults to `object`. *)
  fun flatten_binder (tl : (PDDL_VAR list * PDDL_PRIM_TYPE list) list) =
        List.concat (map (fn (vars, tys) =>
             let val t = case tys of (h :: _) => h | [] => PDDL_PRIM_TYPE "object"
             in map (fn v => (v, t)) vars end) tl)
  val quant_binder = (in_paren (typed_list pddl_var) wth flatten_binder) ?? "quantifier binder"

  val atomic_formula_skeleton = (in_paren (predicate && optional_typed_list pddl_var)) ?? "predicate"

  val predicates_def = (in_paren(pddl_reserved ":predicates" >> (repeat (atomic_formula_skeleton)))) ?? "predicates def"

  val function_type = pddl_reserved "number" ?? "function type"

  fun function_typed_list x =  repeat1 ((x && (pddl_reserved "-" >> function_type))
                                        || x wth (fn tlist => (tlist, ()))) ?? "function_typed_list"

  val function_symbol = (pddl_name wth (fn s => Func s) 
                         || pddl_reserved "total-cost" wth (fn _ => Func "total-cost")) ?? "function symbol"

  val atomic_function_skeleton = (in_paren ((function_symbol && optional_typed_list pddl_var)
                                          || (pddl_reserved "total-cost" wth (fn _ => (Func "total-cost", [])))))
                                            (*action-cost is sometimes witout arguments*)
                                 ?? "atomic function skeleton"

  val functions_def = (in_paren(pddl_reserved ":functions" >>
                                (function_typed_list atomic_function_skeleton))) ?? "functions def"

  val function_term = in_paren(function_symbol && repeat pddl_var) wth (fn (x, _) => x) ?? "Function term" (*This is only to accommodate costs*)

  val term = (pddl_obj_cons wth (fn oc => OBJ_CONS_TERM oc) 
              || pddl_var wth (fn v => VAR_TERM v) (* || function_term *)) ?? "term"


  fun atomic_formula t = (in_paren(predicate && repeat t)
                             wth (fn (pred, tlist) => Prop_atom (PredAtm ((Pred (pddl_pred_name pred)), tlist)))
                          || in_paren((pddl_reserved "=") && t && t)
                               wth (fn (_, (t1, t2)) => Prop_atom (EqAtm (t1, t2)))) ?? "Atomic formula"

  fun literal t = ((atomic_formula t) || (in_paren(pddl_reserved "not" && atomic_formula t)) wth (fn (_, t) =>  Prop_not t)) ?? "literal"

  val f_head = (in_paren(function_symbol && repeat term)
                || function_symbol wth (fn s => (s, []))) ?? "f_head"

  val f_exp_base = (f_head wth (fn (f, args) => FunctionExpr (PNE (f, args)))
                    || pddl_reserved "pi" wth (fn _ => PiExpr) 
                    || dec_num wth ConstantExpr) ?? "f_exp_base"

  val f_exp_da_base = (f_exp_base 
                      || (char #"?" >> string "duration") wth (fn _ => DurationExpr)) ?? "f_exp_da_base"
  
  (*TODO: The n is disgusting, there must be a way to remove it.*)

  fun f_exp' n base = (base
                 || in_paren (pddl_reserved "sin" >> (if n >= 0 then f_exp' (n - 1) base else base)) wth SinExpr
                 || in_paren (pddl_reserved "cos" >> (if n >= 0 then f_exp' (n - 1) base else base)) wth CosExpr
                 || in_paren (pddl_reserved "exp" >> (if n >= 0 then f_exp' (n - 1) base else base)) wth ExpExpr
                 || in_paren(pddl_reserved "-" && (if n >= 0 then f_exp' (n - 1) base else base)) wth (fn (_, a) => SubExpr (ConstantExpr (of_int (intToIsaInt 0)), a))
                 || in_paren(pddl_reserved "+" && (if n >= 0 then f_exp' (n - 1) base && f_exp' (n - 1) base else base && base)) wth (fn (_, (a, b)) => AddExpr (a,b))
                 || in_paren(pddl_reserved "-" && (if n >= 0 then f_exp' (n - 1) base && f_exp' (n - 1) base else base && base)) wth (fn (_, (a, b)) => SubExpr (a,b))
                 || in_paren(pddl_reserved "*" && (if n >= 0 then f_exp' (n - 1) base && f_exp' (n - 1) base else base && base)) wth (fn (_, (a, b)) => MulExpr (a,b))
                 || in_paren(pddl_reserved "/" && (if n >= 0 then f_exp' (n - 1) base && f_exp' (n - 1) base else base && base)) wth (fn (_, (a, b)) => DivExpr (a,b))) ?? "f_exp"

  val f_exp = f_exp' 3 f_exp_base ?? "f_exp"
  val f_exp_da = f_exp' 3 f_exp_da_base ?? "f_exp_da"

  fun GD x fe = fix (fn cont =>
                in_paren(pddl_reserved "forall" >> (quant_binder && cont)) wth (fn (b, g) => Prop_all (b, g)) ||
                in_paren(pddl_reserved "exists" >> (quant_binder && cont)) wth (fn (b, g) => Prop_ex (b, g)) ||
                literal x ||
                in_paren(pddl_reserved "=" && fe && fe) wth (fn (_, (expa, expb)) => Prop_atom (NumericEqAtm (expa, expb))) ||
                in_paren(pddl_reserved "<" && fe && fe) wth (fn (_, (expa, expb)) => Prop_atom (NumericLessAtm (expa, expb))) ||
                in_paren(pddl_reserved "<=" && fe && fe) wth (fn (_, (expa, expb)) => Prop_atom (NumericLEAtm (expa, expb))) ||
                in_paren(pddl_reserved ">" && fe && fe) wth (fn (_, (expa, expb)) => Prop_atom (NumericGreaterAtm (expa, expb))) ||
                in_paren(pddl_reserved ">=" && fe && fe) wth (fn (_, (expa, expb)) => Prop_atom (NumericGEAtm (expa, expb))) ||
                in_paren(pddl_reserved "and" && repeat cont) wth (fn (_, gd) => Prop_and gd) ||
                in_paren(pddl_reserved "or" && repeat cont) wth (fn (_, gd) => Prop_or gd) ||
                in_paren(pddl_reserved "imply" && (cont && cont)) wth (fn (_, (gda, gdb)) => Prop_imply (gda, gdb))) ?? "GD"

  fun pre_GD x = GD x f_exp ?? "pre GD"

  val assign_op = (pddl_reserved "increase" wth (fn () => Increase)
                   || pddl_reserved "assign" wth (fn () => Assign)
                   || pddl_reserved "scale-up" wth (fn () => ScaleUp)
                   || pddl_reserved "scale-down" wth (fn () => ScaleDown)
                   || pddl_reserved "decrease" wth (fn () => Decrease)) ?? "assign_op"


  val p_effect  = ((atomic_formula term) wth LOGIC_EFFECT
                    || (in_paren(pddl_reserved "not" && atomic_formula term))
                          wth (fn (_, t) => LOGIC_EFFECT (Prop_not t))
                    || (in_paren(assign_op && f_head && f_exp))
                          wth (fn (operator, (l, r)) => NUMERIC_EFFECT (NumericEffect (operator, PNE l, r)))) ?? "p_effect"
                          
  val p_effect_da  = (p_effect
                      || (in_paren(assign_op && f_head && f_exp_da))
                          wth (fn (operator, (l, r)) => NUMERIC_EFFECT (NumericEffect (operator, PNE l, r)))) ?? "p_effect_da"

  val c_effect  = p_effect ?? "c_effect"
  
  val c_effect_da = p_effect_da ?? "c_effect_da"

  (* an effect is a (possibly nested / quantified) list of primitive effects.  `(forall (b) e)`
     produces one FORALL_EFFECT carrying the (list of) sub-effects; `(and e ...)` flattens. *)
  val effect = fix (fn eff =>
                  c_effect wth (fn e => [e])
                  || (in_paren(pddl_reserved "and" && repeat eff)) wth (fn (_, effs) => List.concat effs)
                  || (in_paren(pddl_reserved "forall" >> (quant_binder && eff)))
                       wth (fn (b, body) => [FORALL_EFFECT (b, body)])) ?? "effect"

  fun emptyOR x = opt x

  val action_def_body = (opt (pddl_reserved ":precondition" && emptyOR (pre_GD term))
                         && opt (pddl_reserved ":effect" && emptyOR effect)) 
                         wth (fn (pre, eff) => Simple_Action_Def_Body (pre, Option.join (Option.map snd eff))) ?? "Action def body"

  val action_symbol = pddl_name

  val action_def = (in_paren(pddl_reserved ":action" >>
                    action_symbol
                    && (pddl_reserved ":parameters" >> (in_paren(typed_list pddl_var)))
                    && action_def_body)) ?? "action def"

  (* extension for durative actions *)

  val d_op = (pddl_reserved "<=" wth (fn () => LEQ)) 
          || (pddl_reserved "=" wth (fn () => EQ)) 
          || (pddl_reserved ">=" wth (fn () => GEQ)) ?? "d-op"

  val d_value = dec_num (*|| f_exp*) ?? "d value"

  val time_specifier = (string "start" wth (fn () => At_Start) 
                       || string "end" wth (fn () => At_End)) ?? "time specifier"

  (* val simple_duration_constraint = (d_op >> char #"?" >> string "duration" >> (d_value || f_head)) ?? "simple duration constraint" *)

  val simple_duration_constraint = ((opt (string "at" >> time_specifier) && (d_op && (char #"?" >> string "duration") && f_exp)) wth (fn (t, (operator, (_, x))) => (getOpt (t, At_Start), DurationConstraint (operator, x)))
                                    ) ?? "simple duration constraint"

  val duration_constraint = (in_paren (opt (simple_duration_constraint wth (fn c => [c]))) wth (fn c => getOpt(c, []))
                             || in_paren(pddl_reserved "and" >> repeat1 (in_paren simple_duration_constraint))) ?? "duration constraint"

  val interval = string "all" wth (fn () => Over_All) ?? "interval"

  val timed_GD = ((string "at" >> (time_specifier && pre_GD term)) 
                || (string "over" >> (interval && pre_GD term))) ?? "timed GD"

  val pref_timed_GD = timed_GD ?? "pref timed GD"

  val da_GD = in_paren (opt ((pref_timed_GD wth (fn (tgd) => [tgd])) 
                          || (pddl_reserved "and" >> (repeat (in_paren pref_timed_GD) (* TODO: fix repeat *))))) ?? "da-GD" (* only allowing one level of (and ...)! *)

  val assign_op_t = (pddl_reserved "increase" wth (fn _ => ContinuousIncrease)
                    || pddl_reserved "decrease" wth (fn _ => ContinuousDecrease)) ?? "assign-op-t"

  val f_exp_t = (in_paren(pddl_reserved "*" >> f_exp << pddl_reserved "#t")
                 || in_paren(pddl_reserved "*" >> pddl_reserved "#t" >> f_exp)
                 || (pddl_reserved "#t") wth (fn _ => ConstantExpr (of_int (intToIsaInt 1)))) ?? "f-exp-t"

  (* payload after `at start/end`: a single primitive effect OR an `(and e ...)` conjunction.
     A conjunction yields one SNAP_EFFECT per conjunct, all carrying the same time specifier
     (equivalent to `(and (at start e1) (at start e2) ...)`, which the grammar already allows). *)
  val c_effect_da_list = (c_effect_da wth (fn e => [e])
                          || in_paren(pddl_reserved "and" >> repeat c_effect_da)) ?? "c_effect_da list"

  val timed_effect = ((string "at" >> (time_specifier && c_effect_da_list))
                        wth (fn (t, es) => map (fn e => SNAP_EFFECT (t, e)) es)
                     || (assign_op_t && f_head && f_exp_t)
                        wth (fn (operator, (l, r)) => [CONTINUOUS_EFFECT (ContinuousEffect (operator, (PNE l), r))])) ?? "timed effect"

  (* content of one da-effect paren-group (the enclosing parens already stripped): a single timed
     effect, an `(and ...)` of parenthesised items, or a `(forall (b) <item>)` collecting the
     (list of) sub timed-effects into a FORALL_SNAP. *)
  val da_effect_item = fix (fn item =>
                  timed_effect
                  || (pddl_reserved "and" >> (repeat (in_paren item))) wth List.concat
                  || (pddl_reserved "forall" >> (quant_binder && in_paren item))
                       wth (fn (b, body) => [FORALL_SNAP (b, body)])) ?? "da effect item"

  val da_effect = in_paren (opt da_effect_item) ?? "da effect"

  val durative_action_def_body = ((pddl_reserved ":duration" >> duration_constraint)
                                  && (pddl_reserved ":condition" >> da_GD)
                                  && (pddl_reserved ":effect" >> da_effect))
                                  wth (fn (dur, (pre, eff)) => Durative_Action_Def_Body (dur, pre, eff))  ?? "durative action def body"

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

  (* The 5 optional header sections (requirements/types/constants/predicates/functions) may appear
     in ANY order in real PDDL domains (the BNF fixes an order, but gigante benchmarks vary it, e.g.
     :constants after :functions, or :functions before :predicates).  Parse them order-independently:
     each tagged section returns an update closure over the 5-slot option accumulator, then reduce.
     The assembled result keeps the exact right-nested tuple shape the rest of the parser expects. *)
  val dom_section =
        (require_def    wth (fn v => fn (_, t, c, p, f) => (SOME v, t, c, p, f)))
     || (types_def      wth (fn v => fn (r, _, c, p, f) => (r, SOME v, c, p, f)))
     || (constants_def  wth (fn v => fn (r, t, _, p, f) => (r, t, SOME v, p, f)))
     || (predicates_def wth (fn v => fn (r, t, c, _, f) => (r, t, c, SOME v, f)))
     || (functions_def  wth (fn v => fn (r, t, c, p, _) => (r, t, c, p, SOME v)))
     ?? "domain header section"

  val domain_header = (repeat dom_section)
        wth (fn updates => foldl (fn (u, acc) => u acc) (NONE, NONE, NONE, NONE, NONE) updates)

  val domain = in_paren(pddl_reserved "define" >> in_paren(pddl_reserved "domain" >> pddl_name)
                                                  >> domain_header
                                                  && (repeat structure_def)
                                                  && (repeat invariant_def))
                          wth (fn ((r, t, c, p, f), (structs, invs)) =>
                                 (r, (t, (c, (p, (f, (structs, invs))))))) ?? "domain"

  val object_declar = in_paren(pddl_reserved ":objects" >> (typed_list pddl_obj_cons))

  val basic_fun_term = function_symbol wth (fn (x) => (x,[])) ||
                       in_paren(function_symbol && repeat pddl_obj_cons) ?? "basic function term"

  val init_el = (literal (pddl_obj_cons)
                  || in_paren((pddl_reserved "=") >> basic_fun_term && d_value)
                               wth (fn (t1, t2) => Prop_atom (NumericEqAtm (FunctionExpr (PNE t1), ConstantExpr t2))) 
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
                                                  && (opt (object_declar) wth (fn os => getOpt (os, [])))
                                                  && init
                                                  && goal
                                                  && opt metric_spec) ?? "problem"

  (* t: (a p1 ... pn) [t'] *)
  val lbracket = (char #"[" ) ?? "lbracket"
  val rbracket = (char #"]" ) ?? "rbracket"

  fun in_brackets p = spaces_comm >> lbracket >> spaces_comm >> p << spaces_comm << rbracket << spaces_comm

  val plan_action = in_paren(pddl_name && repeat pddl_obj_cons) && opt (in_brackets dec_num) ?? "plan action"
  val plan = spaces_comm >> repeat (dec_num && ((char #":" ) >> plan_action)) << spaces_comm ?? "plan"

  val classical_plan_action = in_paren(pddl_name && repeat pddl_obj_cons) wth (fn (name, args) => ((name, args), NONE)) ?? "classical plan action"
  val classical_plan = repeat classical_plan_action ?? "classical plan"
  
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

fun pddl_prop_map f prop =
 case prop of Prop_atom atm => Prop_atom (map_atom f atm)
           | Prop_not sub_prop => Prop_not (pddl_prop_map f sub_prop)
           | Prop_and props => Prop_and (map (pddl_prop_map f) props)
           | Prop_or props => Prop_or (map (pddl_prop_map f) props)
           | Prop_imply (a, b) => Prop_imply (pddl_prop_map f a, pddl_prop_map f b)
           | Prop_all (binder, sub) => Prop_all (binder, pddl_prop_map f sub)
           | Prop_ex  (binder, sub) => Prop_ex  (binder, pddl_prop_map f sub)

(* The verified checkers reject any input whose enumerated set of primitive
   numeric expressions is empty ("Can't process plan without any numeric
   fluents.", see valid_plan_from2E in
   Continuous_PDDL_Checker_{Explicit,Numeric}.thy).  The enumeration
   (continuous_plan_enumerate_primitive_numeric_expressions,
   PDDL_Checker_Common.thy) collects PNE *occurrences* from the ground plan,
   (:init) and (:goal) — it never consults the (:functions) declarations, so
   even a domain that declares functions can trip the guard if none occur.
   Until the guard is relaxed on the Isabelle side, we unconditionally
   inject a fresh dummy fluent after parsing: declared in the domain and
   initialised to 0 in (:init), so the enumeration is never empty.  No
   action ever touches it, so plan validity is unaffected.  The name cannot
   clash with anything in the input: pddl_name lowercases every identifier
   it parses, so the uppercase letters in "Dummy-PNE" can never appear in a
   parsed function name (and plans only mention action names and objects,
   never functions).  In particular, an input that references an undeclared
   function spelled "dummy-pne" stays ill-formed instead of being silently
   legitimised by the injected declaration. *)
fun ensureDummyPne (dom, prob) =
  let
    val (reqs, (types_def, (consts_def, (pred_def, (fun_def, structs))))) = dom
    val (preqs, (objs, (init, goal_metric))) = prob
    val dummy = Func "Dummy-PNE"
    val fun_def' = SOME (getOpt (fun_def, []) @ [((dummy, []), ())])
    val dummy_init =
      Prop_atom (NumericEqAtm
        (FunctionExpr (PNE (dummy, [])),
         ConstantExpr (of_int (intToIsaInt 0))))
  in
    ((reqs, (types_def, (consts_def, (pred_def, (fun_def', structs))))),
     (preqs, (objs, (dummy_init :: init, goal_metric))))
  end

(* ============================================================================
   Quantifier elimination by expansion over the domain/problem objects.
   Shared by both strategies; operates on the parsed PDDL AST (term level), so
   `forall`-bound variables that are ALSO schema parameters are left as VAR_TERMs
   for the grounder to substitute later.  `Prop_all` -> `Prop_and` over the
   cartesian product of the bound vars' typed objects (`Prop_ex` -> `Prop_or`);
   the empty conjunction/disjunction is `Prop_and []` / `Prop_or []`, which
   `pddlFormulaToASTPropIsabelle` maps to True / False -- exactly the forall/exists
   semantics over an empty domain.
   ============================================================================ *)

(* type hierarchy (sub,sup) string pairs from (:types) *)
fun typePairsOf (typesDefOPT : PDDL_TYPES_DEF) =
  case typesDefOPT of
     NONE => []
   | SOME tds => List.concat (map (fn (subs, sup) =>
        let val supn = case sup of (h :: _) => pddl_prim_type_name h | [] => "object"
        in map (fn s => (pddl_prim_type_name s, supn)) subs end) tds)

fun supertypesStr pairs t0 =
  let fun step acc [] = acc
        | step acc (x :: xs) =
            let val ups = List.mapPartial
                  (fn (sub, sup) => if sub = x andalso Bool.not (List.exists (fn y => y = sup) acc)
                                    then SOME sup else NONE) pairs
            in step (acc @ ups) (xs @ ups) end
  in step [t0] [t0] end

fun flatObjsTyped (typedList : PDDL_OBJ_CONS PDDL_TYPED_LIST) =
  List.concat (map (fn (obs, tys) =>
       let val tns = map pddl_prim_type_name tys
       in map (fn ob => (ob, tns)) obs end) typedList)

(* objectsOfType: every object whose declared type IS or is a SUBTYPE of the query
   (the root `object` type matches all objects). *)
fun objectsOfType pairs objsTyped queryTy =
  let val qn = pddl_prim_type_name queryTy in
    if qn = "object" then map #1 objsTyped
    else List.mapPartial (fn (ob, tns) =>
           if List.exists (fn tn => List.exists (fn s => s = qn) (supertypesStr pairs tn)) tns
           then SOME ob else NONE) objsTyped
  end

fun objsOfForDomProb parsedDom parsedProb =
  let val (_, (types_def, (consts_def, (_, (_, (_, _)))))) = parsedDom
      val (_, (objs, (_, (_, _)))) = parsedProb
      val pairs = typePairsOf types_def
      val constObjs = case consts_def of SOME cs => flatObjsTyped cs | NONE => []
  in objectsOfType pairs (flatObjsTyped objs @ constObjs) end

(* ---- shadow-aware substitution of quantifier-bound vars -> objects ---- *)
fun removeShadow binder asg =
  List.filter (fn (v, _) => Bool.not (List.exists (fn (bv, _) => bv = v) binder)) asg

fun substTermVars asg (VAR_TERM v) =
      (case List.find (fn (v', _) => v' = v) asg of SOME (_, ob) => OBJ_CONS_TERM ob | NONE => VAR_TERM v)
  | substTermVars _ t = t

fun substPropVars asg prop =
  case prop of
     Prop_atom a          => Prop_atom (map_atom (substTermVars asg) a)
   | Prop_not p           => Prop_not (substPropVars asg p)
   | Prop_and ps          => Prop_and (map (substPropVars asg) ps)
   | Prop_or ps           => Prop_or (map (substPropVars asg) ps)
   | Prop_imply (a, b)    => Prop_imply (substPropVars asg a, substPropVars asg b)
   | Prop_all (b, body)   => Prop_all (b, substPropVars (removeShadow b asg) body)
   | Prop_ex  (b, body)   => Prop_ex  (b, substPropVars (removeShadow b asg) body)

fun substLogNumEff asg e =
  case e of
     LOGIC_EFFECT p         => LOGIC_EFFECT (substPropVars asg p)
   | NUMERIC_EFFECT n       => NUMERIC_EFFECT (map_numeric_effect (substTermVars asg) n)
   | FORALL_EFFECT (b, ss)  => FORALL_EFFECT (b, map (substLogNumEff (removeShadow b asg)) ss)

fun substSnapEff asg e =
  case e of
     SNAP_EFFECT (ta, le)   => SNAP_EFFECT (ta, substLogNumEff asg le)
   | CONTINUOUS_EFFECT c    => CONTINUOUS_EFFECT c
   | FORALL_SNAP (b, ss)    => FORALL_SNAP (b, map (substSnapEff (removeShadow b asg)) ss)

fun cartesianP [] = [[]]
  | cartesianP (xs :: rest) =
      List.concat (map (fn x => map (fn tl => x :: tl) (cartesianP rest)) xs)

fun binderAssignsP objsOf binder =
  cartesianP (map (fn (v, ty) => map (fn ob => (v, ob)) (objsOf ty)) binder)

(* ---- expansion (Strategy B "early": objsOf = ALL problem objects) ---- *)
fun expandProp objsOf prop =
  case prop of
     Prop_all (binder, body) =>
       Prop_and (map (fn asg => expandProp objsOf (substPropVars asg body)) (binderAssignsP objsOf binder))
   | Prop_ex (binder, body) =>
       Prop_or (map (fn asg => expandProp objsOf (substPropVars asg body)) (binderAssignsP objsOf binder))
   | Prop_and ps       => Prop_and (map (expandProp objsOf) ps)
   | Prop_or ps        => Prop_or (map (expandProp objsOf) ps)
   | Prop_imply (a, b) => Prop_imply (expandProp objsOf a, expandProp objsOf b)
   | Prop_not p        => Prop_not (expandProp objsOf p)
   | Prop_atom a       => Prop_atom a

fun expandLogNumEff objsOf e =
  case e of
     FORALL_EFFECT (binder, subs) =>
       List.concat (map (fn asg =>
           List.concat (map (fn s => expandLogNumEff objsOf (substLogNumEff asg s)) subs))
         (binderAssignsP objsOf binder))
   | other => [other]

fun expandSnapEff objsOf e =
  case e of
     FORALL_SNAP (binder, subs) =>
       List.concat (map (fn asg =>
           List.concat (map (fn s => expandSnapEff objsOf (substSnapEff asg s)) subs))
         (binderAssignsP objsOf binder))
   | other => [other]

fun expandDefBody objsOf defBody =
  case defBody of
     Simple_Action_Def_Body (pre, eff) =>
       Simple_Action_Def_Body (
         Option.map (fn (u, p) => (u, Option.map (expandProp objsOf) p)) pre,
         Option.map (fn effs => List.concat (map (expandLogNumEff objsOf) effs)) eff)
   | Durative_Action_Def_Body (durs, cond, eff) =>
       Durative_Action_Def_Body (durs,
         Option.map (map (fn (ta, p) => (ta, expandProp objsOf p))) cond,
         Option.map (fn effs => List.concat (map (expandSnapEff objsOf) effs)) eff)

fun expandDomainQuant objsOf (reqs, (td, (cd, (pd, (fd, (structs, invs)))))) =
  let val structs' = map (fn (n, (args, body)) => (n, (args, expandDefBody objsOf body))) structs
  in (reqs, (td, (cd, (pd, (fd, (structs', invs)))))) end

fun expandProbQuant objsOf (preqs, (objs, (init, (goal, metric)))) =
  (preqs, (objs, (init, (expandProp objsOf goal, metric))))
