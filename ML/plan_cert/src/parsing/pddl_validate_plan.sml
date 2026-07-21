  (* Parsed-PDDL -> exported-Isabelle (Converter) conversion for the unsolvability certifier.

     Vendored/adapted from Formal-PDDL-Semantics codeBase/planning/pddlParser/
     pddl_validate_plan_temporal.sml (the newer, temporal-numeric-capable validator that
     matches the newer pddl_refactor.sml grammar).  It builds a `Converter.Problem`
     (Domain types preds funcs consts actions, objs, init, goal) with temporal action schemas
     (SimpleActionSchemaa / DurativeActionSchema) for consumption by check_and_make_network_opt.

     Deltas from the FPS source:
       - variable ctor `Var` -> `Vara` (our export mangles it; AFP Datalog `Var` claims the
         unsuffixed name);
       - `structure PddlParser` wrapper exposing `get_prob dom_file prob_file`;
       - plan parsing stubbed out (the certifier consumes domain+problem only; the temporal
         plan-action ctors are not part of the Converter export). *)
structure PddlParser =
struct
open PDDL

  val IsabelleStringImplode = fn s => s;
  val IsabelleStringExplode = fn s => s;
  val SMLCharImplode = String.implode;
  val SMLCharExplode = String.explode;

  val stringToIsabelle = fn s => s
  fun stringListToIsabelle ss = ss

  (* our export names the FPS variable ctor `Vara` (AFP Datalog `Var` claims the plain name) *)
  fun pddlVarToIsabelle (v:PDDL_VAR) = Vara (IsabelleStringExplode (pddl_var_name v))

  fun pddlObjConsToIsabelle (oc:PDDL_OBJ_CONS) =
    case oc of
    PDDL_OBJ_CONS n => Obj (stringToIsabelle n)

  fun pddlTermToIsabelle term =
    case term of VAR_TERM v => VAR (pddlVarToIsabelle v)
             | OBJ_CONS_TERM oc => CONST (pddlObjConsToIsabelle oc)

  fun pddlVarTermToIsabelle term =
    case term of VAR_TERM v => pddlVarToIsabelle v
             | _ => exit_fail ("Var expected, but object found: pddlVarTermToIsabelle " ^ (pddlObjConsTermToString term))

  fun pddlObjConsTermToIsabelle term =
    case term of OBJ_CONS_TERM v => pddlObjConsToIsabelle v
             | _ => exit_fail ("Object expected, but variable found: pddlObjConsTermToIsabelle " ^ (pddlVarTermToString term))

  fun pddlTypeToIsabelle (type_ :PDDL_TYPE) = Either (stringListToIsabelle (map pddl_prim_type_name type_))

  fun mk_pair x y = (x,y)

  fun type_str_cat_fun (l:string list list) = (String.concatWith ", ") (map (String.concatWith ", ") l)

  fun pddlTypedListVarsTypesToIsabelle (typedList :PDDL_VAR PDDL_TYPED_LIST) =
     (pddlTypedListXTypesConv typedList List.concat mk_pair pddlVarToIsabelle pddlTypeToIsabelle)

  fun pddlTypedListObjsConsTypesToIsabelle (typedList :PDDL_OBJ_CONS PDDL_TYPED_LIST) =
     (pddlTypedListXTypesConv typedList List.concat mk_pair pddlObjConsToIsabelle pddlTypeToIsabelle)

  fun pddlTypedListTypesToIsabelle (typedList :'a PDDL_TYPED_LIST) =
                            map (fn (vars, type_) =>
                                     (map (fn _ => (pddlTypeToIsabelle type_)) vars))
                                 typedList;

  fun extractFlatTypedListIsabelle typedList =
                 extractFlatTypedList List.concat stringToIsabelle mk_pair typedList

  fun pddlTypesDefToIsabelle (typesDefOPT :PDDL_TYPES_DEF) =
                   case typesDefOPT of
                        SOME typesDef =>
                             (extractFlatTypedListIsabelle typesDef)
                      | _ => []


  fun pddlConstsDefToIsabelle (constsDefOPT :PDDL_CONSTS_DEF) =
                   case constsDefOPT of
                        SOME constsDef =>
                             pddlTypedListObjsConsTypesToIsabelle constsDef
                      | _ => []

  fun pddlPredToIsabelle (pred, args) = PredDecl (Pred (stringToIsabelle (pddl_pred_name pred)), List.concat (pddlTypedListTypesToIsabelle args))

  fun pddlFunToIsabelle ((func, args),()) = FuncDecl (func, List.concat (pddlTypedListTypesToIsabelle args))

  fun pddlPredDefToIsabelle pred_defOPT =
                   case pred_defOPT of
                        SOME pred_def => (map pddlPredToIsabelle pred_def)
                        | _ => []

  fun pddlFunDefToIsabelle fun_defOPT =
                   case fun_defOPT of
                        SOME fun_def => (map pddlFunToIsabelle fun_def)
                        | _ => []

  fun pddlEqToIsabelleTerm (term1, term2) = EqAtm (pddlVarTermToIsabelle term1, pddlVarTermToIsabelle term2 )

  fun pddlEqToIsabelleObj (term1, term2) = EqAtm (pddlObjConsToIsabelle term1, pddlObjConsToIsabelle term2)

  fun pddlFormulaToASTPropIsabelle atom_fn phi =
      case phi of Prop_atom(atom : PDDL_TERM PDDL_ATOM) =>  Atom (map_atom atom_fn atom)
                 | Prop_not(prop: PDDL_TERM PDDL_PROP) =>  Not (pddlFormulaToASTPropIsabelle atom_fn prop)
                 | Prop_and(propList: PDDL_TERM PDDL_PROP list) => bigAnd (map (pddlFormulaToASTPropIsabelle atom_fn) propList)
                 | Prop_or(propList: PDDL_TERM PDDL_PROP list) => bigOr (map (pddlFormulaToASTPropIsabelle atom_fn) propList)
                 | Prop_imply(a, b) => Imp (pddlFormulaToASTPropIsabelle atom_fn a, pddlFormulaToASTPropIsabelle atom_fn b)
                 | _ => Bot

  fun pddlFormulaToASTPropIsabelleTerm phi = pddlFormulaToASTPropIsabelle pddlTermToIsabelle phi

  fun pddlFormulaToASTPropIsabelleObj phi = pddlFormulaToASTPropIsabelle pddlObjConsTermToIsabelle phi

  fun pddlPreGDToIsabelle PreGD =
      case PreGD of SOME (prop: PDDL_TERM PDDL_PROP) => pddlFormulaToASTPropIsabelleTerm prop
                 | _ => Not Bot

  fun strToVarAtom atom = map_atom (fn x => pddlTermToIsabelle x) atom

  fun strToObjAtom atom = map_atom (fn x => pddlObjConsTermToIsabelle x) atom

  fun pddlPropLiteralToIsabelleAtom lit =
      case lit of Prop_atom atom => Atom (strToVarAtom atom)
               | Prop_not(Prop_atom atom) => Atom (strToVarAtom atom)
               | _ => exit_fail "Literal expected"

  fun logicOrNumericEffectToASTEffIsabelle eff =
      case eff of LOGIC_EFFECT (Prop_atom atom) => ([Atom (strToVarAtom atom)], [], [])
                 | LOGIC_EFFECT (Prop_not (Prop_atom atom)) => ([], [Atom (strToVarAtom atom)], [])
                 | NUMERIC_EFFECT e => ([], [], [map_numeric_effect pddlTermToIsabelle e])
                 | _ => ([], [], [])

  fun flatten_effects nil = Effect ([], [], [])
  |   flatten_effects (Effect (adds, dels, numerics) :: effs) =
    (let val (Effect (adds', dels', numerics')) = flatten_effects effs
     in Effect (adds @ adds', dels @ dels', numerics @ numerics')
     end)

  fun actDefBodyPreToIsabelle pre = case pre of SOME (u, pre: PDDL_PRE_GD) => pddlPreGDToIsabelle pre
                                            | _ => Not Bot
  fun actDefBodyEffToIsabelle effs = case effs of SOME (the_effs) => flatten_effects (map (Effect o logicOrNumericEffectToASTEffIsabelle) the_effs)
                                                  | _ => Effect ([], [], [])

  fun pddlIsabelleActName actName = SMLCharImplode (map (fn c => if c = #"-" then #"_" else c) (SMLCharExplode actName))

  fun pddlDurConstraintToIsabelle (t, DurationConstraint (d_op, r)) = (t, DurationConstraint (d_op, map_numeric_expression pddlTermToIsabelle r))

  fun pddlTimedCondToIsabelle ((timeSpec, cond): PDDL_TIME_SPECIFIER * (PDDL_TERM PDDL_PROP)) =
      (timeSpec, pddlFormulaToASTPropIsabelleTerm cond)

  fun pddlTimedListCondToIsabelle (cond_opt: (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option) =
      case cond_opt of
        SOME cond => (map pddlTimedCondToIsabelle cond)
      | NONE => []

  fun pddlTimedEffToIsabelle (timeSpec, eff) =
      (timeSpec, Effect (logicOrNumericEffectToASTEffIsabelle eff))

  fun snap_effects nil = nil
  |   snap_effects ((SNAP_EFFECT se) :: effs) = se :: (snap_effects effs)
  |   snap_effects ((CONTINUOUS_EFFECT _) :: effs) = snap_effects effs

    fun continuous_effects nil = nil
  |   continuous_effects ((SNAP_EFFECT _) :: effs) = continuous_effects effs
  |   continuous_effects ((CONTINUOUS_EFFECT ce) :: effs) = ce :: continuous_effects effs

  fun pddlTimedListEffToIsabelle (eff_opt) =
      case eff_opt of
        SOME eff => (map pddlTimedEffToIsabelle (snap_effects eff))
      | NONE => []

  fun has_cont_change (eff_opt) =
      case eff_opt of
        SOME eff => Bool.not (null (continuous_effects eff))
      | NONE => false

  (* Build temporal action schemas from the parsed PDDL. *)
  fun pddlActToTemporalIsabelle (actName, (args, defBody: PDDL_ACTION_DEF_BODY)) =
    case defBody of
      Simple_Action_Def_Body (pre, eff) =>
        SimpleActionSchemaa(ActionHead(IsabelleStringExplode actName,
          pddlTypedListVarsTypesToIsabelle args),
          SimpleActionBody(actDefBodyPreToIsabelle pre,
          actDefBodyEffToIsabelle eff))
    | Durative_Action_Def_Body (durConst, cond, eff) =>
        if (Bool.not (has_cont_change eff))
        then DurativeActionSchema(ActionHead(IsabelleStringExplode actName,
          pddlTypedListVarsTypesToIsabelle args),
          DurativeActionBody(map pddlDurConstraintToIsabelle durConst,
          pddlTimedListCondToIsabelle cond,
          pddlTimedListEffToIsabelle eff))
        else raise Fail "Continuous effects not supported."


  fun pddlTemporalActionsDefToIsabelle (actsDef : PDDL_ACTION list) = (map pddlActToTemporalIsabelle actsDef)

  fun pddlTemporalDomToIsabelle (reqs:PDDL_REQUIRE_DEF,
                         (types_def,
                            (consts_def,
                               (pred_def,
                                   (fun_def,
                                       (actions_def,
                                          constraints_def))))))
                      = Domain
                        ((pddlTypesDefToIsabelle types_def),
                         (pddlPredDefToIsabelle pred_def),
                         (pddlFunDefToIsabelle fun_def),
                         (pddlConstsDefToIsabelle consts_def),
                         (pddlTemporalActionsDefToIsabelle actions_def))


  fun objDefToIsabelle (objs:PDDL_OBJ_DEF) = pddlTypedListObjsConsTypesToIsabelle objs


  fun initElToIsabelle (init_el:PDDL_INIT_EL) = pddlFormulaToASTPropIsabelleObj (pddl_prop_map OBJ_CONS_TERM init_el)

  fun pddlInitToIsabelle (init:PDDL_INIT) objs = (map initElToIsabelle init)


  fun pddlGoalToIsabelle (goal:PDDL_GOAL) = pddlFormulaToASTPropIsabelleObj goal

  fun pddlProbToIsabelle (reqs:PDDL_REQUIRE_DEF,
                          (objs:PDDL_OBJ_DEF,
                              (init:PDDL_INIT,
                                (goal_form:PDDL_GOAL,
                                   metric)))) =
                                   (objDefToIsabelle objs,
                                    (pddlInitToIsabelle init (List.concat (map #1 objs))),
                                    pddlGoalToIsabelle goal_form)

  (* Plan parsing is not used by the unsolvability certifier (it consumes domain+problem only);
     the temporal plan-action ctors are not part of the Converter export. *)
  fun planActionToIsabelle (_: PDDL_PLAN_ACTION) =
      exit_fail "plan parsing not supported by the unsolvability certifier"

  fun planToIsabelle plan = map planActionToIsabelle plan

(* strip a leading UTF-8 byte-order mark (EF BB BF) if present -- several gigante
   domain/problem files begin with one, which is not valid PDDL content. *)
fun stripBOM s =
  if String.size s >= 3 andalso String.substring (s, 0, 3) = "\239\187\191"
  then String.extract (s, 3, NONE) else s

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    stripBOM (next_String stream)
end

fun writeFile file content =
    let val fd = TextIO.openOut file
        val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
        val _ = TextIO.closeOut fd
    in () end

fun parse_wrapper parser file =
  case (CharParser.parseString parser (readFile file ^ "#eof#")) of
    Sum.INR x => x
  | Sum.INL err => exit_fail err

val parse_pddl_dom = parse_wrapper (PDDL.end_of_file PDDL.domain)
val parse_pddl_prob = parse_wrapper (PDDL.end_of_file PDDL.problem)

fun get_prob dom_file prob_file =
  let val parsedDom = parse_pddl_dom dom_file
      val parsedProb = parse_pddl_prob prob_file
      val (objs, init, goal) = pddlProbToIsabelle parsedProb
  in Converter.Problem (pddlTemporalDomToIsabelle parsedDom, objs, init, goal) end
end
