  (* This file contains the code for converting the types in the parsed domain to those used
     by the validator exported by Isabelle in the file ../../../isabelle/code/PDDL_STRIPS_Checker_Exported.sml.
     It also calls the function exported by Isabelle to check the validity of a plan.*)
structure PddlParser =
struct
open PDDL

  val IsabelleStringImplode = implode;
  val IsabelleStringExplode = explode;
  val SMLCharImplode = String.implode;
  val SMLCharExplode = String.explode;

  val stringToIsabelle = IsabelleStringExplode
  fun stringListToIsabelle ss = (map stringToIsabelle ss)

  fun pddlVarToIsabelle (v:PDDL_VAR) = Var (IsabelleStringExplode (pddl_var_name v))

  fun intToIsaNat x = nat_of_integer (IntInf.fromInt x)

  fun intToIsaInt x = int_of_integer (IntInf.fromInt x)

  (* TODO: find nicer way to handle floats with a lot of ending 0's. *)
  (*fun trimEndingZeros (cs, zs) = 
    case cs of
      [] => []
    | (c::cs') => 
      if c = #"0" then trimEndingZeros (cs',#"0"::zs)
      else zs@[c]@(trimEndingZeros (cs',[]))*)

  (* decimal number parsed => String pair = s1 ^ '.' ^ s2 => RAT *)
  (* fun stringPairToIsaRat (s1,s2) =
    case s2 of
      SOME s2' => TEMPORAL_PDDL_Checker_Exported.fract (intToIsaInt (valOf (Int.fromString (s1 ^ s2')))) (int_of_integer (IntInf.pow (10, (size s2'))))
    | NONE => TEMPORAL_PDDL_Checker_Exported.of_int (intToIsaInt (valOf (Int.fromString s1))) *)

  (* decimal number parsed => String pair = s1 ^ '.' ^ s2 => RAT *)
  (*fun stringPairToIsaRat (s1,s2) =
    case s2 of
      SOME s2' => 
        let val s2't = String.implode(trimEndingZeros (String.explode s2',[])) in
          TEMPORAL_PDDL_Checker_Exported.fract (intToIsaInt (valOf (Int.fromString (s1 ^ s2't)))) (int_of_integer (IntInf.pow (10, (size s2't))))
        end
    | NONE => TEMPORAL_PDDL_Checker_Exported.of_int (intToIsaInt (valOf (Int.fromString s1)))*)

  fun charToNat c = intToIsaNat (valOf (Int.fromString (str c)))

  fun stringPairToIsaRat (s1,s2) =
    case s2 of
      SOME s2' => TEMPORAL_PDDL_Checker_Exported.rat_of_digits_pair (map charToNat (String.explode s1), map charToNat (String.explode s2'))
    | NONE => TEMPORAL_PDDL_Checker_Exported.of_int (intToIsaInt (valOf (Int.fromString s1)))

  (*fun ratToIsabelleRat r = case r of 
    (n, d) => TEMPORAL_PDDL_Checker_Exported.fract n d*)

  fun pddlObjConsToIsabelle (oc:PDDL_OBJ_CONS) = 
    case oc of
    PDDL_OBJ_CONS n => Obj (stringToIsabelle n)
  | Rat_Ent r => TimeEnt (stringPairToIsaRat r)
  | Func_Ent (f, args) => FuncEnt (Func (stringToIsabelle f), map pddlObjConsToIsabelle args)

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

  fun pddlFunToIsabelle ((func, args),()) = FuncDecl (Func (stringToIsabelle func), List.concat (pddlTypedListTypesToIsabelle args))

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
                 | _ => Bot (*Fluents shall invalidate the problem*)

  fun pddlFormulaToASTPropIsabelleTerm phi = pddlFormulaToASTPropIsabelle pddlTermToIsabelle phi

  fun pddlFormulaToASTPropIsabelleObj phi = pddlFormulaToASTPropIsabelle pddlObjConsTermToIsabelle phi

  fun pddlPreGDToIsabelle PreGD =
      case PreGD of SOME (prop: PDDL_TERM PDDL_PROP) => pddlFormulaToASTPropIsabelleTerm prop
                 | _ => Not Bot (*If we have no precondition, then it is a tautology*)

  fun isProp_atom fmla = case fmla of Prop_atom(atom) => true | _ => false

  fun isNegProp_atom fmla = case fmla of Prop_not(Prop_atom(atom)) => true | _ => false

  fun strToVarAtom atom = map_atom (fn x => pddlTermToIsabelle x) atom

  fun strToObjAtom atom = map_atom (fn x => pddlObjConsTermToIsabelle x) atom

  fun pddlPropLiteralToIsabelleAtom lit = 
      case lit of Prop_atom atom => Atom (strToVarAtom atom)
               | Prop_not(Prop_atom atom) => Atom (strToVarAtom atom)
               | _ => exit_fail "Literal expected"

  fun pddlPropToASTEffIsabelle (Prop: PDDL_TERM PDDL_PROP) =
      case Prop of Prop_atom atom => ([Atom (strToVarAtom atom)],[])
                 | Prop_not (Prop_atom atom) => ([],[Atom (strToVarAtom atom)])
                 | Prop_and propList
                     => (let val adds = (List.filter isProp_atom propList);
                             val dels = (List.filter isNegProp_atom propList);
                         in (map pddlPropLiteralToIsabelleAtom adds, map pddlPropLiteralToIsabelleAtom dels)
                         end)
                 | _ => ([], [])

  fun pddlCEffectToIsabelle CEff =
      case CEff of SOME (prop: PDDL_TERM PDDL_PROP) => Effect (pddlPropToASTEffIsabelle prop)
                 | _ => Effect ([],[])

  fun actDefBodyPreToIsabelle pre = case pre of SOME (u, pre: PDDL_PRE_GD) => pddlPreGDToIsabelle pre
                                            | _ => Not Bot
  fun actDefBodyEffToIsabelle eff = case eff of SOME (u, eff: C_EFFECT) => pddlCEffectToIsabelle eff
                                            | _ => Effect ([],[])
  (* fun pddlActDefBodyToIsabelle (pre, eff) = ((actDefBodyPreToIsabelle pre), (actDefBodyEffToIsabelle eff)) *)

  fun pddlIsabelleActName actName = SMLCharImplode (map (fn c => if c = #"-" then #"_" else c) (SMLCharExplode actName))

  (* extension for durative actions *)

  fun pddlTimeSpecToIsabelle timeSpec = 
    case timeSpec of 
      at_start => At_Start
    | at_end => At_End
    | over_all => Over_All

  fun pddlDurConstraintToIsabelle (durConst: PDDL_DURATION_CONSTRAINT) = 
    case durConst of 
      No_Const_Def _ => No_Const
    | Time_Const_Def (timeSpec_obt, (d_op, d)) => 
      (case d_op of
        d_op_leq => Time_Const (LEQ, stringPairToIsaRat d) (* (pddlTimeSpecToIsabelle timeSpec, d) *)
      | d_op_eq => Time_Const (EQ, stringPairToIsaRat d) (* (pddlTimeSpecToIsabelle timeSpec, d) *)
      | d_op_geq => Time_Const (GEQ, stringPairToIsaRat d)) (* (pddlTimeSpecToIsabelle timeSpec, d) *)
    | Func_Const_Def (timeSpec_obt, (d_op, (f, args))) => 
      (case d_op of
        d_op_leq => Func_Const (LEQ, Func (stringToIsabelle f), map pddlTermToIsabelle args) (* (pddlTimeSpecToIsabelle timeSpec, d) *)
      | d_op_eq => Func_Const (EQ, Func (stringToIsabelle f), map pddlTermToIsabelle args) (* (pddlTimeSpecToIsabelle timeSpec, d) *)
      | d_op_geq => Func_Const (GEQ, Func (stringToIsabelle f), map pddlTermToIsabelle args)) (* (pddlTimeSpecToIsabelle timeSpec, d) *)
        
  fun pddlTimedCondToIsabelle ((timeSpec, cond): PDDL_TIME_SPECIFIER * (PDDL_TERM PDDL_PROP)) = 
      (pddlTimeSpecToIsabelle timeSpec, pddlFormulaToASTPropIsabelleTerm cond)

  fun pddlTimedListCondToIsabelle (cond_opt: (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option) = 
      case cond_opt of
        SOME cond => (map pddlTimedCondToIsabelle cond)
      | NONE => []

  (* fun pddlDurActDefBodyCondToIsabelle (durConst, cond, eff) = (pddlTimedListCondToIsabelle cond) *)

  fun pddlTimedEffToIsabelle ((timeSpec, eff): PDDL_TIME_SPECIFIER * (PDDL_TERM PDDL_PROP)) = 
      (pddlTimeSpecToIsabelle timeSpec, Effect (pddlPropToASTEffIsabelle eff))

  fun pddlTimedListEffToIsabelle (eff_opt: (PDDL_TERM PDDL_PROP) PDDL_TIMED_LIST option) = 
      case eff_opt of
        SOME eff => (map pddlTimedEffToIsabelle eff)
      | NONE => []

  (* fun pddlDurActDefBodyEffToIsabelle (durConst, cond, eff) = (pddlTimedListEffToIsabelle eff) *)

  (* *)

  fun pddlActToIsabelle (actName, (args, defBody: PDDL_ACTION_DEF_BODY)) =
    case defBody of
      Simple_Action_Def_Body (pre, eff) => 
        Simple_Action_Schema(IsabelleStringExplode actName,
          pddlTypedListVarsTypesToIsabelle args,
          actDefBodyPreToIsabelle pre,
          actDefBodyEffToIsabelle eff)
    | Durative_Action_Def_Body (durConst, (cond, eff)) => 
        Durative_Action_Schema(IsabelleStringExplode actName,
          pddlTypedListVarsTypesToIsabelle args,
          map pddlDurConstraintToIsabelle durConst,
          pddlTimedListCondToIsabelle cond,
          pddlTimedListEffToIsabelle eff)


  fun pddlActionsDefToIsabelle (actsDef : PDDL_ACTION list) = (map pddlActToIsabelle actsDef)

  fun pddlDomToIsabelle (reqs:PDDL_REQUIRE_DEF,
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
                         (pddlActionsDefToIsabelle actions_def))


  fun objDefToIsabelle (objs:PDDL_OBJ_DEF) = pddlTypedListObjsConsTypesToIsabelle objs

  fun isntFluent x = (case x of Fluent => false | _ => true)

  fun isntTautology x = (case x of Not Bot => false | _ => true)

  fun initElToIsabelle (init_el:PDDL_INIT_EL) = pddlFormulaToASTPropIsabelleObj (pddl_prop_map OBJ_CONS_TERM init_el)


  fun pddlInitToIsabelleWithObjEqs (init:PDDL_INIT) objs = (map initElToIsabelle (List.filter isntFluent init)) (*I don't want fluents in the init state. This is usually an init value for the plan-cost.*)
                                                           @ (map (fn obj => Atom (pddlEqToIsabelleObj (obj, obj))) objs)

  fun pddlInitToIsabelle (init:PDDL_INIT) objs = (map initElToIsabelle (List.filter isntFluent init)) (*I don't want fluents in the init state. This is usually an init value for the plan-cost.*)


  fun pddlGoalToIsabelle (goal:PDDL_GOAL) = pddlFormulaToASTPropIsabelleObj goal

  fun pddlProbToIsabelle (reqs:PDDL_REQUIRE_DEF,
                          (objs:PDDL_OBJ_DEF,
                              (init:PDDL_INIT,
                                (goal_form:PDDL_GOAL,
                                   metric)))) =
                                   (objDefToIsabelle objs,
                                    (pddlInitToIsabelle init (List.concat (map #1 objs))),
                                    pddlGoalToIsabelle goal_form)



  fun planActionToIsabelle (tstart, ((act_name, args), tdur_opt): PDDL_PLAN_ACTION) = 
      case tdur_opt of 
        SOME tdur => (stringPairToIsaRat tstart, Durative_Plan_Action(stringToIsabelle act_name, map pddlObjConsToIsabelle args, stringPairToIsaRat tdur))
      | NONE => (stringPairToIsaRat tstart, Simple_Plan_Action(stringToIsabelle act_name, map pddlObjConsToIsabelle args))

  fun planToIsabelle plan = map planActionToIsabelle plan

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
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
val parse_pddl_plan = parse_wrapper (PDDL.end_of_file PDDL.plan)

fun get_prob dom_file prob_file = let
  val parsedDom = parse_pddl_dom dom_file
  val parsedProb = parse_pddl_prob prob_file

  val isaProb = (TEMPORAL_PDDL_Checker_Exported.Problem
                  (let val (p1,p2,p3) = pddlProbToIsabelle parsedProb in
                     (pddlDomToIsabelle parsedDom, p1,p2,p3) end))
in isaProb
end
end