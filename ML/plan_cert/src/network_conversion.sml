(* To do: 
    - Use Error Monad like in mlunta/product_construction/rewrite_bexps.sml 
    - Organise code and type declarations 

To do(?): 
    - Preprocess boolean expressions/constraints into (x [- y] {<,<=,=,>,>=} c) form when possible*)

signature NETWORK_CONVERSION = sig
    
(*  (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, L0, s0) 
    The pure un-renamed network *)

(* The actual exported types are at the bottom of the util/Syntax.sml file:

type var = {name : string, upper : int, lower : int}
type ('a, 'b) invariant =
     ('a, 'b) Invariant.conjunction
type ('a, 'b) guard =
     ('a Difference.clock_pair, 'b) Constraint.constraint Guard.guard
type ('a, 'b) diff_constraint =
     ('a Difference.clock_pair, 'b) Constraint.constraint
type ('a, 'b) constraint = ('a, 'b) Constraint.constraint

*)
    val convert_network: NetworkConversionTypes.isa_network -> ParseBexpTypes.network
end

structure NetworkConversion : NETWORK_CONVERSION =
struct
    fun invert_constraint (constr: (string, int) Syntax.constraint) : (string, int) Syntax.guard =
        (case constr of
            Constr.Eq (a, b) => Guard.Or (Guard.Constr (Constr.Lt (a, b)), Guard.Constr (Constr.Gt (a, b))) |
            Constr.Le (a, b) => Guard.Constr (Constr.Gt (a, b)) |
            Constr.Lt (a, b) => Guard.Constr (Constr.Ge (a, b)) |
            Constr.Ge (a, b) => Guard.Constr (Constr.Lt (a, b)) |
            Constr.Gt (a, b) => Guard.Constr (Constr.Ge (a, b))
        )


    (* vc is an arbitrary clock or variable.
        Adding some arbitrary clock might affect the renaming. Does MLunta use an urgent clock.
        This function is used for guards and not constraints. There is *)
    fun invert_guard (vc: string) (guard: (string, int) Syntax.guard) : (string, int) Syntax.guard =
        let
            val false_constr = Constraint.Gt (Difference.Diff vc vc) 0;
            val always_false = Guard.Constr false_constr
        in (case guard of 
            Guard.True => always_false |
            Guard.Constr x => (
                if (Guard.Constr x = always_false) 
                then Guard.True 
                else invert_constraint x) |
            Guard.And (x, y) => Guard.Or (invert_guard x, invert_guard y) |
            Guard.Or (x, y) => Guard.And (invert_guard x, invert_guard y)
        )
        end

    (* This does not fully implement features supported by Munta.
    - Arbitrary operators: Unop f x, Binop f x y
    - If then else: If_then_else b x y 

    *)

    (* unsafe *)
    fun is_plus f = (f 2 5 = 7)
    fun is_minus f = (f 1 2 = -1)

    (* These are not clocks. These are variables *)
    fun convert_exp_left (guard_exp: (string, inta) Model_Checker.exp): string Difference.clock_pair =
        (case guard_exp of
            Model_Checker.Var x => Difference.Single x |
            Model_Checker.Binop (f, Model_Checker.Var x, Model_Checker.Var y) => (case is_minus f of 
                (true) => Difference.Diff (x, y) |
                _ => Exn.error "Not a valid variable (difference) constraint. Ill-defined LHS. Should be minus."
            ) |
            _ => Exn.error ""
        ) (* The datatypes that are parsed by MLunta do not explicitly mark variables as different to clocks.*)

    fun convert_exp_right (guard_exp: (string, inta) Model_Checker.exp): int =
        (case guard_exp of
            Model_Checker.Const x => integer_of_int x |
            _ => Exn.error "RHS of comparison must be constant."
        )

    fun convert_comparison (comp: (string, inta) Model_Checker.bexp): (string, int) Syntax.guard =
        Guard.Constr ((case comp of
            Model_Checker.Eq  x => (Constraint.Eq, integer_of_int x) |
            Model_Checker.Lea x => (Constraint.Le, integer_of_int x) |
            Model_Checker.Lta x => (Constraint.Lt, integer_of_int x) |
            Model_Checker.Gea x => (Constraint.Ge, integer_of_int x) |
            Model_Checker.Gta x => (Constraint.Gt, integer_of_int x) |
            _ => Exn.error "Invalid expression in guard or constraint of edge. Not a comparison."
        ) |> (fn (f, (l, r)) => f (convert_exp_left l, convert_exp_right r)))

    fun convert_guard (vc: string) guard = 
    let 
        val invert_guard = invert_guard vc;
        fun convert_guard' (guard: (string, inta) Model_Checker.bexp): (string, int) Syntax.guard =
            (case guard of 
                Model_Checker.True => Guard.True |
                Model_Checker.Not x => invert_guard (convert_guard' x) |
                Model_Checker.And (x, y) => Guard.And (convert_guard' x, convert_guard' y) |
                Model_Checker.Or (x, y) => Guard.Or (convert_guard' x, convert_guard' y) |
                Model_Checker.Imply (x, y) => 
                    let val x' = convert_guard' x;
                        val y' = convert_guard' y'
                    in Guard.Or (invert_guard x', Guard.And (x', y'))
                    end |
                Model_Checker.Eq x  => convert_comparison (Model_Checker.Eq x) |
                Model_Checker.Lea x => convert_comparison (Model_Checker.Lea x) |
                Model_Checker.Lta x => convert_comparison (Model_Checker.Lta x) |
                Model_Checker.Gea x => convert_comparison (Model_Checker.Gea x) |
                Model_Checker.Gta x => convert_comparison (Model_Checker.Gta x)
            )
    in convert_guard' guard

    fun convert_constraint (constr: (string, int) Model_Checker.acconstraint): (string, int) Syntax.guard =
        (case constr of 
            Model_Checker.LT x => (Constraint.Lt x) |
            Model_Checker.LE x => (Constraint.Le x) |
            Model_Checker.EQ x => (Constraint.Eq x) |
            Model_Checker.GE x => (Constraint.Ge x) |
            Model_Checker.GT x => (Constraint.Gt x) |
        ) |> Guard.Constr

    fun convert_constraints (cs: (string, inta) Model_Checker.acconstraint list): (string, int) Syntax.guard =
        fold Guard.And (map convert_constraint cs) Guard.True

    fun convert_action (act: string Model_Checker.act): string Syntax.action =
        (case act of
            Model_Checker.In x  => Syntax.In x |
            Model_Checker.Out x => Syntax.Out x |
            Model_Checker.Sil x => Syntax.Internal x
        )

    fun convert_update (upd: string * (string, inta) Model_Checker.exp): string Syntax.update =
        (case upd of
            (x, Model_Checker.Const c) => Syntax.Reset (x, integer_of_int c) |
            (x, Model_Checker.Binop (f, Model_Checker.Var v, Model_Checker.Const c)) =>
                let 
                    val c = integer_of_int c;
                    val offset = (case (is_minus f, is_plus f) of
                            (true, false) => -c |
                            (false, true) => c |
                            _ => Exn.error "Invalid update. Unknown operator on RHS")
                in (if x = v then Syntax.Shift (x, offset) else (Syntax.Update (x, v, offset)))
                    (* (case (x = v, offset = 0) of 
                        (false, false) => Update (x, v, offset) |
                        (_, true) => Copy (x, v) |
                        (true, false) => Shift (x, offset) |
                    ) *)
                end
            |
            _ => Exn.error "Invalid update. RHS not neither constant nor relative (v op c)."
        )

    fun convert_updates (upds: (string * (string, inta) Model_Checker.exp) list): (string Syntax.update list) =
        map convert_update upds

    fun convert_resets = 
        map (fn x => Syntax.Reset (x, 0))

    (* Note; naming collisions are handled by MLunta *)
    fun convert_edge (vc: string) (edge: NetworkConversionTypes.isa_edge): ParseBexpTypes.edge =
        let 
            val (out_loc, guard, constr, action, updates, resets, in_loc) = edge;
            val guard = convert_guard vc guard;
            val constr = convert_constraints constr;
            val guard = Model_Checker.And guard constr;
            val act = convert_action action;
            val upds = convert_updates updates;
            val resets = convert_resets resets;
            val upds = upds @ resets
        in {
            integer_of_nat out_loc,
            guard,
            act,
            upds,
            integer_of_nat in_loc
        }
        end

    fun convert_node 
        (name_asmt: nat -> string)
        (inv_asmt: nat -> (string, inta) Model_Checker.acconstraint list) 
        (node_id: nat) 
        =
        let
            val name = name_asmt node_id 
        in {
            id = integer_of_nat node_id,
            name = name,
            invariant = convert_acconstraint_list (inv_asmt node_id)
        }
        end

    fun pair_list_to_fun xs default = (fn x =>
        (List.find (fn (a, b) => a = x) xs)
        |> (the_default default)
    )

    fun convert_automaton 
        (vc: string) (name_asmt: nat -> string) (initial: nat)
        (auto: NetworkConversionTypes.isa_automaton): ParseBexpTypes.automaton =
        let
            val (committed, urgent, edges, invs) = auto;
            val inv_asmt = pair_list_to_fun invs [];
            val edges = map (convert_edge vc) edges;
            val nodes = map (convert_node name_asmt inv_asmt) nodes
        in {
            committed = map integer_of_nat committed,
            urgent = map integer_of_nat urgent,
            initial = integer_of_nat initial,
            edges = edges,
            nodes = nodes
        }
        end

    (* Arbitrary variable to ensure it is always possible to create an unsatisfiable guard. *)
    val arbitrary_var = ("var12345", 0, 0)

    fun add_arbitrary_var xs = arbitrary_var::xs

    fun get_arbitrary_var xs = 
        case (if (length xs) = 0 then add_arbitrary_var xs else xs)
        |> (fn xs => (hd xs, xs))


    fun make_var (v, l, u) =
        {
            name = v,
            lower = l,
            upper = u
        }

    fun convert_sexp 
            (auto_num_to_name: nat -> string) 
            (auto_and_loc_nums_to_name: nat -> nat -> string)
            (exp: isa_state_exp): (string, inta) Syntax.Formula.bexp =
        (case exp of
            Model_Checker.Truea => Syntax.Formula.True |
            Model_Checker.Nota x => Syntax.Formula.Not (convert_sexp x) |
            Model_Checker.Anda (x, y) => Syntax.Formula.And (convert_sexp x, convert_sexp y) |
            Model_Checker.Ora (x, y) => Syntax.Formula.Or (convert_sexp x, convert_sexp y) |
            Model_Checker.Implya (x, y) => Syntax.Formula.Impl (convert_sexp x, convert_sexp y) |
            Model_Checker.Eqa (x, y) => Syntax.Formula.Pred (Syntax.Constraint.Eq (Syntax.Difference.single x, integer_of_int y)) |
            Model_Checker.Leb (x, y) => Syntax.Formula.Pred (Syntax.Constraint.Le (Syntax.Difference.single x, integer_of_int y)) |
            Model_Checker.Ltb (x, y) => Syntax.Formula.Pred (Syntax.Constraint.Lt (Syntax.Difference.single x, integer_of_int y)) |
            Model_Checker.Gea (x, y) => Syntax.Formula.Pred (Syntax.Constraint.Ge (Syntax.Difference.single x, integer_of_int y)) |
            Model_Checker.Gta (x, y) => Syntax.Formula.Pred (Syntax.Constraint.Gt (Syntax.Difference.single x, integer_of_int y)) |
            Model_Checker.Loc (auto_num, loc_num) => Syntax.Formula.Loc (auto_num_to_name auto_num, auto_and_loc_nums_to_name auto_num loc_num)
        )

    fun convert_formula 
            (auto_num_to_name: nat -> string) 
            (auto_and_loc_nums_to_name: nat -> nat -> string)
            (form: isa_formula): (string, inta) Syntax.formula 
        let 
            val f = convert_sexp auto_num_to_name auto_and_loc_nums_to_name
        in (case form of
            Model_Checker.EX x => Syntax.Formula.Ex (f x) |
            Model_Checker.AX x => Syntax.Formula.Ax (f x) |
            Model_Checker.EG x => Syntax.Formula.Eg (f x) 
            Model_Checker.AG x => Syntax.Formula.Ag (f x) |
            Model_Checker.Leadsto (x, y) => Syntax.Formula.Leadsto (f x, f y)
        )
        end

    fun convert_network (net: clocks_name_network): ParseBexpTypes.network = 
        let 
            val (clocks, 
                auto_names, 
                (node_ids_to_names, 
                    auto_names_to_index, 
                    broadcast, 
                    automata,
                    vars_and_bounds,
                    formula,
                    init_locs,
                    init_vars)) = net;

            val (v, vars_and_bounds) = get_arbitrary_var vars_and_bounds;
            val vars = map make_var vars_and_bounds;
            val indexed_auto_names = sort_by_index auto_names auto_names_to_index;

            val automata =
                (zip init_locs automata) 
                |> List.map ((fn (i, (l, a)) => (node_ids_to_names i, (l, a)))
                        #> (fn (n, (l, a)) => convert_automaton v n l a))
                |> ListPair.zip indexed_auto_names;

            val auto_num_to_name = (fn n => List.nth n indexed_auto_names)
            val formula = convert_formula auto_num_to_name node_ids_to_names formula;
        in {
            automata = automata,
            clocks = clocks,
            vars = vars,
            formula = formula,
            broadcast_channels = broadcast
        }
        end
end
