(* To do: 
    - Use Error Monad like in mlunta/product_construction/rewrite_bexps.sml 
    - Organise code and type declarations 
*)
signature NETWORK_CONVERSION = sig
    
    val convert_network: NetworkConversionTypes.clocks_name_network -> ParseBexpTypes.network
end

structure NetworkConversion : NETWORK_CONVERSION =
struct
    open Syntax
    open NetworkConversionTypes

    fun invert_constraint (constr: (string diff, int) constraint) : (string, int) guard =
        (case constr of
            Constraint.Eq (a, b) => Guard.Or (Guard.Constr (Constraint.Lt (a, b)), Guard.Constr (Constraint.Gt (a, b))) |
            Constraint.Le (a, b) => Guard.Constr (Constraint.Gt (a, b)) |
            Constraint.Lt (a, b) => Guard.Constr (Constraint.Ge (a, b)) |
            Constraint.Ge (a, b) => Guard.Constr (Constraint.Lt (a, b)) |
            Constraint.Gt (a, b) => Guard.Constr (Constraint.Ge (a, b))
        )


    (* vc is an arbitrary clock or variable.
        Adding some arbitrary clock might affect the renaming. Does MLunta use an urgent clock.
        This function is used for guards and not constraints. There is *)
    fun invert_guard (vc: string) (guard: (string, int) guard) : (string, int) guard =
        let
            val false_constr = Constraint.Gt (Difference.Diff (vc, vc), (0:Int.int));
            val always_false : (string, int) guard = Guard.Constr false_constr
            fun ig guard = (case guard of 
                Guard.True => always_false |
                Guard.Constr x => (
                    if (Guard.Constr x = always_false) 
                    then Guard.True 
                    else invert_constraint x) |
                Guard.And (x, y) => Guard.Or (ig x, ig y) |
                Guard.Or (x, y) => Guard.And (ig x, ig y)
            )
        in ig guard
        end

    (* This does not fully implement features supported by Munta.
    - Arbitrary operators: Unop f x, Binop f x y
    - If then else: If_then_else b x y 

    *)

    (* unsafe *)
    fun is_plus f = (f (Model_Checker.Int_of_integer 2) (Model_Checker.Int_of_integer 5)) 
        |> Model_Checker.integer_of_int |> (fn x => x = (7))

    fun is_minus f = (f (Model_Checker.Int_of_integer 1) (Model_Checker.Int_of_integer 2)) 
        |> Model_Checker.integer_of_int |> (fn x => x = ~1)
    exception Unsupported of string
    
    (* These are not clocks. These are variables *)
    fun convert_exp_left (guard_exp: (string, inta) Model_Checker.exp): string Difference.clock_pair =
        (case guard_exp of
            Model_Checker.Var x => Difference.Single x |
            Model_Checker.Binop (f, Model_Checker.Var x, Model_Checker.Var y) =>
                (case is_minus f of 
                    true => Difference.Diff (x, y) |
                    _ => raise Unsupported "Not a valid variable (difference) constraint. Ill-defined LHS. Should be minus.") |
            _ => raise Unsupported "Not a valid variable (difference) constraint. Ill-defined LHS. Should be x - y or x."
        ) (* The datatypes that are parsed by MLunta do not explicitly mark variables as different to clocks.*)

    fun convert_exp_right (guard_exp: (string, inta) Model_Checker.exp): int =
        (case guard_exp of
            Model_Checker.Const x => Model_Checker.integer_of_int x |
            _ => Exn.error "RHS of comparison must be constant."
        )

    fun convert_comparison (comp: (string, inta) Model_Checker.bexp): (string, int) guard =
        Guard.Constr ((case comp of
            Model_Checker.Eq  x => (Constraint.Eq, x) |
            Model_Checker.Lea x => (Constraint.Le, x) |
            Model_Checker.Lta x => (Constraint.Lt, x) |
            Model_Checker.Ge x  => (Constraint.Ge, x) |
            Model_Checker.Gt x  => (Constraint.Gt, x) |
            _ => raise Unsupported "Invalid expression in guard or constraint of edge. Not a comparison."
        ) |> (fn (f, (l, r)) => f (convert_exp_left l, convert_exp_right r)))

    fun convert_guard (vc: string) (guard: (string, inta) Model_Checker.bexp): (string, int) guard = 
    let 
        val invert_guard = invert_guard vc;
        fun convert_guard' guard =
            (case guard of 
                Model_Checker.True => Guard.True |
                Model_Checker.Not x => invert_guard (convert_guard' x) |
                Model_Checker.And (x, y) => Guard.And (convert_guard' x, convert_guard' y) |
                Model_Checker.Or (x, y) => Guard.Or (convert_guard' x, convert_guard' y) |
                Model_Checker.Imply (x, y) => 
                    let val x' = convert_guard' x;
                        val y' = convert_guard' y
                    in Guard.Or (invert_guard x', Guard.And (x', y'))
                    end |
                Model_Checker.Eq x  => convert_comparison (Model_Checker.Eq x) |
                Model_Checker.Lea x => convert_comparison (Model_Checker.Lea x) |
                Model_Checker.Lta x => convert_comparison (Model_Checker.Lta x) |
                Model_Checker.Ge x  => convert_comparison (Model_Checker.Ge x) |
                Model_Checker.Gt x  => convert_comparison (Model_Checker.Gt x)
            )
    in convert_guard' guard
    end

    fun convert_guard_constraint (constr: (string, inta) Model_Checker.acconstraint): (string diff, int) constraint =
        let fun convert_pair (x, y) = (Difference.Single x, Model_Checker.integer_of_int y)
        in (case constr of 
            Model_Checker.LT x => (Constraint.Lt (convert_pair x)) |
            Model_Checker.LE x => (Constraint.Le (convert_pair x)) |
            Model_Checker.EQ x => (Constraint.Eq (convert_pair x)) |
            Model_Checker.GE x => (Constraint.Ge (convert_pair x)) |
            Model_Checker.GT x => (Constraint.Gt (convert_pair x))
        ) 
        end

    fun convert_guard_constraints (cs: (string, inta) Model_Checker.acconstraint list): (string, int) guard =
        cs
        |> map convert_guard_constraint
        |> map Guard.Constr
        |> List.foldl Guard.And Guard.True

    
    fun convert_invariant_constraint (constr: (string, inta) Model_Checker.acconstraint): (string, int) constraint =
        let fun convert_pair (x, y) = (x, Model_Checker.integer_of_int y)
        in (case constr of 
            Model_Checker.LT x => (Constraint.Lt (convert_pair x)) |
            Model_Checker.LE x => (Constraint.Le (convert_pair x)) |
            Model_Checker.EQ x => (Constraint.Eq (convert_pair x)) |
            Model_Checker.GE x => (Constraint.Ge (convert_pair x)) |
            Model_Checker.GT x => (Constraint.Gt (convert_pair x))
        ) 
        end

    fun convert_invariant_constraints (cs: (string, inta) Model_Checker.acconstraint list): (string, int) invariant =
        cs
        |> map convert_invariant_constraint
        |> map Invariant.Constr
        |> List.foldl Invariant.And Invariant.True


    fun convert_action (act: string Model_Checker.act): string action =
        (case act of
            Model_Checker.In x  => In x |
            Model_Checker.Out x => Out x |
            Model_Checker.Sil x => Internal x
        )

    fun convert_update (upd: string * (string, inta) Model_Checker.exp): string update =
        (case upd of
            (x, Model_Checker.Const c) => Reset (x, Model_Checker.integer_of_int c) |
            (x, Model_Checker.Binop (f, Model_Checker.Var v, Model_Checker.Const c)) =>
                let 
                    val c = Model_Checker.integer_of_int c;
                    val offset = (case (is_minus f, is_plus f) of
                            (true, false) => ~c |
                            (false, true) => c |
                            _ => raise Unsupported "Invalid update. Unknown operator on RHS")
                in (if x = v then Shift (x, offset) else (Update (x, v, offset)))
                    (* (case (x = v, offset = 0) of 
                        (false, false) => Update (x, v, offset) |
                        (_, true) => Copy (x, v) |
                        (true, false) => Shift (x, offset) |
                    ) *)
                end
            |
            _ => raise Unsupported "Invalid update. RHS not neither constant nor relative (v op c)."
        )

    fun convert_updates (upds: (string * (string, inta) Model_Checker.exp) list): (string update list) =
        map convert_update upds

    val convert_resets = 
        map (fn x => Reset (x, 0))

    (* Note; naming collisions are handled by MLunta *)
    fun convert_edge (vc: string) (edge: NetworkConversionTypes.isa_edge): ParseBexpTypes.edge =
        let 
            val (out_loc, guard, constr, action, updates, resets, in_loc) = edge;
            val guard = convert_guard vc guard;
            val constr = convert_guard_constraints constr;
            val guard = Guard.And(guard, constr);
            val act = convert_action action;
            val upds = convert_updates updates;
            val resets = convert_resets resets;
            val upds = upds @ resets
        in {
            source = Model_Checker.integer_of_nat out_loc,
            guard = guard,
            label = act,
            update = upds,
            target = Model_Checker.integer_of_nat in_loc
        }
        end

    

    fun convert_node 
        (name_asmt: nat -> string)
        (inv_asmt: nat -> (string, inta) Model_Checker.acconstraint list) 
        (node_id: nat) 
        = {
            id = Model_Checker.integer_of_nat node_id,
            name = name_asmt node_id,
            invariant = inv_asmt node_id |> convert_invariant_constraints
        }

    fun edge_nodes (out_loc, guard, constr, action, updates, resets, in_loc) =
        [out_loc, in_loc]
    
    fun all_edge_nodes edges =
        edges
        |> List.map edge_nodes
        |> List.concat

    fun all_inv_nodes invs = 
        map fst invs

    fun convert_automaton 
        (vc: string) (name_asmt: nat -> string) (initial: nat)
        (auto: NetworkConversionTypes.isa_automaton): ParseBexpTypes.automaton =
        let
            val (committed, urgent, edges, invs) = auto;
            val inv_asmt = ListUtils.pair_list_to_fun invs (List.nil);
            val nodes = all_edge_nodes edges @ all_inv_nodes invs @ committed @ urgent
                |> ListMergeSort.uniqueSort (fn (x, y) => Int.compare (Model_Checker.integer_of_nat x, Model_Checker.integer_of_nat y))
                |> map (convert_node name_asmt inv_asmt)
            val edges = map (convert_edge vc) edges;
        in {
            committed = map Model_Checker.integer_of_nat committed,
            urgent = map Model_Checker.integer_of_nat urgent,
            initial = Model_Checker.integer_of_nat initial,
            edges = edges,
            nodes = nodes
        }
        end

    (* Arbitrary variable to ensure it is always possible to create an unsatisfiable guard. *)
    val arbitrary_var = ("var12345", Model_Checker.Int_of_integer 0, Model_Checker.Int_of_integer 0)

    fun add_arbitrary_var xs = arbitrary_var::xs

    fun get_arbitrary_var xs = 
        (if (length xs) = 0 then add_arbitrary_var xs else xs)
        |> (fn xs => (hd xs, xs))

    fun make_var (v, l, u): var =
        { 
            name = v,
            lower = Model_Checker.integer_of_int l,
            upper = Model_Checker.integer_of_int u
        }

    fun convert_sexp 
            (auto_num_to_name: nat -> string) 
            (auto_and_loc_nums_to_name: nat -> nat -> string)
            (exp: isa_state_exp): (string, int) Formula.bexp =
        let 
            fun conv exp = (case exp of
                Model_Checker.Truea => Formula.True |
                Model_Checker.Nota x => Formula.Not (conv x) |
                Model_Checker.Anda (x, y) => Formula.And (conv x, conv y) |
                Model_Checker.Ora (x, y) => Formula.Or (conv x, conv y) |
                Model_Checker.Implya (x, y) => Formula.Impl (conv x, conv y) |
                Model_Checker.Eqa (x, y) => Formula.Pred (Constraint.Eq (Difference.Single x, Model_Checker.integer_of_int y)) |
                Model_Checker.Leb (x, y) => Formula.Pred (Constraint.Le (Difference.Single x, Model_Checker.integer_of_int y)) |
                Model_Checker.Ltb (x, y) => Formula.Pred (Constraint.Lt (Difference.Single x, Model_Checker.integer_of_int y)) |
                Model_Checker.Gea (x, y) => Formula.Pred (Constraint.Ge (Difference.Single x, Model_Checker.integer_of_int y)) |
                Model_Checker.Gta (x, y) => Formula.Pred (Constraint.Gt (Difference.Single x, Model_Checker.integer_of_int y)) |
                Model_Checker.Loc (auto_num, loc_num) => Formula.Loc (auto_num_to_name auto_num, auto_and_loc_nums_to_name auto_num loc_num))
        in conv exp
        end

    fun convert_formula 
            (auto_num_to_name: nat -> string) 
            (auto_and_loc_nums_to_name: nat -> nat -> string)
            (form: isa_formula): (string, int) formula =
        let val f = convert_sexp auto_num_to_name auto_and_loc_nums_to_name
        in (case form of
            Model_Checker.EX x => Formula.Ex (f x) |
            Model_Checker.AX x => Formula.Ax (f x) |
            Model_Checker.EG x => Formula.Eg (f x) |
            Model_Checker.AG x => Formula.Ag (f x) |
            Model_Checker.Leadsto (x, y) => Formula.Leadsto (f x, f y)
        )
        end

    fun convert_network (
            (clocks, 
                (auto_names, 
                    (node_ids_to_names, 
                    auto_names_to_index, 
                    broadcast, 
                    automata,
                    vars_and_bounds,
                    formula,
                    init_locs,
                    init_vars))) : clocks_name_network): ParseBexpTypes.network = 
        let 
            val ((v, _, _), vars_and_bounds) = get_arbitrary_var vars_and_bounds;
            val vars = map make_var vars_and_bounds;
            val indexed_auto_names = ListUtils.sort_by_index auto_names (auto_names_to_index #> Model_Checker.integer_of_nat);

            val automata =
                (ListPair.zip (init_locs, automata))
                |> ListUtils.zip_with_index
                |> List.map ((fn ((l, a), i) => (node_ids_to_names (Model_Checker.nat_of_integer i), l, a))
                        #> (fn (n, l, a) => convert_automaton v n l a))
                |> (fn xs => ListPair.zip (indexed_auto_names, xs));

            val auto_num_to_name = (fn n => List.nth (indexed_auto_names, Model_Checker.integer_of_nat n))
            val formula = convert_formula auto_num_to_name node_ids_to_names formula
        in {
            automata = automata,
            clocks = clocks,
            vars = vars,
            formula = formula,
            broadcast_channels = broadcast
        }
        end
end
