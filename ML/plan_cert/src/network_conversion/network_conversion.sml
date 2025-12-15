(* To do: 
    - Use Error Monad like in mlunta/product_construction/rewrite_bexps.sml 
    - Organise code and type declarations 
*)
signature NETWORK_CONVERSION = sig
    
    val convert_network: bool -> string -> NetworkConversionTypes.clocks_name_network -> ParseBexpTypes.network
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
        Adding an arbitrary clock might affect the renaming. Does MLunta use an urgent clock.
        This function is used for guards and not constraints. There is *)
    fun invert_guard (vc: string) (guard: (string, int) guard) : (string, int) guard =
        let
            val false_constr = Constraint.Gt (Difference.Diff (vc, vc), (0:Int.int));
            val always_false : (string, int) guard = Guard.Constr false_constr
            fun ig guard = (case guard of 
                Guard.True => always_false |
                Guard.Constr x => (invert_constraint x) |
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
    fun is_plus f = (f (Converter.Int_of_integer 2) (Converter.Int_of_integer 5)) 
        |> Converter.integer_of_int |> (fn x => x = 7)

    fun is_minus f = (f (Converter.Int_of_integer 1) (Converter.Int_of_integer 2)) 
        |> Converter.integer_of_int |> (fn x => x = ~1)
    exception Unsupported of string
    
    (* These are not clocks. These are variables *)
    fun convert_exp_left (guard_exp: (string, inta) Converter.exp): string Difference.clock_pair =
        (case guard_exp of
            Converter.Var x => Difference.Single x |
            Converter.Binop (f, Converter.Var x, Converter.Var y) =>
                (case is_minus f of 
                    true => Difference.Diff (x, y) |
                    _ => raise Unsupported "Not a valid variable (difference) constraint. Ill-defined LHS. Should be minus.") |
            _ => raise Unsupported "Not a valid variable (difference) constraint. Ill-defined LHS. Should be x - y or x."
        ) (* The datatypes that are parsed by MLunta do not explicitly mark variables as different from clocks.*)

    fun convert_exp_right (guard_exp: (string, inta) Converter.exp): int =
        (case guard_exp of
            Converter.Const x => Converter.integer_of_int x |
            _ => Exn.error "RHS of comparison must be constant."
        )

    fun convert_comparison (comp: (string, inta) Converter.bexp): (string, int) guard =
        Guard.Constr ((case comp of
            Converter.Eqa x => (Constraint.Eq, x) |
            Converter.Lea x => (Constraint.Le, x) |
            Converter.Ltb x => (Constraint.Lt, x) |
            Converter.Ge x  => (Constraint.Ge, x) |
            Converter.Gta x  => (Constraint.Gt, x) |
            _ => raise Unsupported "Invalid expression in guard or constraint of edge. Not a comparison."
        ) |> (fn (f, (l, r)) => f (convert_exp_left l, convert_exp_right r)))

    fun convert_guard (vc: string) (guard: (string, inta) Converter.bexp): (string, int) guard = 
    let 
        val invert_guard = invert_guard vc;
        fun convert_guard' guard =
            (case guard of 
                Converter.True => Guard.True |
                Converter.Nota x => invert_guard (convert_guard' x) |
                Converter.Anda (x, y) => Guard.And (convert_guard' x, convert_guard' y) |
                Converter.Ora (x, y) => Guard.Or (convert_guard' x, convert_guard' y) |
                Converter.Imply (x, y) => 
                    let val x' = convert_guard' x;
                        val y' = convert_guard' y
                    in Guard.Or (invert_guard x', Guard.And (x', y'))
                    end |
                Converter.Eqa x  => convert_comparison (Converter.Eqa x) |
                Converter.Lea x => convert_comparison (Converter.Lea x) |
                Converter.Ltb x => convert_comparison (Converter.Ltb x) |
                Converter.Ge x  => convert_comparison (Converter.Ge x) |
                Converter.Gta x  => convert_comparison (Converter.Gta x)
            )
    in convert_guard' guard
    end

    fun convert_guard_constraint (constr: (string, inta) Converter.acconstraint): (string diff, int) constraint =
        let fun convert_pair (x, y) = (Difference.Single x, Converter.integer_of_int y)
        in (case constr of 
            Converter.LTa x => (Constraint.Lt (convert_pair x)) |
            Converter.LEa x => (Constraint.Le (convert_pair x)) |
            Converter.EQ x => (Constraint.Eq (convert_pair x)) |
            Converter.GEa x => (Constraint.Ge (convert_pair x)) |
            Converter.GTa x => (Constraint.Gt (convert_pair x))
        ) 
        end

    fun convert_guard_constraints (cs: (string, inta) Converter.acconstraint list): (string, int) guard =
        cs
        |> map convert_guard_constraint
        |> map Guard.Constr
        |> List.foldl Guard.And Guard.True

    fun simplify_guard (g: ('a, 'b) guard) : ('a, 'b) guard = case g of 
        Guard.True => Guard.True |
        Guard.Constr c => Guard.Constr c |
        Guard.And (a, b) => (case (simplify_guard a, simplify_guard b) of
            (Guard.True, b) => b |
            (a, Guard.True) => a |
            (a, b) => Guard.And (a, b)
        ) |
        Guard.Or (a, b) => (case (simplify_guard a, simplify_guard b) of
            (Guard.True, b) => Guard.True |
            (a, Guard.True) => Guard.True |
            (a, b) => Guard.Or (a, b)
        )

    
    fun convert_invariant_constraint (constr: (string, inta) Converter.acconstraint): (string, int) constraint =
        let fun convert_pair (x, y) = (x, Converter.integer_of_int y)
        in (case constr of 
            Converter.LTa x => (Constraint.Lt (convert_pair x)) |
            Converter.LEa x => (Constraint.Le (convert_pair x)) |
            Converter.EQ x => (Constraint.Eq (convert_pair x)) |
            Converter.GEa x => (Constraint.Ge (convert_pair x)) |
            Converter.GTa x => (Constraint.Gt (convert_pair x))
        ) 
        end

    fun convert_invariant_constraints (cs: (string, inta) Converter.acconstraint list): (string, int) invariant =
        cs
        |> map convert_invariant_constraint
        |> map Invariant.Constr
        |> List.foldl Invariant.And Invariant.True

    fun simplify_invariant (inv : ('a, 'b) invariant) = case inv of
        Invariant.True => Invariant.True |
        Invariant.Constr c => Invariant.Constr c |
        Invariant.And (a, b) => (case (simplify_invariant a, simplify_invariant b) of
            (Invariant.True, b) => b |
            (a, Invariant.True) => a |
            (a, b) => Invariant.And (a, b)
        )


    fun convert_action (act: string Converter.act): string action =
        (case act of
            Converter.In x  => In x |
            Converter.Out x => Out x |
            Converter.Sil x => Internal x
        )

    fun convert_update (upd: string * (string, inta) Converter.exp): string update =
        (case upd of
            (x, Converter.Const c) => Reset (x, Converter.integer_of_int c) |
            (x, Converter.Binop (f, Converter.Var v, Converter.Const c)) =>
                let 
                    val c = Converter.integer_of_int c;
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

    fun convert_updates (upds: (string * (string, inta) Converter.exp) list): (string update list) =
        map convert_update upds

    val convert_resets = 
        map (fn x => Reset (x, 0))

    (* Note; naming collisions are handled by MLunta *)
    fun convert_edge (vc: string) (edge: NetworkConversionTypes.isa_edge): ParseBexpTypes.edge =
        let 
            val (out_loc, (guard, (constr, (action, (updates, (resets, in_loc)))))) = edge
            val guard = convert_guard vc guard
            val constr = convert_guard_constraints constr

            val act = convert_action action

            val upds = convert_updates updates
            val resets = convert_resets resets
        in {
            source = Converter.integer_of_nat out_loc,
            guard = simplify_guard (Guard.And (guard, constr)),
            label = act,
            update = upds @ resets,
            target = Converter.integer_of_nat in_loc
        }
        end

    

    fun convert_node 
        (name_asmt: nat -> string)
        (inv_asmt: nat -> (string, inta) Converter.acconstraint list) 
        (node_id: nat) 
        = {
            id = Converter.integer_of_nat node_id,
            name = name_asmt node_id,
            invariant = inv_asmt node_id |> convert_invariant_constraints |> simplify_invariant
        }

    fun edge_nodes (out_loc, (guard, (constr, (action, (updates, (resets, in_loc)))))) =
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
            val (committed, (urgent, (edges, invs))) = auto;
            val inv_asmt = ListUtils.pair_list_to_fun invs (List.nil);
            val nodes = all_edge_nodes edges @ all_inv_nodes invs @ committed @ urgent
                |> ListMergeSort.uniqueSort (fn (x, y) => Int.compare (Converter.integer_of_nat x, Converter.integer_of_nat y))
                |> map (convert_node name_asmt inv_asmt)
            val edges = map (convert_edge vc) edges;
        in {
            committed = map Converter.integer_of_nat committed,
            urgent = map Converter.integer_of_nat urgent,
            initial = Converter.integer_of_nat initial,
            edges = edges,
            nodes = nodes
        }
        end

    (* Arbitrary variable to ensure it is always possible to create an unsatisfiable guard. *)
    val arbitrary_var = ("var12345", (Converter.Int_of_integer 0, Converter.Int_of_integer 0))

    fun add_arbitrary_var xs = arbitrary_var::xs

    fun get_arbitrary_var xs = 
        (if (length xs) = 0 then add_arbitrary_var xs else xs)
        |> (fn xs => (hd xs, xs))

    fun make_var (v, (l, u)): var =
        { 
            name = v,
            lower = Converter.integer_of_int l,
            upper = Converter.integer_of_int u
        }

    fun convert_sexp 
            (auto_num_to_name: nat -> string) 
            (auto_and_loc_nums_to_name: nat -> nat -> string)
            (exp: isa_state_exp): (string, int) Formula.bexp =
        let 
            fun conv exp = (case exp of
                Converter.Truea => Formula.True |
                Converter.Notb x => Formula.Not (conv x) |
                Converter.Andb (x, y) => Formula.And (conv x, conv y) |
                Converter.Orb (x, y) => Formula.Or (conv x, conv y) |
                Converter.Implya (x, y) => Formula.Impl (conv x, conv y) |
                Converter.Eqb (x, y) => Formula.Pred (Constraint.Eq (Difference.Single x, Converter.integer_of_int y)) |
                Converter.Leb (x, y) => Formula.Pred (Constraint.Le (Difference.Single x, Converter.integer_of_int y)) |
                Converter.Ltc (x, y) => Formula.Pred (Constraint.Lt (Difference.Single x, Converter.integer_of_int y)) |
                Converter.Gea (x, y) => Formula.Pred (Constraint.Ge (Difference.Single x, Converter.integer_of_int y)) |
                Converter.Gtb (x, y) => Formula.Pred (Constraint.Gt (Difference.Single x, Converter.integer_of_int y)) |
                Converter.Loc (auto_num, loc_num) => Formula.Loc (auto_num_to_name auto_num, auto_and_loc_nums_to_name auto_num loc_num))
        in conv exp
        end

    fun convert_formula 
            (auto_num_to_name: nat -> string) 
            (auto_and_loc_nums_to_name: nat -> nat -> string)
            (form: isa_formula): (string, int) formula =
        let val f = convert_sexp auto_num_to_name auto_and_loc_nums_to_name
        in (case form of
            Converter.EX x => Formula.Ex (f x) |
            Converter.AX x => Formula.Ax (f x) |
            Converter.EG x => Formula.Eg (f x) |
            Converter.AG x => Formula.Ag (f x) |
            Converter.Leadsto (x, y) => Formula.Leadsto (f x, f y)
        )
        end

    fun save_network show_net net_file net =
    let
        val net_str = net |> NetworkToString.to_string
        val _ = if show_net then Log.info net_str else () 
    in TextIOUtil.save_data net_file net_str
    end

    fun convert_network show_net net_file
            ((clocks, 
                (auto_names, 
                    (node_ids_to_names, 
                        (auto_names_to_index, 
                            (broadcast, 
                                (automata,
                                    (vars_and_bounds,
                                        (formula,
                                            (init_locs,
                                            init_vars))))))))) : clocks_name_network): ParseBexpTypes.network = 
        let 
            val ((v, (_, _)), vars_and_bounds) = get_arbitrary_var vars_and_bounds;
            val vars = map make_var vars_and_bounds;
            val indexed_auto_names = ListUtils.sort_by_index auto_names (auto_names_to_index #> Converter.integer_of_nat);

            val automata =
                (ListPair.zip (init_locs, automata))
                |> ListUtils.zip_with_index
                |> List.map ((fn ((l, a), i) => (node_ids_to_names (Converter.nat_of_integer i), l, a))
                        #> (fn (name_fun, l, a) => convert_automaton v name_fun l a))
                |> (fn xs => ListPair.zip (indexed_auto_names, xs)); (* Needs to preserve order, since indexes are used in renamings. *)

            val auto_num_to_name = (fn n => List.nth (indexed_auto_names, Converter.integer_of_nat n))
            val formula = convert_formula auto_num_to_name node_ids_to_names formula
            val res = {
                automata = automata,
                clocks = clocks,
                vars = vars,
                formula = formula,
                broadcast_channels = broadcast
            }
            val _ = save_network show_net net_file res
        in res
        end
end
