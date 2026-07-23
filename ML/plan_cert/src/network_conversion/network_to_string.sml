fun strv s = "\"" ^ s ^ "\""

fun key_val k v = "\"" ^ k ^ "\": " ^ v

structure JsonObjectToString : TO_STRING = ListToString(
    structure Ty = StringToString
    val sep = ", "
    val start_delim = "{"
    val end_delim = "}"
)

structure JsonListToString : TO_STRING = ListToString(
    structure Ty = StringToString
    val sep = ", "
    val start_delim = "["
    val end_delim = "]"
)

structure VarToString : TO_STRING =
struct
    type t = Syntax.var

    fun to_string {name, lower, upper} = 
        name ^ "[" ^ IntToStringSign.to_string lower ^ ":" ^ IntToStringSign.to_string upper ^ "]"
end

functor ConstraintToString(
    structure X : TO_STRING
    structure Y : TO_STRING
) : TO_STRING =
struct
    type t = (X.t, Y.t) Syntax.Constraint.constraint
    
    open Syntax
    open Constraint

    fun to_string (Eq (a, b)) = X.to_string a ^ " = " ^ Y.to_string b |
        to_string (Le (a, b)) = X.to_string a ^ " <= " ^ Y.to_string b |
        to_string (Lt (a, b)) = X.to_string a ^ " < " ^ Y.to_string b |
        to_string (Ge (a, b)) = X.to_string a ^ " >= " ^ Y.to_string b |
        to_string (Gt (a, b)) = X.to_string a ^ " > " ^ Y.to_string b
end


functor InvariantToString(
    structure X : TO_STRING
    structure Y : TO_STRING
) : TO_STRING =
struct
    type t = (X.t, Y.t) Syntax.invariant
    structure C = ConstraintToString(
        structure X = X
        structure Y = Y
    )

    open Syntax
    open Invariant

    fun to_string' True = "True" |
        to_string' (Constr c) = C.to_string c |
        to_string' (And (a, b)) = to_string' a ^ " && " ^ to_string' b
    
    fun to_string True = "" |
        to_string inv = to_string' inv
end

functor DifferenceToString(
    X : TO_STRING
) : TO_STRING =
struct
    type t = X.t Syntax.diff
    open Syntax
    open Difference
    fun to_string (Single v) = X.to_string v
      | to_string (Diff (u, v)) = X.to_string u ^ " - " ^ X.to_string v
end

functor GuardToString(
    X : TO_STRING
) : TO_STRING =
struct
    type t = X.t Syntax.Guard.guard
    open Syntax
    open Guard
    fun to_string' True = "True" |
        to_string' (And (l, r)) = to_string' l ^ " && " ^ to_string' r |
        to_string' (Or (l, r)) = "(" ^ to_string' l ^ " || " ^ to_string' r ^ ")" |
        to_string' (Constr c) = X.to_string c

    fun to_string True = "" | 
        to_string g = to_string' g
end


functor ActionToString(
    X : TO_STRING
): TO_STRING =
struct
    type t = X.t Syntax.action
    open Syntax
    fun to_string (Internal x) = X.to_string x|
        to_string (Out x) = X.to_string x ^ "!" |
        to_string (In x) =  X.to_string x ^ "?"
end

functor UpdateToString(
    X : TO_STRING
) : TO_STRING =
struct
    type t = X.t Syntax.update
    open Syntax
    fun to_string (Reset (x, i)) = X.to_string x ^ " := " ^ IntToStringSign.to_string i |
        to_string (Copy (x, y)) = X.to_string x ^ " := " ^ X.to_string y |
        to_string (Shift (x, i)) = X.to_string x ^ " := " ^ X.to_string x ^ " + " ^ IntToStringSign.to_string i |
        to_string (Update (x, y, i)) = X.to_string x ^ " := " ^ X.to_string y ^ " + " ^ IntToStringSign.to_string i
end

structure NodeToString : TO_STRING =
struct
    type t = ParseBexpTypes.node
    structure I = InvariantToString(
        structure X = StringToString
        structure Y = IntToStringSign
    )

    fun to_string {id, name, invariant} = 
    let 
        val id_string = key_val "id" (IntToStringSign.to_string id)
        val name_string = key_val "name" (strv name)
        val invariant_string = key_val "invariant" (strv (I.to_string invariant))
    in JsonObjectToString.to_string [id_string, name_string, invariant_string]
    end
end

structure EdgeToString : TO_STRING =
struct
    structure G = GuardToString(
        ConstraintToString(
            structure X = DifferenceToString(StringToString)
            structure Y = IntToStringSign
        )
    )

    structure U = UpdateToString(StringToString)

    structure US = ListToString(
        structure Ty = U
        val sep = ", "
        val start_delim = "\""
        val end_delim = "\""
    )

    structure L = ActionToString(StringToString)

    type t = ParseBexpTypes.edge

    fun to_string{source, target, guard, label, update} =
    let 
        val source_string = key_val "source" (IntToStringSign.to_string source)
        val target_string = key_val "target" (IntToStringSign.to_string target)
        val guard_string = key_val "guard" (strv (G.to_string guard))
        val label_string = key_val "label" (strv (L.to_string label))
        val update_string = key_val "update" (US.to_string update)
    in
        JsonObjectToString.to_string [source_string, target_string, guard_string, label_string, update_string]
    end
end

structure AutomatonToString : TO_STRING =
struct
    type t = (string * ParseBexpTypes.automaton)
    
    fun to_string (name, {nodes, edges, initial, committed, urgent}) =
    let 
        val name_string = key_val "name" (strv name)
        val node_string = key_val "nodes" (nodes |> map NodeToString.to_string |> JsonListToString.to_string)
        val edge_string = key_val "edges" (edges |> map EdgeToString.to_string |> JsonListToString.to_string)
        val init_string = key_val "initial" (IntToStringSign.to_string initial)
        val committed_string = key_val "committed" (committed |> map IntToStringSign.to_string |> JsonListToString.to_string)
        val urgent_string = key_val "urgent" (urgent |> map IntToStringSign.to_string |> JsonListToString.to_string)
    in
        JsonObjectToString.to_string [name_string, node_string, committed_string, urgent_string, init_string, edge_string]
    end
end

functor FormulaBToString(
    structure X : TO_STRING
    structure Y : TO_STRING
) : TO_STRING =
struct
    structure C = ConstraintToString(
        structure X = DifferenceToString(X)
        structure Y = Y
    )
    type t = (X.t, Y.t) Syntax.Formula.bexp

    open Syntax
    open Formula

    fun to_string True = "True" |
        to_string (Not f) = "!" ^ to_string f |
        to_string (And (f, g)) = "(" ^ to_string f ^ " && " ^ to_string g ^ ")" |
        to_string (Or (f, g)) = "(" ^ to_string f ^ " || " ^ to_string g ^ ")" |
        to_string (Impl (f, g)) = "(" ^ to_string f ^ " -> " ^ to_string g ^ ")" |
        to_string (Loc (a, b)) = X.to_string a ^ "." ^ X.to_string b |
        to_string (Pred c) = C.to_string c
end

functor FormulaFToString(X : TO_STRING) : TO_STRING =
struct
    type t = X.t Syntax.Formula.F
    open Syntax
    open Formula
    fun to_string (Ex a) = "E<> " ^ X.to_string a |
        to_string (Eg a) = "E[] " ^ X.to_string a |
        to_string (Ax a) = "A<> " ^ X.to_string a |
        to_string (Ag a) = "A[] " ^ X.to_string a |
        to_string (Leadsto (a, b)) = X.to_string a ^ " --> " ^ X.to_string b
end

functor FormulaToString(
    structure X : TO_STRING 
    structure Y : TO_STRING
) : TO_STRING =
struct
    type t = (X.t, Y.t) Syntax.formula

    structure B = FormulaBToString(
        structure X = X
        structure Y = Y
    )

    structure F = FormulaFToString(B)

    val to_string = F.to_string
end


structure NetworkToString : TO_STRING =
struct

    type t = ParseBexpTypes.network
    
    structure VS = ListToString(
        structure Ty = VarToString
        val sep = ", "
        val start_delim = "\""
        val end_delim = "\""
    )

    structure F = FormulaToString(
        structure X = StringToString
        structure Y = IntToStringSign
    )

    structure CS = ListToString(
        structure Ty = StringToString
        val sep = ", "
        val start_delim = "\""
        val end_delim = "\""
    )

    fun to_string {automata, clocks, vars, formula, broadcast_channels} =
    let
        val automata_string = key_val "automata" (automata |> map AutomatonToString.to_string |> JsonListToString.to_string)
        val clock_string = key_val "clocks" (clocks |> CS.to_string)
        val var_string = key_val "vars" (vars |> VS.to_string)
        val formula_string =  key_val "formula" (formula |> F.to_string |> strv)
        val broadcast_string = key_val "broadcast" (broadcast_channels |> JsonListToString.to_string)
    in
        JsonObjectToString.to_string [automata_string, clock_string, var_string, formula_string, broadcast_string]
    end

end