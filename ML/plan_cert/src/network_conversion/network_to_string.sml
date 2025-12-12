structure VarToString : TO_STRING =
struct
    type t = Syntax.var

    fun to_string {name, lower, upper} = 
    let 
        val name_string = "(name: " ^ name ^ ")"
        val bounds_string = "(bounds: " ^ Int.toString lower ^ " " ^ Int.toString upper ^ ")"
    in
        "(Var " ^ " " ^ name_string ^ " " ^ bounds_string ^ ")"
    end
end

functor ConstraintToString(
    structure X : TO_STRING
    structure Y : TO_STRING
) : TO_STRING =
struct
    type t = (X.t, Y.t) Syntax.Constraint.constraint
    
    open Syntax
    open Constraint

    fun to_string (Eq (a, b)) = "(= " ^ X.to_string a ^ " " ^ Y.to_string b ^ ")" |
        to_string (Le (a, b)) = "(<= " ^ X.to_string a ^ " " ^ Y.to_string b ^ ")" |
        to_string (Lt (a, b)) = "(< " ^ X.to_string a ^ " " ^ Y.to_string b ^ ")" |
        to_string (Ge (a, b)) = "(>= " ^ X.to_string a ^ " " ^ Y.to_string b ^ ")" |
        to_string (Gt (a, b)) = "(> " ^ X.to_string a ^ " " ^ Y.to_string b ^ ")"
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

    fun to_string (True) = "True" |
        to_string (Constr c) = C.to_string c |
        to_string (And (a, b)) = "(and " ^ to_string a ^ " " ^ to_string b ^ ")"
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
    fun to_string (True) = "True" | 
        to_string (And (l, r)) = "(" ^ to_string l ^ " && " ^ to_string r ^ " )" |
        to_string (And (l, r)) = "(" ^ to_string l ^ " || " ^ to_string r ^ " )" |
        to_string (Constr c) = X.to_string c 
end


functor ActionToString(
    X : TO_STRING
): TO_STRING =
struct
    type t = X.t Syntax.action
    open Syntax
    fun to_string (Internal x) = "(Internal " ^ X.to_string x ^ ")" |
        to_string (Out x) = "(Out " ^ X.to_string x ^ ")" |
        to_string (In x) = "(In " ^ X.to_string x ^ ")"
end

functor UpdateToString(
    X : TO_STRING
) : TO_STRING =
struct
    type t = X.t Syntax.update
    open Syntax
    fun to_string (Reset (x, i)) = "(Reset " ^ X.to_string x ^ " " ^ Int.toString i ^ ")" |
        to_string (Copy (x, y)) = "(Copy " ^ X.to_string x ^ " " ^ X.to_string y ^ ")" |
        to_string (Shift (x, i)) = "(Shift " ^ X.to_string x ^ " " ^ Int.toString i ^ ")" |
        to_string (Update (x, y, i)) = "(Update " ^ X.to_string x ^ " " ^ X.to_string y ^ " " ^ Int.toString i ^ ")"
end

structure NodeToString : TO_STRING =
struct
    type t = ParseBexpTypes.node
    structure I = InvariantToString(
        structure X = StringToString
        structure Y = IntToString
    )

    fun to_string {id, name, invariant} = 
    let 
        val id_string = "(id: " ^ IntToString.to_string id ^ ")"
        val name_string = "(name: " ^ name ^ ")"
        val invariant_string = "(invariant: " ^ I.to_string invariant ^ ")"
    in "(" ^ id_string ^ " " ^ name_string ^ " " ^ invariant_string ^ ")"
    end
end

structure EdgeToString : TO_STRING =
struct
    structure G = GuardToString(
        ConstraintToString(
            structure X = DifferenceToString(StringToString)
            structure Y = IntToString
        )
    )

    structure U = UpdateToString(StringToString)

    structure US = ListToString(
        structure Ty = U
        val sep = ", "
    )

    structure L = ActionToString(StringToString)

    type t = ParseBexpTypes.edge

    fun to_string{source, target, guard, label, update} =
    let 
        val source_string = "(Source: " ^ Int.toString source ^ ")"
        val target_string = "(Target: " ^ Int.toString target ^ ")"
        val guard_string = "(Guard: " ^ G.to_string guard ^ ")"
        val label_string = "(Label: " ^ L.to_string label  ^ ")"
        val update_string = "(Updates: " ^ US.to_string update ^ ")"
    in
        "(" ^ source_string ^ " " ^ target_string ^ " " ^ guard_string ^ " " ^ label_string ^ " " ^ update_string ^ ")"
    end
end

structure AutomatonToString : TO_STRING =
struct
    type t = ParseBexpTypes.automaton
    
    structure NS = ListToString(
        structure Ty = NodeToString
        val sep = ", "
    )

    structure ES = ListToString(
        structure Ty = EdgeToString
        val sep = ", "
    )

    structure IS = ListToString(
        structure Ty = IntToString
        val sep = ", "
    )

    fun to_string {nodes, edges, initial, committed, urgent} =
    let 
        val node_string = "(Nodes: " ^ NS.to_string nodes ^ ")"
        val edge_string = "(Edges: " ^ ES.to_string edges ^ ")"
        val init_string = "(Init: " ^ Int.toString initial ^ ")"
        val committed_string = "(Committed: " ^ IS.to_string committed ^ ")"
        val urgent_string = "(Committed: " ^ IS.to_string urgent ^ ")"
    in
        "(Automaton: " ^ node_string ^ " " ^ committed_string ^ " " ^ urgent_string ^ " " ^ init_string ^ " " ^ edge_string ^ ")"
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
        to_string (Not f) = "(not " ^ to_string f  ^ ")" |
        to_string (And (f, g)) = "(" ^ to_string f ^ " && " ^ to_string g ^ ")" |
        to_string (Or (f, g)) = "(" ^ to_string f ^ " || " ^ to_string g ^ ")" |
        to_string (Impl (f, g)) = "(" ^ to_string f ^ " -> " ^ to_string g ^ ")" |
        to_string (Loc (a, b)) = "Loc." ^ X.to_string a ^ "." ^ X.to_string b |
        to_string (Pred c) = C.to_string c
end

functor FormulaFToString(X : TO_STRING) : TO_STRING =
struct
    type t = X.t Syntax.Formula.F
    open Syntax
    open Formula
    fun to_string (Ex a) = "Ex " ^ X.to_string a |
        to_string (Eg a) = "Eg " ^ X.to_string a |
        to_string (Ax a) = "Ax " ^ X.to_string a |
        to_string (Ag a) = "Ag " ^ X.to_string a |
        to_string (Leadsto (a, b)) = "Leadsto " ^ X.to_string a ^ " " ^ X.to_string b
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

    structure A : TO_STRING =
    struct
        type t = (string * ParseBexpTypes.automaton)
        fun to_string (name, auto) =
            "(Name: " ^ name ^ " " ^ AutomatonToString.to_string auto ^ ")"
    end
    structure AS = ListToString(
        structure Ty = A
        val sep = ", "
    )
    
    structure F = FormulaToString(
        structure X = StringToString
        structure Y = IntToString
    )

    structure VS = ListToString(
        structure Ty = VarToString
        val sep = ", "
    )

    structure CS = ListToString(
        structure Ty = StringToString
        val sep = ", "
    )

    structure BS = ListToString(
        structure Ty = StringToString
        val sep = ", "
    )

    fun to_string {automata, clocks, vars, formula, broadcast_channels} =
    let
        val automata_string = "(Automata: " ^ AS.to_string automata ^ ")"
        val clock_string = "(Clocks: " ^ CS.to_string clocks ^ ")"
        val var_string = "(Vars: " ^ VS.to_string vars ^ ")"
        val formula_string = "(Formula: " ^ F.to_string formula ^ ")"
        val broadcast_string = "(Broadcast: "  ^ BS.to_string broadcast_channels ^ ")"
    in
        "(\n" ^
        automata_string ^ "\n" ^
        clock_string ^ "\n" ^
        var_string ^ "\n" ^
        formula_string ^ "\n" ^
        broadcast_string ^ "\n)"
    end

end