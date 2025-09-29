structure NetworkConversionTypes = struct
    type nat = Model_Checker.nat
    type inta = Model_Checker.inta
    type 'a act = 'a Model_Checker.act
    type int = int


    type isa_edge = 
        nat * 
        (string, inta) Model_Checker.bexp * 
        (string, inta) Model_Checker.acconstraint list * 
        string act * 
        (string * (string, inta) Model_Checker.exp) list * 
        string list * 
        nat

    type isa_automaton = 
        nat list * 
        nat list * 
        isa_edge list * 
        (nat * (string, inta) Model_Checker.acconstraint list) list

    type isa_state_exp =
        (nat, nat, string, inta) Model_Checker.sexp

    type isa_formula = 
        (nat, nat, string, inta) Model_Checker.formula

    type isa_network = 
        (nat -> nat -> string) *
        (string -> nat) *
        string list *
        isa_automaton list *
        (string * inta * inta) list * 
        isa_formula * 
        nat list * 
        (string * inta) list
    
    (* (ids_to_names, process_names_to_index,
     broadcast, automata, bounds, formula, init_locs, init_vars) *)
    
    (* names, network *)
    type named_isa_network =
        string list *
        isa_network

    (* clocks, network *)
    type clocks_name_network =
        string list *
        named_isa_network

    type ml_network = ParseBexpTypes.network
end