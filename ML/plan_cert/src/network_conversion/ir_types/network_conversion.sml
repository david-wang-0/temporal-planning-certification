structure NetworkConversionTypes = struct
    type nat = Converter.nat
    type inta = Converter.inta
    type 'a act = 'a Converter.act
    type int = int


    type isa_edge = 
        (nat * 
            ((string, inta) Converter.bexp * 
                ((string, inta) Converter.acconstraint list * 
                    (string act * 
                        ((string * (string, inta) Converter.exp) list * 
                            (string list * 
                            nat))))))

    type isa_automaton = 
        (nat list * 
            (nat list * 
                (isa_edge list * 
                (nat * (string, inta) Converter.acconstraint list) list)))

    type isa_state_exp =
        (nat, nat, string, inta) Converter.sexp

    type isa_formula = 
        (nat, nat, string, inta) Converter.formulaa

    type isa_network = 
        (nat -> nat -> string) *
            ((string -> nat) *
                (string list *
                    (isa_automaton list *
                        ((string * (inta * inta)) list * 
                            (isa_formula * 
                                (nat list * 
                                (string * inta) list))))))
    
    (* (ids_to_names, process_names_to_index,
     broadcast, automata, bounds, formula, init_locs, init_vars) 
     where
        - ids_to_names: auto id -> loc id -> loc name
        - process_names_to_index: auto name -> auto id
        
     *)
    
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