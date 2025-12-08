signature CERTIFICATE_CONVERSION_TYPES = 
sig
    type nat = Converter.nat
    type inta = Converter.inta
    type 'a act = 'a Converter.act

    type isa_renaming = 
        (string -> nat) *
            ((string -> nat) *
                ((nat -> nat -> nat) *
                    ((nat -> string) *
                        ((nat -> string) *
                            (nat -> nat -> nat)))))

    type isa_dbm_entry = inta Converter.dBMEntry

    type isa_state_space = inta Converter.state_space

    type isa_cert = isa_renaming * isa_state_space

    type ml_renaming

    type ml_state_space

    type ml_cert = ml_renaming * ml_state_space

end