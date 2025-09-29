
structure CertificateConversionTypes = struct
    type nat = Model_Checker.nat
    type inta = Model_Checker.inta
    type 'a act = 'a Model_Checker.act

    type isa_renaming = (string -> nat) * 
        (string -> nat) * 
        (nat -> nat -> nat) * 
        (nat -> string) * 
        (nat -> string) * 
        (nat -> nat -> nat)

    type isa_dbm_entry = inta Model_Checker.dBMEntry

    type isa_state_space = inta Model_Checker.state_space

    type isa_cert = isa_renaming * isa_state_space

    type 'a ml_renaming = 'a Network.system

    type ml_state_space = (Location.key, LnDBMInt.zone) PolyPassedSet.hash_table

    type 'a ml_cert = 'a ml_renaming * ml_state_space
end