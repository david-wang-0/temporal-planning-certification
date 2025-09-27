structure CertificateConversionTypes = struct

(* (var_renaming, 
    clock_renaming, 
    location_renaming,
    inv_renum_vars, 
    inv_renum_clocks, 
    inv_renum_states)
*)
type isa_renaming = (string -> nat) * 
    (string -> nat) * 
    (nat -> nat -> nat) * 
    (nat -> string) * 
    (nat -> string) * 
    (nat -> nat -> nat)

type isa_dbm_entry = inta Model_Checker.dBMEntry

type isa_state_space = inta Model_Checker.state_space

type isa_cert = isa_renaming * isa_state_space

(* To do: This needs some imports from MLunta. Maybe refactor for cleanliness. *)
type net_info = Network.info 

type 'a ml_renaming = 'a Network.system

type ml_state_space = (Location, DBM) POLY_PASSED_SET.hash_table

type 'a ml_cert = 'a ml_renaming * ml_state_space


end