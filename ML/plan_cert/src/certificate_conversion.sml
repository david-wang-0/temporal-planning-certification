
fun convert_location (loc: Location) : (inta list * inta list) =
    loc
    |> Location.key 
    |> (fn (xs, ys) => (map Int_of_integer xs, map Int_of_integer ys))

fun convert_int_rep (rep: INT_REP.t): isa_dbm_entry =
    (case rep of 
        INT_REP.LT x => Model_Checker.Lt (Int_of_integer x) |
        INT_REP.LE x => Model_Checker.Le (Int_of_integer x) |
        INT_REP.Inf  => Model_Checker.INF
    )

fun convert_zone (zone: DBM) : inta Model_Checker.dBMEntry list list =
    zone
    |> DBM.to_int_rep_list
    |> map (map convert_int_rep)

fun convert_passed (passed: (Location, DBM) POLY_PASSED_SET.hash_table) : isa_state_space =
    let 
        fun f = (fn (loc, zones, acc) =>
            let val l = convert_location loc
                val states = map (fn z => (l, convert_zone z))
            in states@acc
            end
        )
    in POLY_PASSED_SET.fold f [] passed

(* (info, prop) :: (Network.info) * PWList 

info is obtained from something else
Network.info contains the renaming as JSON
This is obtained from a dictionary

PWList is the set of passed states

{certificate: {clocks: int,
                             passed: (int array * int array,
                                      E.t LnLayoutMatrix.matrix) PolyPassedSet.hash_table,
                             processes: int,
                             renaming: JsonP.json,
                             vars: int} option,
               result: {checking_time: Time.time,
                        explored_states: int,
                        sat: unit Property.result}}
*)

(* loc_dict: int IndexDict.t IndexDict.t
    clock_dict: string IndexDict.t
    var_dict: string IndexDict.t
    ta_names: string IndexDict.t
*)

fun convert_renaming ({clock_dict, var_dict, loc_dict, ta_names, ...}
                   : 'a ml_renaming) : isa_renaming =
    let 
        val var_renaming = IndexDict.to_function var_dict
        val clock_renaming = IndexDict.to_function clock_dict
        val location_renaming = IndexDict.to_function o (IndexDict.to_function loc_dict)

        val inv_var_renaming = IndexDict.inv_function var_dict
        val inv_clock_renaming = IndexDict.inv_function clock_dict
        val inv_location_renaming = IndexDict.to_function o (IndexDict.inv_function loc_dict)
    in (var_renaming, clock_renaming, location_renaming,
        inv_var_renaming, inv_clock_renaming, inv_location_renaming)
    end

(* 
    (var_renaming, 
    clock_renaming, 
    location_renaming,
    inv_renum_vars, 
    inv_renum_clocks, 
    inv_renum_states)

type isa_renaming = (string -> nat) * 
    (string -> nat) * 
    (nat -> nat -> nat) * 
    (nat -> string) * 
    (nat -> string) * 
    (nat -> nat -> nat) 
*)

fun convert_cert (cert: 'a ml_cert) : isa_cert =
    let
        val renaming = convert_renaming cert
        val state_space = convert_passed passed
    in (renaming, state_space)
