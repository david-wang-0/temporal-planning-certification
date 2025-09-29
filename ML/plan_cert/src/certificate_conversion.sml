
structure CertificateConversion =
struct
    open CertificateConversionTypes

    fun convert_location (loc: Location.key) : (inta list * inta list) =
        loc
        |> (fn (xs, ys) => (ArrayUtils.to_list xs, ArrayUtils.to_list ys))
        |> (fn (xs, ys) => (List.map Model_Checker.Int_of_integer xs, List.map Model_Checker.Int_of_integer ys))

    fun convert_int_rep (rep: IntRep.t): isa_dbm_entry =
        (case rep of 
            IntRep.LT x => Model_Checker.Lt (Model_Checker.Int_of_integer x) |
            IntRep.LTE x => Model_Checker.Le (Model_Checker.Int_of_integer x) |
            IntRep.Inf  => Model_Checker.INF
        )

    fun convert_zone (zone: LnDBMInt.zone) : inta Model_Checker.dBMEntry list list =
        zone
        |> LnDBMInt.to_int_rep_list
        |> map (map convert_int_rep)

    fun convert_passed (passed: (Location.key, LnDBMInt.zone) PolyPassedSet.hash_table) : isa_state_space =
        let 
            val f = (fn (loc, zones, acc) =>
                let val l = convert_location loc
                    val states = map (fn z => (l, convert_zone z)) zones
                in states@acc
                end
            )
        in PolyPassedSet.fold f [] passed
          |> Model_Checker.Reachable_Set
        end

    fun convert_renaming ({clock_dict, var_dict, loc_dict, ta_names, ...}
                    : 'a ml_renaming) : isa_renaming =
        let 
            val var_renaming = IndexDict.to_function var_dict
            val clock_renaming = IndexDict.to_function clock_dict
            val location_renaming = (IndexDict.to_function loc_dict) #> IndexDict.to_function 

            val inv_var_renaming = IndexDict.inv_function var_dict
            val inv_clock_renaming = IndexDict.inv_function clock_dict
            val inv_location_renaming = I(IndexDict.to_function loc_dict) #> IndexDict.inv_function 
        in (var_renaming, clock_renaming, location_renaming,
            inv_var_renaming, inv_clock_renaming, inv_location_renaming)
        end

    fun convert_cert (cert: 'a ml_cert) : isa_cert =
        let
            val renaming = convert_renaming cert
            val state_space = convert_passed passed
        in (renaming, state_space)
        end
end