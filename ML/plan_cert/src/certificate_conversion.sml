signature CERTIFICATE_CONVERSION = 
sig 
    val convert_certificate: 'a CertificateConversionTypes.ml_cert -> CertificateConversionTypes.isa_cert
end

structure CertificateConversion : CERTIFICATE_CONVERSION =
struct
    open CertificateConversionTypes

    fun convert_location (loc: Location.key) : (inta list * inta list) =
        loc
        |> (fn (xs, ys) => (ArrayUtils.to_list xs, ArrayUtils.to_list ys))
        |> (fn (xs, ys) => (List.map Converter.Int_of_integer xs, List.map Converter.Int_of_integer ys))

    fun convert_int_rep (rep: IntRep.t): isa_dbm_entry =
        (case rep of 
            IntRep.LT x => Converter.Lt (Converter.Int_of_integer x) |
            IntRep.LTE x => Converter.Le (Converter.Int_of_integer x) |
            IntRep.Inf  => Converter.INF
        )

    fun convert_zone (zone: LnDBMInt.zone) : inta Converter.dBMEntry list list =
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
          |> Converter.Reachable_Set
        end

    fun convert_renaming ({clock_dict, var_dict, loc_dict, ta_names, ...}
                    : 'a ml_renaming) : isa_renaming =
        let 
            val var_renaming = IndexDict.inv_function var_dict #> Converter.nat_of_integer
            val inv_var_renaming = Converter.integer_of_nat #> IndexDict.to_function var_dict

            val clock_renaming = IndexDict.inv_function clock_dict #> Converter.nat_of_integer
            val inv_clock_renaming = Converter.integer_of_nat #> IndexDict.to_function clock_dict

            val loc_dict' = Converter.integer_of_nat #> IndexDict.to_function loc_dict
            val location_renaming = loc_dict'
                #> (fn f => (Converter.integer_of_nat #> IndexDict.inv_function f #> Converter.nat_of_integer))
            val inv_location_renaming = loc_dict'
                #> (fn f => (Converter.integer_of_nat #> IndexDict.to_function f #> Converter.nat_of_integer))


        in (var_renaming, (clock_renaming, (location_renaming,
            (inv_var_renaming, (inv_clock_renaming, inv_location_renaming)))))
        end

    fun convert_certificate ((renaming, passed): 'a ml_cert) : isa_cert =
        let
            val renaming = convert_renaming renaming
            val state_space = convert_passed passed
        in (renaming, state_space)
        end
end