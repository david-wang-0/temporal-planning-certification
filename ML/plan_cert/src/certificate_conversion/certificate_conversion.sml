signature CERTIFICATE_CONVERSION =
sig
    include CERTIFICATE_CONVERSION_TYPES
    val convert_certificate: ml_cert -> isa_cert
    val convert_renaming: ml_renaming -> isa_renaming

    structure Dbm : DBM
end

functor CertificateConversion (Setup : CHECKING_SETUP) : CERTIFICATE_CONVERSION =
struct
    
    structure Dbm = Setup.D
    structure Entry = Dbm.Entry
    structure Basic = BasicSetup(Dbm)
    structure Passed = Setup.Passed

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

    type ml_renaming = Dbm.t Network.system

    type ml_state_space = Passed.passed_set

    type ml_cert = ml_renaming * ml_state_space

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

    fun convert_zone (zone: Dbm.zone) : inta Converter.dBMEntry list list =
        let 
            val int_rep_list = Dbm.to_int_rep_list zone;
        in 
            List.map (List.map convert_int_rep) int_rep_list
        end

    fun convert_passed (passed: Passed.passed_set) : isa_state_space =
        let 
            val f = (fn (loc, zones, acc) =>
                let val l = convert_location loc
                    val states = List.map (fn z => (l, convert_zone z)) zones
                in states@acc
                end
            )
        in Passed.fold f [] passed
          |> Converter.Reachable_Set
        end

    (* debug aid: name the failing lookup family + key before re-raising (the lookups are
       called back lazily from INSIDE the verified checker, so a bare ValueNotFound is
       otherwise untraceable) *)
    fun dbg_s fam f (x : string) =
        f x handle IndexDict.ValueNotFound _ =>
          (print ("+ renaming MISS (" ^ fam ^ "): " ^ x ^ "\n");
           raise IndexDict.ValueNotFound fam)

    fun convert_renaming ({clock_dict, var_dict, loc_dict, ta_names, ...}
                    : ml_renaming) : isa_renaming =
        let
            val var_renaming = dbg_s "var" (IndexDict.inv_function var_dict) #> Converter.nat_of_integer
            val inv_var_renaming = Converter.integer_of_nat #> IndexDict.to_function var_dict

            (* Munta's verified conversion appends its synthetic urgency clock _urge AFTER all
               model clocks (make_renaming: clk_set @ [_urge], all Suc-shifted past the zero
               clock).  mlunta's clock_dict holds the zero clock at 0 and the model clocks at
               1..n, so _urge belongs at the next free index n+1 = size of the dict. *)
            val n_clocks = IndexDict.size clock_dict
            val clock_renaming =
                (fn s => if s = "_urge" then n_clocks
                         else dbg_s "clock" (IndexDict.inv_function clock_dict) s)
                #> Converter.nat_of_integer
            val inv_clock_renaming =
                Converter.integer_of_nat
                #> (fn i => if i = n_clocks then "_urge" else IndexDict.to_function clock_dict i)

            val loc_dict' = Converter.integer_of_nat #> IndexDict.to_function loc_dict
            (* Munta's make_renaming makes each process's location renaming TOTAL over the
               UNION of all processes' locations (its loc_set_diff extension), and its
               renaming check queries foreign ids too.  mlunta's per-process dict covers only
               the process's own node ids (as identity maps in our emission), so totalize
               with an identity fallback -- injective, and index-consistent with the cert. *)
            val location_renaming =
                (fn p =>
                  let val f = loc_dict' p
                  in Converter.integer_of_nat
                     #> (fn l => IndexDict.inv_function f l
                           handle IndexDict.ValueNotFound _ => l)
                     #> Converter.nat_of_integer
                  end)
            val inv_location_renaming = loc_dict'
                #> (fn f => (Converter.integer_of_nat #> IndexDict.to_function f #> Converter.nat_of_integer))


        in (var_renaming, (clock_renaming, (location_renaming,
            (inv_var_renaming, (inv_clock_renaming, inv_location_renaming)))))
        end

    fun convert_certificate ((renaming, passed): ml_cert) : isa_cert =
        let
            val renaming = convert_renaming renaming
            val state_space = convert_passed passed
        in (renaming, state_space)
        end
end