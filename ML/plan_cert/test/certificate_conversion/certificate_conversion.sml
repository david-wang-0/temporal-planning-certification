
functor CertificateConversionTest(Setup : CHECKING_SETUP) : TESTSUITE = struct

    open SMLUnit

    structure CertConv = CertificateConversion(Setup)
    structure Dbm = CertConv.Dbm
    structure Entry = Dbm.Entry

    fun from_int_list ls =
        ls
        |> List.map (List.map (fn x => IntRep.LT x))
        |> Dbm.from_int_rep_list

    exception Overflow of string

    fun to_int_list d =
        d
        |> Dbm.to_int_rep_list
        |> List.map (List.map (fn e => (case e of IntRep.LT x => x | IntRep.LTE x => x | IntRep.Inf => case (Int.maxInt) of SOME x => x | NONE => raise Overflow "No infinity representable as int")))

    fun test eq_f name f input expected =
        let
                val is = f input
        in
            name >+ assert_cmp_res
                eq_f is expected (Dbm.to_string is) (Dbm.to_string expected)
        end

    val eqtest_dbm = test Dbm.equal

    fun test_dbm_to_from_list_inv (num, xs) = 
        eqtest_dbm ("test_dbm_to_from_list_inv_" ^ num) (id) (from_int_list (to_int_list (from_int_list xs))) (from_int_list xs) 

    val test_dbms_to_from_list_inv =
        let 
            val test1 = ("1", [
                        [2,1,0],
                        [0, ~1,~2],
                        [0,~1,~2]
                    ])
            val tests = [test1]
        in map test_dbm_to_from_list_inv tests
        end
    
    (* fun test_eq eq_f f str_f input expected =
        let
            val is = f input
        in
            name >+ assert_cmp_res
                eq_f is expected (str_f is) (str_f expected)
        end


    fun eqtest_list = test_eq (fn (xs, ys) => xs = ys) (id) (List.to_string) 

    fun test_convert_zone (num, xs, ys) =
        let 

        in 

        end

    val test_convert_zones =
        let 
            val test1 = (
                "1", 
                [
                    [
                        [ (LT 3),  (LT 2), (LT 1)],
                        [Inf,  (LT 20),  (LT (~1))],
                        [Inf,  (LT 0),  (LT 13)]
                    ]
                ],
                [
                    [Converter.Lt 3, Converter.Lt 2, Converter.Lt 1],
                    [Converter.INF, Converter.Lt 20, Converter.Lt (~1)],
                    [Converter.INF, Converter.Lt 0, Converter.Lt 13]
                ]
                )
            val tests = [test1]
        in map test_convert_zone tests
        end *)

    fun tests name =
        (name >++
        test_dbms_to_from_list_inv)

    fun check name =
        run_test (tests name)
end

functor SetupCertConvFn(E : DBM_ENTRY) : CHECKING_SETUP = struct
    structure D = MakeLinDBM(E)
    structure Passed = PolyToMonoPassed(
        structure Zone = D
        structure Key = Location
        )
        
end

structure CertificateConversionTest = CertificateConversionTest(SetupCertConvFn(Entry))
structure CertificateConversionTest8 = CertificateConversionTest(SetupCertConvFn(Entry8Bit))
structure CertificateConversionTest32 = CertificateConversionTest(SetupCertConvFn(Entry32Bit))
structure CertificateConversionTest64 = CertificateConversionTest(SetupCertConvFn(Entry64Bit))