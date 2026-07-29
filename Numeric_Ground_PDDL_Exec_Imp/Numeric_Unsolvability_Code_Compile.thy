theory Numeric_Unsolvability_Code_Compile
  imports Numeric_Unsolvability_Export
begin

text \<open>Post-process the unified \<open>Converter\<close> export (propositional + numeric) exactly as the old
  propositional \<open>Unsolvability_Code_Compile\<close> did: replace the arbitrary-precision \<open>IntInf\<close> with the
  native \<open>Int\<close> (int64 MLton build), splice in the \<open>list_of_set\<close> destructor, and move the emitted
  \<open>Check_Unsolvability.ML\<close> into \<open>ML/\<close> where the \<open>converter.mlb\<close> build picks it up.  This SUPERSEDES
  the propositional-only export in \<open>PDDL_TP_Reduction\<close>; the ROOT \<open>export_files\<close> now copies this
  session's store export.\<close>

compile_generated_files "code/Check_Unsolvability.ML" (in Numeric_Unsolvability_Export)
export_files \<open>ML/Check_Unsolvability.ML\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute dir

      val _ =
          exec \<open>Replace int type\<close>
            "sed -i -e 's/IntInf/Int/g' code/Check_Unsolvability.ML"

      \<comment> \<open>Delete the dead \<open>Bit_Shifts\<close> structure: the numeric code pulls in this arbitrary-precision
         bit-splitting helper (push_bit/drop_bit via pow/divMod/shifts under an IntInf preamble),
         but nothing calls its push/drop.  The IntInf-to-Int retype above leaves its body
         referencing operations Int lacks, so the whole (unused) structure fails to compile under
         MLton -- excise it wholesale.\<close>
      val _ =
          exec \<open>Delete dead Bit_Shifts structure\<close>
            "sed -i -e '/^structure Bit_Shifts : sig/,/^end;/d' code/Check_Unsolvability.ML"

      val _ =
          exec \<open>Replace list_of_set'\<close>
            "sed -i -e 's/listofsetreplacethiswhilecompiling/(fn (Set_Monad xs) => xs | DList_set (Abs_dlist xs) => xs | RBT_set (Mapping_RBTa r) => rbt_to_list r | _ => raise Fail \"Unsupported set implementation\")/g' code/Check_Unsolvability.ML"

      val _ =
          exec \<open>Create ML folder\<close>
            "mkdir -p ML"

      val _ =
          exec \<open>Move to ML folder\<close>
            "mv -t ML code/Check_Unsolvability.ML"

    in () end\<close>

end
