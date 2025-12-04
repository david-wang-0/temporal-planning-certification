theory Unsolvability_Code_Export
  imports Check_Unsolvability
begin

text \<open>Just replaces the int type.\<close>
compile_generated_files "code/Check_Unsolvability.ML" (in Check_Unsolvability)
export_files \<open>ML/Check_Unsolvability.ML\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute dir

      
      val _ =
          exec \<open>Replace int type\<close>
            "sed -i -e 's/IntInf/Int/g' code/Check_Unsolvability.ML" 

      val _ =
          exec \<open>Create ML folder\<close>
            "mkdir -p ML" 

      val _ =
          exec \<open>Move to ML folder\<close>
            "mv -t ML code/Check_Unsolvability.ML" 
        

      val _ = exec \<open>Copy and paste code\<close> ("cp ML/Check_Unsolvability.ML " ^ Path.implode (Path.append (File.absolute_path Path.current) (Path.explode "ML")))
    in () end\<close> 


end