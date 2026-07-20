theory Unsolvability_Code_Compile
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