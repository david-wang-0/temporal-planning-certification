theory Error_List_Monad_Add
  imports "TA_Library.Error_List_Monad"
          Temporal_Planning_Base.Base
begin

(* Could be done with a filter followed by a map *)
definition "collect f xs \<equiv> xs |> map f |> option_list_to_list"


fun get_or_err::"string \<Rightarrow> ('x \<Rightarrow> 'y option) \<Rightarrow> 'x \<Rightarrow> 'y Error_List_Monad.result" where
"get_or_err msg f x = (case f x of 
  None \<Rightarrow> Error [msg  |> String.implode]
| Some y \<Rightarrow> Result y)"

end