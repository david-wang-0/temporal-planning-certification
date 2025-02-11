theory Error_List_Monad_Add
  imports "TA_Library.Error_List_Monad"
          Temporal_Planning_Base.Base
begin

(* Could be done with a filter followed by a map *)
definition "collect f xs \<equiv> xs |> map f |> option_list_to_list"



end