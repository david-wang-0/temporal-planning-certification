theory StateSeq
  imports Main
begin

context 
  fixes s_rel::"'s \<Rightarrow> 's \<Rightarrow> bool"
    and t_rel::"'t \<Rightarrow> 't \<Rightarrow> bool"
    and abs::"'s \<Rightarrow> 't"
  assumes "s_rel s s' \<Longrightarrow> t_rel (abs s) (abs s')"
begin
  
end
end