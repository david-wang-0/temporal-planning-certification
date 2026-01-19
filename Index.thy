theory Index
  imports "PDDL_TP_Reduction.Check_Unsolvability"
begin

(* 
To do:
- Actions
- Problems
- Plans
- Uniqueness
  - Actions
  - Problems
  - Plans
- Replacement
  - Actions
  - Problems
  - Plans

- Box
  - Locale with definitions
  - Locale with plan
  - 
*)

text \<open>
\newcommand{\tpp}{\ensuremath \planningproblem}
\newcommand{\tp}{\ensuremath{\plan}}
\newcommand{\tppa}{\ensuremath{\tpp a}}
\newcommand{\tpa}{\ensuremath{\tp a}}
\newcommand{\tppl}{\ensuremath{\tpp l}}
\newcommand{\tpl}{\ensuremath{\tp l}}
\newcommand{\tppal}{\ensuremath{\tppa l}}
\newcommand{\tpal}{\ensuremath{\tpa l}}
\newcommand{\tppli}{\ensuremath{\tppl i}}
\newcommand{\tpli}{\ensuremath{\tpl i}}
\newcommand{\tppali}{\ensuremath{\tppal i}}
\newcommand{\tpali}{\ensuremath{\tpal i}}
\newcommand{\tpplin}{\ensuremath{\tppli N}}
\newcommand{\tplin}{\ensuremath{\tpli N}}
\newcommand{\tppalin}{\ensuremath{\tppali N}}
\newcommand{\tpalin}{\ensuremath{\tpali N}}
\newcommand{\tpc}{\ensuremath{C \tp}}

\newcommand{\pdpp}{\ensuremath{\tpp S}}
\newcommand{\pdp}{\ensuremath{\tp S}}
\newcommand{\gpdpp}{\ensuremath{\pdpp g}}
\newcommand{\gpdp}{\ensuremath{\pdp g}}
\newcommand{\gpdppdefs}{\ensuremath{\gpdpp D}}

\newcommand{\actt}{\ensuremath{A}}
\newcommand{\actta}{\ensuremath{\actt a}}

\newcommand{\timaut}{\ensuremath{\auto}}

\newcommand{\acttd}{\ensuremath{\actt d}}
\newcommand{\tppd}{\ensuremath{\tpp d}}
\newcommand{\tpd}{\ensuremath{\tp d}}

\newcommand{\actts}{\ensuremath{\actt S}}
\newcommand{\tpps}{\ensuremath{\tpp S}}
\newcommand{\tps}{\ensuremath{\tp S}}

\section{Locales}
\begin{table}[h]
\centering
\begin{tabular}{|l|r|}
\hline
Informal Locale Name & Locale \\
\hline
$\tpp$  & @{locale temp_planning_problem_set_impl} \\
$\tppa$   & @{locale temp_planning_problem_set_impl'} \\
$\tp$   & @{locale temp_plan_for_problem_impl} \\
$\tpa$  & @{locale temp_plan_for_problem_impl'} \\
\hline
$\tppli$  & @{locale temp_planning_problem_list_impl_int} \\
$\tppali$   & @{locale temp_planning_problem_list_impl_int'} \\
$\tpli$   & @{locale temp_plan_for_problem_list_impl_int} \\
$\tpali$  & @{locale temp_plan_for_problem_list_impl_int'} \\
\hline
$\tpplin$  & @{locale tp_nta_reduction_model_checking} \\
$\tppalin$   &  @{locale tp_nta_reduction_model_checking'}\\
$\tplin$   & @{locale tp_nta_reduction_correctness} \\
$\tpalin$  & @{locale tp_nta_reduction_correctness'} \\
\hline
$\timaut$  & @{locale Simple_Network_Impl} \\
$\gpdpp$   & @{locale ground_ast_problem} \\
$\gpdp$   &  @{locale valid_ground_plan}\\
$\gpdppdefs$  & @{locale ground_ast_problem} \\
$\pdpp$   &  @{locale ast_problem}\\
\hline
\end{tabular}
\caption{Informal Locales and Formal Locales}
\label{tab:locales}
\end{table}

\section{Lemmas and Theorems}
We have presented Theorem 1 and three lemmas needed to arrive at a proof.
Theorem 1 is @{thm tp_nta_reduction_correctness.valid_plan_imp_form_holds}.
Lemma 1 is @{thm tp_nta_reduction_correctness.plan_steps_possible}.
Lemma 2 is @{thm tp_nta_reduction_correctness.initial_step_possible}.
Lemma 3 is @{thm tp_nta_reduction_correctness.final_step_possible}.

Our main condition \( \mathit{encodes\_after(...)} \) is 
@{const tp_nta_reduction_correctness.happening_post}.
The condition on clocks corresponds to @{const tp_nta_reduction_correctness.act_clock_post_happ_spec}
and the condition on propositions corresponds to @{const tp_nta_reduction_correctness.prop_state_after_happ}.
\<close>

end