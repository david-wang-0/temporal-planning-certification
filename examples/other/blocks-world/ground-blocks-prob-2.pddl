(define (problem groundproblem) (:domain ground)
(:init
 (on-table_a)
 (on-table_b)
 (clear_a)
 (clear_b)
 (arm-empty)
)
(:goal
(and
 (on_a_b)
 (on_b_a)
)
)
)
