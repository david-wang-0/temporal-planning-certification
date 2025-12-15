(define (problem groundproblem) (:domain ground)
(:init
 (clear_a)
 (clear_b)
 (ontable_a)
 (ontable_b)
 (handempty)
)
(:goal
(and
 (on_a_b)
 (on_b_a)
)
)
)
