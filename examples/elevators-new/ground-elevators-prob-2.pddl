(define (problem groundproblem) (:domain ground)
(:init
 (elevator-on-floor_e0_f1)
 (stopped_e0)
 (person-on-floor_p0_f0)
)
(:goal
(and
 (person-on-floor_p0_f1)
 (person-on-floor_p0_f0)
)
)
)
