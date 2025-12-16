(define (problem groundproblem) (:domain ground)
(:init
 (at_apn1_apt2)
 (at_tru1_pos1)
 (at_obj1_pos1)
 (at_tru2_pos2)
)
(:goal
(and
 (at_obj1_pos2)
 (at_obj1_apt1)
)
)
)
