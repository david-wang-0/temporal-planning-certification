(define (problem groundproblem) (:domain ground)
(:init
 (robot_at_r0_p4)
 (robot_free_r0)
 (battery_level_r0_four)
 (pallet_at_b0_p4)
 (pallet_at_b1_p4)
 (position_free_p4)
)
(:goal
(and
 (treated_b0_t0)
 (treated_b1_t0)
)
)
)
