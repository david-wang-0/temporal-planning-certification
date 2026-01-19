(define (domain ground)
(:requirements :strips)
(:predicates
 (started_i0_last_t)
 (ready_i0_t0)
 (started_i1_last_t)
 (ready_i1_t0)
 (started_i2_last_t)
 (ready_i2_t0)
 (started_i3_last_t)
 (ready_i3_t0)
 (not_started_i0_t0)
 (not_treated_i0_t0)
 (not_started_i1_t0)
 (not_treated_i1_t0)
 (not_started_i2_t0)
 (not_treated_i2_t0)
 (not_started_i3_t0)
 (not_treated_i3_t0)
 (next_to_treat_t0_i0)
 (joined)
 (next_to_treat_last_t_i0)
 (not_started_i0_last_t)
 (not_treated_i0_last_t)
 (not_started_i1_last_t)
 (not_treated_i1_last_t)
 (not_started_i2_last_t)
 (not_treated_i2_last_t)
 (not_started_i3_last_t)
 (not_treated_i3_last_t)
 (s2_i0_t0_last_t)
 (treated_i0_t0)
 (not_busy)
 (next_to_treat_t0_i1)
 (busy)
 (started_i0_t0)
 (s2_i1_t0_last_t)
 (treated_i1_t0)
 (next_to_treat_t0_i2)
 (started_i1_t0)
 (s2_i2_t0_last_t)
 (treated_i2_t0)
 (next_to_treat_t0_i3)
 (started_i2_t0)
 (s3_i0_t0_last_t)
 (ready_i0_last_t)
 (s3_i1_t0_last_t)
 (ready_i1_last_t)
 (s3_i2_t0_last_t)
 (ready_i2_last_t)
 (s4_i0_t0_last_t)
 (s4_i1_t0_last_t)
 (s4_i2_t0_last_t)
 (s1_i0_t0_last_t)
 (s1_i1_t0_last_t)
 (s1_i2_t0_last_t)
)

(:action _join_i1_i0_t0_
 :parameters ()
 :precondition
  (and
   (not_treated_i1_t0)
   (not_treated_i0_t0)
   (started_i1_t0)
   (started_i0_t0)
   (ready_i1_t0)
   (ready_i0_t0)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i2_i0_t0_
 :parameters ()
 :precondition
  (and
   (not_treated_i2_t0)
   (not_treated_i0_t0)
   (started_i2_t0)
   (started_i0_t0)
   (ready_i2_t0)
   (ready_i0_t0)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i0_i1_t0_
 :parameters ()
 :precondition
  (and
   (not_treated_i0_t0)
   (not_treated_i1_t0)
   (started_i0_t0)
   (started_i1_t0)
   (ready_i0_t0)
   (ready_i1_t0)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i2_i1_t0_
 :parameters ()
 :precondition
  (and
   (not_treated_i2_t0)
   (not_treated_i1_t0)
   (started_i2_t0)
   (started_i1_t0)
   (ready_i2_t0)
   (ready_i1_t0)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i0_i2_t0_
 :parameters ()
 :precondition
  (and
   (not_treated_i0_t0)
   (not_treated_i2_t0)
   (started_i0_t0)
   (started_i2_t0)
   (ready_i0_t0)
   (ready_i2_t0)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i1_i2_t0_
 :parameters ()
 :precondition
  (and
   (not_treated_i1_t0)
   (not_treated_i2_t0)
   (started_i1_t0)
   (started_i2_t0)
   (ready_i1_t0)
   (ready_i2_t0)
  )
 :effect (and
  (joined)
 )
)
(:action _reset_i0_
 :parameters ()
 :precondition ()
 :effect (and
  (not (started_i0_last_t))
  (not (started_i1_last_t))
  (not (started_i2_last_t))
  (not (started_i3_last_t))
  (not (treated_i0_t0))
  (not (started_i0_t0))
  (not (treated_i1_t0))
  (not (started_i1_t0))
  (not (treated_i2_t0))
  (not (started_i2_t0))
  (not_started_i0_t0)
  (not_treated_i0_t0)
  (not_started_i1_t0)
  (not_treated_i1_t0)
  (not_started_i2_t0)
  (not_treated_i2_t0)
  (not_started_i3_t0)
  (not_treated_i3_t0)
  (next_to_treat_t0_i0)
  (next_to_treat_last_t_i0)
  (not_started_i0_last_t)
  (not_treated_i0_last_t)
  (not_started_i1_last_t)
  (not_treated_i1_last_t)
  (not_started_i2_last_t)
  (not_treated_i2_last_t)
  (not_started_i3_last_t)
  (not_treated_i3_last_t)
 )
)
(:durative-action _make_treatment1_i0_i1_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i0_t0_last_t))
   (at start (next_to_treat_t0_i0))
   (at start (not_busy))
   (at start (not_treated_i0_t0))
   (at start (not_started_i0_t0))
   (at start (ready_i0_t0))
  )
 :effect (and
  (at start (not (not_started_i0_t0)))
  (at start (not (next_to_treat_t0_i0)))
  (at start (not (not_busy)))
  (at start (not (s1_i0_t0_last_t)))
  (at start (next_to_treat_t0_i1))
  (at start (busy))
  (at start (started_i0_t0))
  (at end (not (not_treated_i0_t0)))
  (at end (not (busy)))
  (at end (s2_i0_t0_last_t))
  (at end (treated_i0_t0))
  (at end (not_busy))
 )
)
(:durative-action _make_treatment1_i1_i2_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i1_t0_last_t))
   (at start (next_to_treat_t0_i1))
   (at start (not_busy))
   (at start (not_treated_i1_t0))
   (at start (not_started_i1_t0))
   (at start (ready_i1_t0))
  )
 :effect (and
  (at start (not (not_started_i1_t0)))
  (at start (not (not_busy)))
  (at start (not (next_to_treat_t0_i1)))
  (at start (not (s1_i1_t0_last_t)))
  (at start (busy))
  (at start (next_to_treat_t0_i2))
  (at start (started_i1_t0))
  (at end (not (not_treated_i1_t0)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i1_t0_last_t))
  (at end (treated_i1_t0))
 )
)
(:durative-action _make_treatment1_i2_i3_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i2_t0_last_t))
   (at start (next_to_treat_t0_i2))
   (at start (not_busy))
   (at start (not_treated_i2_t0))
   (at start (not_started_i2_t0))
   (at start (ready_i2_t0))
  )
 :effect (and
  (at start (not (not_started_i2_t0)))
  (at start (not (not_busy)))
  (at start (not (next_to_treat_t0_i2)))
  (at start (not (s1_i2_t0_last_t)))
  (at start (busy))
  (at start (next_to_treat_t0_i3))
  (at start (started_i2_t0))
  (at end (not (not_treated_i2_t0)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i2_t0_last_t))
  (at end (treated_i2_t0))
 )
)
(:durative-action _make_treatment2_i0_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i0_t0_last_t))
 :effect (and
  (at start (not (s2_i0_t0_last_t)))
  (at end (s3_i0_t0_last_t))
  (at end (ready_i0_last_t))
 )
)
(:durative-action _make_treatment2_i1_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i1_t0_last_t))
 :effect (and
  (at start (not (s2_i1_t0_last_t)))
  (at end (s3_i1_t0_last_t))
  (at end (ready_i1_last_t))
 )
)
(:durative-action _make_treatment2_i2_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i2_t0_last_t))
 :effect (and
  (at start (not (s2_i2_t0_last_t)))
  (at end (s3_i2_t0_last_t))
  (at end (ready_i2_last_t))
 )
)
(:durative-action _make_treatment3_i0_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i0_t0_last_t))
   (at end (started_i0_last_t))
  )
 :effect (and
  (at start (not (s3_i0_t0_last_t)))
  (at end (s4_i0_t0_last_t))
 )
)
(:durative-action _make_treatment3_i1_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i1_t0_last_t))
   (at end (started_i1_last_t))
  )
 :effect (and
  (at start (not (s3_i1_t0_last_t)))
  (at end (s4_i1_t0_last_t))
 )
)
(:durative-action _make_treatment3_i2_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i2_t0_last_t))
   (at end (started_i2_last_t))
  )
 :effect (and
  (at start (not (s3_i2_t0_last_t)))
  (at end (s4_i2_t0_last_t))
 )
)
(:durative-action _make_treatment_container_i0_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i0_t0_last_t))
 :effect (and
  (at start (s1_i0_t0_last_t))
  (at end (not (s4_i0_t0_last_t)))
 )
)
(:durative-action _make_treatment_container_i1_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i1_t0_last_t))
 :effect (and
  (at start (s1_i1_t0_last_t))
  (at end (not (s4_i1_t0_last_t)))
 )
)
(:durative-action _make_treatment_container_i2_t0_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i2_t0_last_t))
 :effect (and
  (at start (s1_i2_t0_last_t))
  (at end (not (s4_i2_t0_last_t)))
 )
)
)
