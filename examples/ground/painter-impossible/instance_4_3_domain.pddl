(define (domain ground)
(:requirements :strips)
(:predicates
 (started_i0_last_t)
 (ready_i0_t0)
 (started_i1_last_t)
 (ready_i1_t0)
 (started_i2_last_t)
 (ready_i2_t0)
 (not_started_i0_t0)
 (not_treated_i0_t0)
 (not_started_i0_t1)
 (not_treated_i0_t1)
 (not_started_i0_t2)
 (not_treated_i0_t2)
 (not_started_i0_t3)
 (not_treated_i0_t3)
 (not_started_i1_t0)
 (not_treated_i1_t0)
 (not_started_i1_t1)
 (not_treated_i1_t1)
 (not_started_i1_t2)
 (not_treated_i1_t2)
 (not_started_i1_t3)
 (not_treated_i1_t3)
 (not_started_i2_t0)
 (not_treated_i2_t0)
 (not_started_i2_t1)
 (not_treated_i2_t1)
 (not_started_i2_t2)
 (not_treated_i2_t2)
 (not_started_i2_t3)
 (not_treated_i2_t3)
 (next_to_treat_t0_i0)
 (next_to_treat_t1_i0)
 (next_to_treat_t2_i0)
 (next_to_treat_t3_i0)
 (joined)
 (next_to_treat_last_t_i0)
 (not_started_i0_last_t)
 (not_treated_i0_last_t)
 (not_started_i1_last_t)
 (not_treated_i1_last_t)
 (not_started_i2_last_t)
 (not_treated_i2_last_t)
 (s2_i0_t3_last_t)
 (treated_i0_t3)
 (not_busy)
 (next_to_treat_t3_i1)
 (busy)
 (started_i0_t3)
 (s2_i1_t3_last_t)
 (treated_i1_t3)
 (next_to_treat_t3_i2)
 (started_i1_t3)
 (s2_i0_t0_t1)
 (treated_i0_t0)
 (next_to_treat_t0_i1)
 (started_i0_t0)
 (s2_i1_t0_t1)
 (treated_i1_t0)
 (next_to_treat_t0_i2)
 (started_i1_t0)
 (s2_i0_t1_t2)
 (treated_i0_t1)
 (next_to_treat_t1_i1)
 (started_i0_t1)
 (s2_i1_t1_t2)
 (treated_i1_t1)
 (next_to_treat_t1_i2)
 (started_i1_t1)
 (s2_i0_t2_t3)
 (treated_i0_t2)
 (next_to_treat_t2_i1)
 (started_i0_t2)
 (s2_i1_t2_t3)
 (treated_i1_t2)
 (next_to_treat_t2_i2)
 (started_i1_t2)
 (s3_i0_t3_last_t)
 (ready_i0_last_t)
 (s3_i1_t3_last_t)
 (ready_i1_last_t)
 (s3_i0_t0_t1)
 (ready_i0_t1)
 (s3_i1_t0_t1)
 (ready_i1_t1)
 (s3_i0_t1_t2)
 (ready_i0_t2)
 (s3_i1_t1_t2)
 (ready_i1_t2)
 (s3_i0_t2_t3)
 (ready_i0_t3)
 (s3_i1_t2_t3)
 (ready_i1_t3)
 (s4_i0_t3_last_t)
 (s4_i1_t3_last_t)
 (s4_i0_t0_t1)
 (s4_i1_t0_t1)
 (s4_i0_t1_t2)
 (s4_i1_t1_t2)
 (s4_i0_t2_t3)
 (s4_i1_t2_t3)
 (s1_i0_t3_last_t)
 (s1_i1_t3_last_t)
 (s1_i0_t0_t1)
 (s1_i1_t0_t1)
 (s1_i0_t1_t2)
 (s1_i1_t1_t2)
 (s1_i0_t2_t3)
 (s1_i1_t2_t3)
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
(:action _join_i1_i0_t1_
 :parameters ()
 :precondition
  (and
   (not_treated_i1_t1)
   (not_treated_i0_t1)
   (started_i1_t1)
   (started_i0_t1)
   (ready_i1_t1)
   (ready_i0_t1)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i0_i1_t1_
 :parameters ()
 :precondition
  (and
   (not_treated_i0_t1)
   (not_treated_i1_t1)
   (started_i0_t1)
   (started_i1_t1)
   (ready_i0_t1)
   (ready_i1_t1)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i1_i0_t2_
 :parameters ()
 :precondition
  (and
   (not_treated_i1_t2)
   (not_treated_i0_t2)
   (started_i1_t2)
   (started_i0_t2)
   (ready_i1_t2)
   (ready_i0_t2)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i0_i1_t2_
 :parameters ()
 :precondition
  (and
   (not_treated_i0_t2)
   (not_treated_i1_t2)
   (started_i0_t2)
   (started_i1_t2)
   (ready_i0_t2)
   (ready_i1_t2)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i1_i0_t3_
 :parameters ()
 :precondition
  (and
   (not_treated_i1_t3)
   (not_treated_i0_t3)
   (started_i1_t3)
   (started_i0_t3)
   (ready_i1_t3)
   (ready_i0_t3)
  )
 :effect (and
  (joined)
 )
)
(:action _join_i0_i1_t3_
 :parameters ()
 :precondition
  (and
   (not_treated_i0_t3)
   (not_treated_i1_t3)
   (started_i0_t3)
   (started_i1_t3)
   (ready_i0_t3)
   (ready_i1_t3)
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
  (not (treated_i0_t3))
  (not (started_i0_t3))
  (not (treated_i1_t3))
  (not (started_i1_t3))
  (not (treated_i0_t0))
  (not (started_i0_t0))
  (not (treated_i1_t0))
  (not (started_i1_t0))
  (not (treated_i0_t1))
  (not (started_i0_t1))
  (not (treated_i1_t1))
  (not (started_i1_t1))
  (not (treated_i0_t2))
  (not (started_i0_t2))
  (not (treated_i1_t2))
  (not (started_i1_t2))
  (not_started_i0_t0)
  (not_treated_i0_t0)
  (not_started_i0_t1)
  (not_treated_i0_t1)
  (not_started_i0_t2)
  (not_treated_i0_t2)
  (not_started_i0_t3)
  (not_treated_i0_t3)
  (not_started_i1_t0)
  (not_treated_i1_t0)
  (not_started_i1_t1)
  (not_treated_i1_t1)
  (not_started_i1_t2)
  (not_treated_i1_t2)
  (not_started_i1_t3)
  (not_treated_i1_t3)
  (not_started_i2_t0)
  (not_treated_i2_t0)
  (not_started_i2_t1)
  (not_treated_i2_t1)
  (not_started_i2_t2)
  (not_treated_i2_t2)
  (not_started_i2_t3)
  (not_treated_i2_t3)
  (next_to_treat_t0_i0)
  (next_to_treat_t1_i0)
  (next_to_treat_t2_i0)
  (next_to_treat_t3_i0)
  (next_to_treat_last_t_i0)
  (not_started_i0_last_t)
  (not_treated_i0_last_t)
  (not_started_i1_last_t)
  (not_treated_i1_last_t)
  (not_started_i2_last_t)
  (not_treated_i2_last_t)
 )
)
(:durative-action _make_treatment1_i0_i1_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i0_t3_last_t))
   (at start (next_to_treat_t3_i0))
   (at start (not_busy))
   (at start (not_treated_i0_t3))
   (at start (not_started_i0_t3))
   (at start (ready_i0_t3))
  )
 :effect (and
  (at start (not (not_started_i0_t3)))
  (at start (not (next_to_treat_t3_i0)))
  (at start (not (not_busy)))
  (at start (not (s1_i0_t3_last_t)))
  (at start (next_to_treat_t3_i1))
  (at start (busy))
  (at start (started_i0_t3))
  (at end (not (not_treated_i0_t3)))
  (at end (not (busy)))
  (at end (s2_i0_t3_last_t))
  (at end (treated_i0_t3))
  (at end (not_busy))
 )
)
(:durative-action _make_treatment1_i1_i2_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i1_t3_last_t))
   (at start (next_to_treat_t3_i1))
   (at start (not_busy))
   (at start (not_treated_i1_t3))
   (at start (not_started_i1_t3))
   (at start (ready_i1_t3))
  )
 :effect (and
  (at start (not (not_started_i1_t3)))
  (at start (not (not_busy)))
  (at start (not (next_to_treat_t3_i1)))
  (at start (not (s1_i1_t3_last_t)))
  (at start (busy))
  (at start (next_to_treat_t3_i2))
  (at start (started_i1_t3))
  (at end (not (not_treated_i1_t3)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i1_t3_last_t))
  (at end (treated_i1_t3))
 )
)
(:durative-action _make_treatment1_i0_i1_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i0_t0_t1))
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
  (at start (not (s1_i0_t0_t1)))
  (at start (busy))
  (at start (next_to_treat_t0_i1))
  (at start (started_i0_t0))
  (at end (not (not_treated_i0_t0)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i0_t0_t1))
  (at end (treated_i0_t0))
 )
)
(:durative-action _make_treatment1_i1_i2_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i1_t0_t1))
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
  (at start (not (s1_i1_t0_t1)))
  (at start (busy))
  (at start (next_to_treat_t0_i2))
  (at start (started_i1_t0))
  (at end (not (not_treated_i1_t0)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i1_t0_t1))
  (at end (treated_i1_t0))
 )
)
(:durative-action _make_treatment1_i0_i1_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i0_t1_t2))
   (at start (next_to_treat_t1_i0))
   (at start (not_busy))
   (at start (not_treated_i0_t1))
   (at start (not_started_i0_t1))
   (at start (ready_i0_t1))
  )
 :effect (and
  (at start (not (not_started_i0_t1)))
  (at start (not (next_to_treat_t1_i0)))
  (at start (not (not_busy)))
  (at start (not (s1_i0_t1_t2)))
  (at start (busy))
  (at start (next_to_treat_t1_i1))
  (at start (started_i0_t1))
  (at end (not (not_treated_i0_t1)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i0_t1_t2))
  (at end (treated_i0_t1))
 )
)
(:durative-action _make_treatment1_i1_i2_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i1_t1_t2))
   (at start (next_to_treat_t1_i1))
   (at start (not_busy))
   (at start (not_treated_i1_t1))
   (at start (not_started_i1_t1))
   (at start (ready_i1_t1))
  )
 :effect (and
  (at start (not (not_started_i1_t1)))
  (at start (not (not_busy)))
  (at start (not (next_to_treat_t1_i1)))
  (at start (not (s1_i1_t1_t2)))
  (at start (busy))
  (at start (next_to_treat_t1_i2))
  (at start (started_i1_t1))
  (at end (not (not_treated_i1_t1)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i1_t1_t2))
  (at end (treated_i1_t1))
 )
)
(:durative-action _make_treatment1_i0_i1_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i0_t2_t3))
   (at start (next_to_treat_t2_i0))
   (at start (not_busy))
   (at start (not_treated_i0_t2))
   (at start (not_started_i0_t2))
   (at start (ready_i0_t2))
  )
 :effect (and
  (at start (not (not_started_i0_t2)))
  (at start (not (next_to_treat_t2_i0)))
  (at start (not (not_busy)))
  (at start (not (s1_i0_t2_t3)))
  (at start (busy))
  (at start (next_to_treat_t2_i1))
  (at start (started_i0_t2))
  (at end (not (not_treated_i0_t2)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i0_t2_t3))
  (at end (treated_i0_t2))
 )
)
(:durative-action _make_treatment1_i1_i2_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at start (s1_i1_t2_t3))
   (at start (next_to_treat_t2_i1))
   (at start (not_busy))
   (at start (not_treated_i1_t2))
   (at start (not_started_i1_t2))
   (at start (ready_i1_t2))
  )
 :effect (and
  (at start (not (not_started_i1_t2)))
  (at start (not (not_busy)))
  (at start (not (next_to_treat_t2_i1)))
  (at start (not (s1_i1_t2_t3)))
  (at start (busy))
  (at start (next_to_treat_t2_i2))
  (at start (started_i1_t2))
  (at end (not (not_treated_i1_t2)))
  (at end (not (busy)))
  (at end (not_busy))
  (at end (s2_i1_t2_t3))
  (at end (treated_i1_t2))
 )
)
(:durative-action _make_treatment2_i0_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i0_t3_last_t))
 :effect (and
  (at start (not (s2_i0_t3_last_t)))
  (at end (s3_i0_t3_last_t))
  (at end (ready_i0_last_t))
 )
)
(:durative-action _make_treatment2_i1_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i1_t3_last_t))
 :effect (and
  (at start (not (s2_i1_t3_last_t)))
  (at end (s3_i1_t3_last_t))
  (at end (ready_i1_last_t))
 )
)
(:durative-action _make_treatment2_i0_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i0_t0_t1))
 :effect (and
  (at start (not (s2_i0_t0_t1)))
  (at end (s3_i0_t0_t1))
  (at end (ready_i0_t1))
 )
)
(:durative-action _make_treatment2_i1_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i1_t0_t1))
 :effect (and
  (at start (not (s2_i1_t0_t1)))
  (at end (s3_i1_t0_t1))
  (at end (ready_i1_t1))
 )
)
(:durative-action _make_treatment2_i0_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i0_t1_t2))
 :effect (and
  (at start (not (s2_i0_t1_t2)))
  (at end (s3_i0_t1_t2))
  (at end (ready_i0_t2))
 )
)
(:durative-action _make_treatment2_i1_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i1_t1_t2))
 :effect (and
  (at start (not (s2_i1_t1_t2)))
  (at end (s3_i1_t1_t2))
  (at end (ready_i1_t2))
 )
)
(:durative-action _make_treatment2_i0_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i0_t2_t3))
 :effect (and
  (at start (not (s2_i0_t2_t3)))
  (at end (s3_i0_t2_t3))
  (at end (ready_i0_t3))
 )
)
(:durative-action _make_treatment2_i1_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 6)
   (<= ?duration 6)
  )
 :condition
  (at start (s2_i1_t2_t3))
 :effect (and
  (at start (not (s2_i1_t2_t3)))
  (at end (s3_i1_t2_t3))
  (at end (ready_i1_t3))
 )
)
(:durative-action _make_treatment3_i0_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i0_t3_last_t))
   (at end (started_i0_last_t))
  )
 :effect (and
  (at start (not (s3_i0_t3_last_t)))
  (at end (s4_i0_t3_last_t))
 )
)
(:durative-action _make_treatment3_i1_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i1_t3_last_t))
   (at end (started_i1_last_t))
  )
 :effect (and
  (at start (not (s3_i1_t3_last_t)))
  (at end (s4_i1_t3_last_t))
 )
)
(:durative-action _make_treatment3_i0_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i0_t0_t1))
   (at end (started_i0_t1))
  )
 :effect (and
  (at start (not (s3_i0_t0_t1)))
  (at end (s4_i0_t0_t1))
 )
)
(:durative-action _make_treatment3_i1_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i1_t0_t1))
   (at end (started_i1_t1))
  )
 :effect (and
  (at start (not (s3_i1_t0_t1)))
  (at end (s4_i1_t0_t1))
 )
)
(:durative-action _make_treatment3_i0_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i0_t1_t2))
   (at end (started_i0_t2))
  )
 :effect (and
  (at start (not (s3_i0_t1_t2)))
  (at end (s4_i0_t1_t2))
 )
)
(:durative-action _make_treatment3_i1_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i1_t1_t2))
   (at end (started_i1_t2))
  )
 :effect (and
  (at start (not (s3_i1_t1_t2)))
  (at end (s4_i1_t1_t2))
 )
)
(:durative-action _make_treatment3_i0_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i0_t2_t3))
   (at end (started_i0_t3))
  )
 :effect (and
  (at start (not (s3_i0_t2_t3)))
  (at end (s4_i0_t2_t3))
 )
)
(:durative-action _make_treatment3_i1_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (and
   (at start (s3_i1_t2_t3))
   (at end (started_i1_t3))
  )
 :effect (and
  (at start (not (s3_i1_t2_t3)))
  (at end (s4_i1_t2_t3))
 )
)
(:durative-action _make_treatment_container_i0_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i0_t3_last_t))
 :effect (and
  (at start (s1_i0_t3_last_t))
  (at end (not (s4_i0_t3_last_t)))
 )
)
(:durative-action _make_treatment_container_i1_t3_last_t_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i1_t3_last_t))
 :effect (and
  (at start (s1_i1_t3_last_t))
  (at end (not (s4_i1_t3_last_t)))
 )
)
(:durative-action _make_treatment_container_i0_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i0_t0_t1))
 :effect (and
  (at start (s1_i0_t0_t1))
  (at end (not (s4_i0_t0_t1)))
 )
)
(:durative-action _make_treatment_container_i1_t0_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i1_t0_t1))
 :effect (and
  (at start (s1_i1_t0_t1))
  (at end (not (s4_i1_t0_t1)))
 )
)
(:durative-action _make_treatment_container_i0_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i0_t1_t2))
 :effect (and
  (at start (s1_i0_t1_t2))
  (at end (not (s4_i0_t1_t2)))
 )
)
(:durative-action _make_treatment_container_i1_t1_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i1_t1_t2))
 :effect (and
  (at start (s1_i1_t1_t2))
  (at end (not (s4_i1_t1_t2)))
 )
)
(:durative-action _make_treatment_container_i0_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i0_t2_t3))
 :effect (and
  (at start (s1_i0_t2_t3))
  (at end (not (s4_i0_t2_t3)))
 )
)
(:durative-action _make_treatment_container_i1_t2_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 16)
   (<= ?duration 16)
  )
 :condition
  (at end (s4_i1_t2_t3))
 :effect (and
  (at start (s1_i1_t2_t3))
  (at end (not (s4_i1_t2_t3)))
 )
)
)
