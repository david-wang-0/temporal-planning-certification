(define (domain ground)
(:requirements :strips :durative-actions)
(:predicates
 (s_x)
 (p_x)
 (q_x)
 (r_x)
)

(:durative-action _a_x_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (or
    (over all (p_x))
    (over all (q_x))
   )
   (at end (r_x))
  )
 :effect (and
  (at start (p_x))
  (at end (s_x))
 )
)
(:durative-action _b_x_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (at start (p_x))
 :effect (and
  (at start (not (p_x)))
  (at start (q_x))
  (at start (r_x))
 )
)
)
