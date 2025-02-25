(define (domain ground)
(:requirements :strips)
(:predicates
 (elevator-on-floor_e0_f4)
 (stopped_e0)
 (person-on-floor_p0_f0)
 (person-on-floor_p1_f0)
 (person-on-floor_p2_f0)
 (person-on-floor_p3_f0)
 (person-on-floor_p4_f1)
 (person-in-elevator_p0_e0)
 (person-in-elevator_p1_e0)
 (person-in-elevator_p2_e0)
 (person-in-elevator_p3_e0)
 (person-in-elevator_p4_e0)
 (person-on-floor_p4_f0)
 (person-on-floor_p0_f1)
 (person-on-floor_p1_f1)
 (person-on-floor_p2_f1)
 (person-on-floor_p3_f1)
 (person-on-floor_p0_f2)
 (person-on-floor_p1_f2)
 (person-on-floor_p2_f2)
 (person-on-floor_p3_f2)
 (person-on-floor_p4_f2)
 (person-on-floor_p0_f3)
 (person-on-floor_p1_f3)
 (person-on-floor_p2_f3)
 (person-on-floor_p3_f3)
 (person-on-floor_p4_f3)
 (person-on-floor_p0_f4)
 (person-on-floor_p1_f4)
 (person-on-floor_p2_f4)
 (person-on-floor_p3_f4)
 (person-on-floor_p4_f4)
 (elevator-on-floor_e0_f0)
 (elevator-on-floor_e0_f1)
 (elevator-on-floor_e0_f2)
 (elevator-on-floor_e0_f3)
)

(:durative-action _enter-elevator_p0_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-on-floor_p0_f0))
  )
 :effect (and
  (at start (not (person-on-floor_p0_f0)))
  (at end (person-in-elevator_p0_e0))
 )
)
(:durative-action _enter-elevator_p1_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-on-floor_p1_f0))
  )
 :effect (and
  (at start (not (person-on-floor_p1_f0)))
  (at end (person-in-elevator_p1_e0))
 )
)
(:durative-action _enter-elevator_p2_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-on-floor_p2_f0))
  )
 :effect (and
  (at start (not (person-on-floor_p2_f0)))
  (at end (person-in-elevator_p2_e0))
 )
)
(:durative-action _enter-elevator_p3_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-on-floor_p3_f0))
  )
 :effect (and
  (at start (not (person-on-floor_p3_f0)))
  (at end (person-in-elevator_p3_e0))
 )
)
(:durative-action _enter-elevator_p4_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-on-floor_p4_f0))
  )
 :effect (and
  (at start (not (person-on-floor_p4_f0)))
  (at end (person-in-elevator_p4_e0))
 )
)
(:durative-action _enter-elevator_p0_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-on-floor_p0_f1))
  )
 :effect (and
  (at start (not (person-on-floor_p0_f1)))
  (at end (person-in-elevator_p0_e0))
 )
)
(:durative-action _enter-elevator_p1_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-on-floor_p1_f1))
  )
 :effect (and
  (at start (not (person-on-floor_p1_f1)))
  (at end (person-in-elevator_p1_e0))
 )
)
(:durative-action _enter-elevator_p2_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-on-floor_p2_f1))
  )
 :effect (and
  (at start (not (person-on-floor_p2_f1)))
  (at end (person-in-elevator_p2_e0))
 )
)
(:durative-action _enter-elevator_p3_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-on-floor_p3_f1))
  )
 :effect (and
  (at start (not (person-on-floor_p3_f1)))
  (at end (person-in-elevator_p3_e0))
 )
)
(:durative-action _enter-elevator_p4_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-on-floor_p4_f1))
  )
 :effect (and
  (at start (not (person-on-floor_p4_f1)))
  (at end (person-in-elevator_p4_e0))
 )
)
(:durative-action _enter-elevator_p0_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-on-floor_p0_f2))
  )
 :effect (and
  (at start (not (person-on-floor_p0_f2)))
  (at end (person-in-elevator_p0_e0))
 )
)
(:durative-action _enter-elevator_p1_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-on-floor_p1_f2))
  )
 :effect (and
  (at start (not (person-on-floor_p1_f2)))
  (at end (person-in-elevator_p1_e0))
 )
)
(:durative-action _enter-elevator_p2_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-on-floor_p2_f2))
  )
 :effect (and
  (at start (not (person-on-floor_p2_f2)))
  (at end (person-in-elevator_p2_e0))
 )
)
(:durative-action _enter-elevator_p3_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-on-floor_p3_f2))
  )
 :effect (and
  (at start (not (person-on-floor_p3_f2)))
  (at end (person-in-elevator_p3_e0))
 )
)
(:durative-action _enter-elevator_p4_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-on-floor_p4_f2))
  )
 :effect (and
  (at start (not (person-on-floor_p4_f2)))
  (at end (person-in-elevator_p4_e0))
 )
)
(:durative-action _enter-elevator_p0_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-on-floor_p0_f3))
  )
 :effect (and
  (at start (not (person-on-floor_p0_f3)))
  (at end (person-in-elevator_p0_e0))
 )
)
(:durative-action _enter-elevator_p1_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-on-floor_p1_f3))
  )
 :effect (and
  (at start (not (person-on-floor_p1_f3)))
  (at end (person-in-elevator_p1_e0))
 )
)
(:durative-action _enter-elevator_p2_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-on-floor_p2_f3))
  )
 :effect (and
  (at start (not (person-on-floor_p2_f3)))
  (at end (person-in-elevator_p2_e0))
 )
)
(:durative-action _enter-elevator_p3_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-on-floor_p3_f3))
  )
 :effect (and
  (at start (not (person-on-floor_p3_f3)))
  (at end (person-in-elevator_p3_e0))
 )
)
(:durative-action _enter-elevator_p4_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-on-floor_p4_f3))
  )
 :effect (and
  (at start (not (person-on-floor_p4_f3)))
  (at end (person-in-elevator_p4_e0))
 )
)
(:durative-action _enter-elevator_p0_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-on-floor_p0_f4))
  )
 :effect (and
  (at start (not (person-on-floor_p0_f4)))
  (at end (person-in-elevator_p0_e0))
 )
)
(:durative-action _enter-elevator_p1_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-on-floor_p1_f4))
  )
 :effect (and
  (at start (not (person-on-floor_p1_f4)))
  (at end (person-in-elevator_p1_e0))
 )
)
(:durative-action _enter-elevator_p2_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-on-floor_p2_f4))
  )
 :effect (and
  (at start (not (person-on-floor_p2_f4)))
  (at end (person-in-elevator_p2_e0))
 )
)
(:durative-action _enter-elevator_p3_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-on-floor_p3_f4))
  )
 :effect (and
  (at start (not (person-on-floor_p3_f4)))
  (at end (person-in-elevator_p3_e0))
 )
)
(:durative-action _enter-elevator_p4_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-on-floor_p4_f4))
  )
 :effect (and
  (at start (not (person-on-floor_p4_f4)))
  (at end (person-in-elevator_p4_e0))
 )
)
(:durative-action _leave-elevator_p0_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-in-elevator_p0_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p0_e0)))
  (at end (person-on-floor_p0_f0))
 )
)
(:durative-action _leave-elevator_p1_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-in-elevator_p1_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p1_e0)))
  (at end (person-on-floor_p1_f0))
 )
)
(:durative-action _leave-elevator_p2_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-in-elevator_p2_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p2_e0)))
  (at end (person-on-floor_p2_f0))
 )
)
(:durative-action _leave-elevator_p3_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-in-elevator_p3_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p3_e0)))
  (at end (person-on-floor_p3_f0))
 )
)
(:durative-action _leave-elevator_p4_e0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f0))
   (over all (stopped_e0))
   (at start (person-in-elevator_p4_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p4_e0)))
  (at end (person-on-floor_p4_f0))
 )
)
(:durative-action _leave-elevator_p0_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-in-elevator_p0_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p0_e0)))
  (at end (person-on-floor_p0_f1))
 )
)
(:durative-action _leave-elevator_p1_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-in-elevator_p1_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p1_e0)))
  (at end (person-on-floor_p1_f1))
 )
)
(:durative-action _leave-elevator_p2_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-in-elevator_p2_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p2_e0)))
  (at end (person-on-floor_p2_f1))
 )
)
(:durative-action _leave-elevator_p3_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-in-elevator_p3_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p3_e0)))
  (at end (person-on-floor_p3_f1))
 )
)
(:durative-action _leave-elevator_p4_e0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f1))
   (over all (stopped_e0))
   (at start (person-in-elevator_p4_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p4_e0)))
  (at end (person-on-floor_p4_f1))
 )
)
(:durative-action _leave-elevator_p0_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-in-elevator_p0_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p0_e0)))
  (at end (person-on-floor_p0_f2))
 )
)
(:durative-action _leave-elevator_p1_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-in-elevator_p1_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p1_e0)))
  (at end (person-on-floor_p1_f2))
 )
)
(:durative-action _leave-elevator_p2_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-in-elevator_p2_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p2_e0)))
  (at end (person-on-floor_p2_f2))
 )
)
(:durative-action _leave-elevator_p3_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-in-elevator_p3_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p3_e0)))
  (at end (person-on-floor_p3_f2))
 )
)
(:durative-action _leave-elevator_p4_e0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f2))
   (over all (stopped_e0))
   (at start (person-in-elevator_p4_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p4_e0)))
  (at end (person-on-floor_p4_f2))
 )
)
(:durative-action _leave-elevator_p0_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-in-elevator_p0_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p0_e0)))
  (at end (person-on-floor_p0_f3))
 )
)
(:durative-action _leave-elevator_p1_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-in-elevator_p1_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p1_e0)))
  (at end (person-on-floor_p1_f3))
 )
)
(:durative-action _leave-elevator_p2_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-in-elevator_p2_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p2_e0)))
  (at end (person-on-floor_p2_f3))
 )
)
(:durative-action _leave-elevator_p3_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-in-elevator_p3_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p3_e0)))
  (at end (person-on-floor_p3_f3))
 )
)
(:durative-action _leave-elevator_p4_e0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f3))
   (over all (stopped_e0))
   (at start (person-in-elevator_p4_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p4_e0)))
  (at end (person-on-floor_p4_f3))
 )
)
(:durative-action _leave-elevator_p0_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-in-elevator_p0_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p0_e0)))
  (at end (person-on-floor_p0_f4))
 )
)
(:durative-action _leave-elevator_p1_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-in-elevator_p1_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p1_e0)))
  (at end (person-on-floor_p1_f4))
 )
)
(:durative-action _leave-elevator_p2_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-in-elevator_p2_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p2_e0)))
  (at end (person-on-floor_p2_f4))
 )
)
(:durative-action _leave-elevator_p3_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-in-elevator_p3_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p3_e0)))
  (at end (person-on-floor_p3_f4))
 )
)
(:durative-action _leave-elevator_p4_e0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (over all (elevator-on-floor_e0_f4))
   (over all (stopped_e0))
   (at start (person-in-elevator_p4_e0))
  )
 :effect (and
  (at start (not (person-in-elevator_p4_e0)))
  (at end (person-on-floor_p4_f4))
 )
)
(:durative-action _move-elevator_e0_f0_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f0))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f0))
 )
)
(:durative-action _move-elevator_e0_f1_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f1))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f1)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f0))
 )
)
(:durative-action _move-elevator_e0_f2_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f2))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f2)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f0))
 )
)
(:durative-action _move-elevator_e0_f3_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f3))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f3)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f0))
 )
)
(:durative-action _move-elevator_e0_f4_f0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f4))
 :effect (and
  (at start (not (elevator-on-floor_e0_f4)))
  (at start (not (stopped_e0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f0))
 )
)
(:durative-action _move-elevator_e0_f0_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f0))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f1))
 )
)
(:durative-action _move-elevator_e0_f1_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f1))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f1)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f1))
 )
)
(:durative-action _move-elevator_e0_f2_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f2))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f2)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f1))
 )
)
(:durative-action _move-elevator_e0_f3_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f3))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f3)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f1))
 )
)
(:durative-action _move-elevator_e0_f4_f1_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f4))
 :effect (and
  (at start (not (elevator-on-floor_e0_f4)))
  (at start (not (stopped_e0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f1))
 )
)
(:durative-action _move-elevator_e0_f0_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f0))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f2))
 )
)
(:durative-action _move-elevator_e0_f1_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f1))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f1)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f2))
 )
)
(:durative-action _move-elevator_e0_f2_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f2))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f2)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f2))
 )
)
(:durative-action _move-elevator_e0_f3_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f3))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f3)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f2))
 )
)
(:durative-action _move-elevator_e0_f4_f2_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f4))
 :effect (and
  (at start (not (elevator-on-floor_e0_f4)))
  (at start (not (stopped_e0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f2))
 )
)
(:durative-action _move-elevator_e0_f0_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f0))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f3))
 )
)
(:durative-action _move-elevator_e0_f1_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f1))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f1)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f3))
 )
)
(:durative-action _move-elevator_e0_f2_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f2))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f2)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f3))
 )
)
(:durative-action _move-elevator_e0_f3_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f3))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f3)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f3))
 )
)
(:durative-action _move-elevator_e0_f4_f3_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f4))
 :effect (and
  (at start (not (elevator-on-floor_e0_f4)))
  (at start (not (stopped_e0)))
  (at end (stopped_e0))
  (at end (elevator-on-floor_e0_f3))
 )
)
(:durative-action _move-elevator_e0_f0_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f0))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f0)))
  (at end (elevator-on-floor_e0_f4))
  (at end (stopped_e0))
 )
)
(:durative-action _move-elevator_e0_f1_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f1))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f1)))
  (at end (elevator-on-floor_e0_f4))
  (at end (stopped_e0))
 )
)
(:durative-action _move-elevator_e0_f2_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f2))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f2)))
  (at end (elevator-on-floor_e0_f4))
  (at end (stopped_e0))
 )
)
(:durative-action _move-elevator_e0_f3_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f3))
 :effect (and
  (at start (not (stopped_e0)))
  (at start (not (elevator-on-floor_e0_f3)))
  (at end (elevator-on-floor_e0_f4))
  (at end (stopped_e0))
 )
)
(:durative-action _move-elevator_e0_f4_f4_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (at start (elevator-on-floor_e0_f4))
 :effect (and
  (at start (not (elevator-on-floor_e0_f4)))
  (at start (not (stopped_e0)))
  (at end (elevator-on-floor_e0_f4))
  (at end (stopped_e0))
 )
)
)
