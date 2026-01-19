(define (domain ground)
(:requirements :strips)
(:predicates
 (exd_r0)
 (exc_r0)
 (pa_r0)
 (pg_r0)
 (px_r0_p0)
 (pb_r0_p0)
 (px_r0_p1)
 (pb_r0_p1)
 (px_r0_p2)
 (pb_r0_p2)
 (px_r0_p3)
 (pb_r0_p3)
 (px_r0_p4)
 (pb_r0_p4)
 (px_r0_p5)
 (pb_r0_p5)
 (px_r0_p6)
 (pb_r0_p6)
 (px_r0_p7)
 (pb_r0_p7)
 (px_r0_p8)
 (pb_r0_p8)
)

(:durative-action _c1_r0_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (exd_r0))
   (at start (exc_r0))
   (at end (pb_r0_p0))
   (at end (pb_r0_p1))
   (at end (pb_r0_p2))
   (at end (pb_r0_p3))
   (at end (pb_r0_p4))
   (at end (pb_r0_p5))
   (at end (pb_r0_p6))
   (at end (pb_r0_p7))
   (at end (pb_r0_p8))
  )
 :effect (and
  (at start (not (exc_r0)))
  (at start (not (pb_r0_p0)))
  (at start (not (pb_r0_p1)))
  (at start (not (pb_r0_p2)))
  (at start (not (pb_r0_p3)))
  (at start (not (pb_r0_p4)))
  (at start (not (pb_r0_p5)))
  (at start (not (pb_r0_p6)))
  (at start (not (pb_r0_p7)))
  (at start (not (pb_r0_p8)))
  (at start (pa_r0))
  (at end (not (pa_r0)))
  (at end (exc_r0))
 )
)
(:durative-action _c2_r0_
 :parameters ()
 :duration
  (and
   (>= ?duration 4)
   (<= ?duration 4)
  )
 :condition
  (and
   (at end (px_r0_p0))
   (at end (px_r0_p1))
   (at end (px_r0_p2))
   (at end (px_r0_p3))
   (at end (px_r0_p4))
   (at end (px_r0_p5))
   (at end (px_r0_p6))
   (at end (px_r0_p7))
   (at end (px_r0_p8))
   (at start (exc_r0))
  )
 :effect (and
  (at start (not (exc_r0)))
  (at start (not (px_r0_p0)))
  (at start (not (px_r0_p1)))
  (at start (not (px_r0_p2)))
  (at start (not (px_r0_p3)))
  (at start (not (px_r0_p4)))
  (at start (not (px_r0_p5)))
  (at start (not (px_r0_p6)))
  (at start (not (px_r0_p7)))
  (at start (not (px_r0_p8)))
  (at end (exc_r0))
  (at end (pg_r0))
 )
)
(:durative-action _d_r0_p0_
 :parameters ()
 :duration
  (and
   (>= ?duration 18)
   (<= ?duration 18)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p0))
  (at end (exd_r0))
  (at end (px_r0_p0))
 )
)
(:durative-action _d_r0_p1_
 :parameters ()
 :duration
  (and
   (>= ?duration 30)
   (<= ?duration 30)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p1))
  (at end (exd_r0))
  (at end (px_r0_p1))
 )
)
(:durative-action _d_r0_p2_
 :parameters ()
 :duration
  (and
   (>= ?duration 41)
   (<= ?duration 41)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p2))
  (at end (exd_r0))
  (at end (px_r0_p2))
 )
)
(:durative-action _d_r0_p3_
 :parameters ()
 :duration
  (and
   (>= ?duration 24)
   (<= ?duration 24)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p3))
  (at end (exd_r0))
  (at end (px_r0_p3))
 )
)
(:durative-action _d_r0_p4_
 :parameters ()
 :duration
  (and
   (>= ?duration 11)
   (<= ?duration 11)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p4))
  (at end (exd_r0))
  (at end (px_r0_p4))
 )
)
(:durative-action _d_r0_p5_
 :parameters ()
 :duration
  (and
   (>= ?duration 24)
   (<= ?duration 24)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p5))
  (at end (exd_r0))
  (at end (px_r0_p5))
 )
)
(:durative-action _d_r0_p6_
 :parameters ()
 :duration
  (and
   (>= ?duration 23)
   (<= ?duration 23)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p6))
  (at end (exd_r0))
  (at end (px_r0_p6))
 )
)
(:durative-action _d_r0_p7_
 :parameters ()
 :duration
  (and
   (>= ?duration 14)
   (<= ?duration 14)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p7))
  (at end (exd_r0))
  (at end (px_r0_p7))
 )
)
(:durative-action _d_r0_p8_
 :parameters ()
 :duration
  (and
   (>= ?duration 43)
   (<= ?duration 43)
  )
 :condition
  (at start (pa_r0))
 :effect (and
  (at start (not (exd_r0)))
  (at start (pb_r0_p8))
  (at end (exd_r0))
  (at end (px_r0_p8))
 )
)
)
