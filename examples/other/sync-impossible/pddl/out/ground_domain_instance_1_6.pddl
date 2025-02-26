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
  )
 :effect (and
  (at start (not (exc_r0)))
  (at start (not (pb_r0_p0)))
  (at start (not (pb_r0_p1)))
  (at start (not (pb_r0_p2)))
  (at start (not (pb_r0_p3)))
  (at start (not (pb_r0_p4)))
  (at start (not (pb_r0_p5)))
  (at start (pa_r0))
  (at end (not (pa_r0)))
  (at end (exc_r0))
 )
)
(:durative-action _c2_r0_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at end (px_r0_p0))
   (at end (px_r0_p1))
   (at end (px_r0_p2))
   (at end (px_r0_p3))
   (at end (px_r0_p4))
   (at end (px_r0_p5))
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
  (at end (exc_r0))
  (at end (pg_r0))
 )
)
(:durative-action _d_r0_p0_
 :parameters ()
 :duration
  (and
   (>= ?duration 25)
   (<= ?duration 25)
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
   (>= ?duration 7)
   (<= ?duration 7)
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
   (>= ?duration 23)
   (<= ?duration 23)
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
   (>= ?duration 23)
   (<= ?duration 23)
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
   (>= ?duration 39)
   (<= ?duration 39)
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
   (>= ?duration 17)
   (<= ?duration 17)
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
)
