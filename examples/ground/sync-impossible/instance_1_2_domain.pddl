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
)

(:durative-action _c1_r0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (exd_r0))
   (at start (exc_r0))
   (at end (pb_r0_p0))
   (at end (pb_r0_p1))
  )
 :effect (and
  (at start (not (exc_r0)))
  (at start (not (pb_r0_p0)))
  (at start (not (pb_r0_p1)))
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
   (at start (exc_r0))
  )
 :effect (and
  (at start (not (exc_r0)))
  (at start (not (px_r0_p0)))
  (at start (not (px_r0_p1)))
  (at end (exc_r0))
  (at end (pg_r0))
 )
)
(:durative-action _d_r0_p0_
 :parameters ()
 :duration
  (and
   (>= ?duration 44)
   (<= ?duration 44)
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
   (>= ?duration 48)
   (<= ?duration 48)
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
)
