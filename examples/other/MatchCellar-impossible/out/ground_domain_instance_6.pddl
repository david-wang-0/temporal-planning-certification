(define (domain ground)
(:requirements :strips)
(:predicates
 (handfree)
 (unused_match0)
 (unused_match1)
 (unused_match2)
 (unused_match3)
 (light_match0)
 (light_match1)
 (light_match2)
 (light_match3)
 (mended_fuse0)
 (mended_fuse1)
 (mended_fuse2)
 (mended_fuse3)
 (mended_fuse4)
 (mended_fuse5)
 (mended_fuse6)
 (mended_fuse7)
 (mended_fuse8)
)

(:durative-action _light_match_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (unused_match0))
 :effect (and
  (at start (not (unused_match0)))
  (at start (light_match0))
  (at end (not (light_match0)))
 )
)
(:durative-action _light_match_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (unused_match1))
 :effect (and
  (at start (not (unused_match1)))
  (at start (light_match1))
  (at end (not (light_match1)))
 )
)
(:durative-action _light_match_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (unused_match2))
 :effect (and
  (at start (not (unused_match2)))
  (at start (light_match2))
  (at end (not (light_match2)))
 )
)
(:durative-action _light_match_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (unused_match3))
 :effect (and
  (at start (not (unused_match3)))
  (at start (light_match3))
  (at end (not (light_match3)))
 )
)
(:durative-action _mend_fuse_fuse0_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse0))
 )
)
(:durative-action _mend_fuse_fuse1_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse1))
 )
)
(:durative-action _mend_fuse_fuse2_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse2))
 )
)
(:durative-action _mend_fuse_fuse3_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse3))
 )
)
(:durative-action _mend_fuse_fuse4_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse4))
 )
)
(:durative-action _mend_fuse_fuse5_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse5))
 )
)
(:durative-action _mend_fuse_fuse6_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse6))
 )
)
(:durative-action _mend_fuse_fuse7_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse7))
 )
)
(:durative-action _mend_fuse_fuse8_match0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match0))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse8))
 )
)
(:durative-action _mend_fuse_fuse0_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse0))
 )
)
(:durative-action _mend_fuse_fuse1_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse1))
 )
)
(:durative-action _mend_fuse_fuse2_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse2))
 )
)
(:durative-action _mend_fuse_fuse3_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse3))
 )
)
(:durative-action _mend_fuse_fuse4_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse4))
 )
)
(:durative-action _mend_fuse_fuse5_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse5))
 )
)
(:durative-action _mend_fuse_fuse6_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse6))
 )
)
(:durative-action _mend_fuse_fuse7_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse7))
 )
)
(:durative-action _mend_fuse_fuse8_match1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match1))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse8))
 )
)
(:durative-action _mend_fuse_fuse0_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse0))
 )
)
(:durative-action _mend_fuse_fuse1_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse1))
 )
)
(:durative-action _mend_fuse_fuse2_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse2))
 )
)
(:durative-action _mend_fuse_fuse3_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse3))
 )
)
(:durative-action _mend_fuse_fuse4_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse4))
 )
)
(:durative-action _mend_fuse_fuse5_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse5))
 )
)
(:durative-action _mend_fuse_fuse6_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse6))
 )
)
(:durative-action _mend_fuse_fuse7_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse7))
 )
)
(:durative-action _mend_fuse_fuse8_match2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match2))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse8))
 )
)
(:durative-action _mend_fuse_fuse0_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse0))
 )
)
(:durative-action _mend_fuse_fuse1_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse1))
 )
)
(:durative-action _mend_fuse_fuse2_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse2))
 )
)
(:durative-action _mend_fuse_fuse3_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse3))
 )
)
(:durative-action _mend_fuse_fuse4_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse4))
 )
)
(:durative-action _mend_fuse_fuse5_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse5))
 )
)
(:durative-action _mend_fuse_fuse6_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse6))
 )
)
(:durative-action _mend_fuse_fuse7_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse7))
 )
)
(:durative-action _mend_fuse_fuse8_match3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (at start (handfree))
   (over all (light_match3))
  )
 :effect (and
  (at start (not (handfree)))
  (at end (handfree))
  (at end (mended_fuse8))
 )
)
)
