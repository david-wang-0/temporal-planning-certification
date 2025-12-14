(define (domain ground)
(:requirements :strips)
(:predicates
 (robot-at_robot1_tile-3-3)
 (robot-has_robot1_white)
 (robot-at_robot2_tile-0-1)
 (robot-has_robot2_black)
 (clear_tile-0-2)
 (clear_tile-0-3)
 (clear_tile-0-4)
 (clear_tile-1-1)
 (clear_tile-1-2)
 (clear_tile-1-3)
 (clear_tile-1-4)
 (clear_tile-2-1)
 (clear_tile-2-2)
 (clear_tile-2-3)
 (clear_tile-2-4)
 (clear_tile-3-1)
 (clear_tile-3-2)
 (clear_tile-3-4)
 (clear_tile-4-1)
 (clear_tile-4-2)
 (clear_tile-4-3)
 (clear_tile-4-4)
 (robot-has_robot1_black)
 (robot-has_robot2_white)
 (painted_tile-1-1_black)
 (painted_tile-1-2_black)
 (painted_tile-1-3_black)
 (painted_tile-1-4_black)
 (painted_tile-2-1_black)
 (painted_tile-2-2_black)
 (painted_tile-2-3_black)
 (painted_tile-2-4_black)
 (painted_tile-3-1_black)
 (painted_tile-3-2_black)
 (painted_tile-3-3_black)
 (painted_tile-3-4_black)
 (painted_tile-4-1_black)
 (painted_tile-4-2_black)
 (painted_tile-4-3_black)
 (painted_tile-4-4_black)
 (painted_tile-1-1_white)
 (painted_tile-1-2_white)
 (painted_tile-1-3_white)
 (painted_tile-1-4_white)
 (painted_tile-2-1_white)
 (painted_tile-2-2_white)
 (painted_tile-2-3_white)
 (painted_tile-2-4_white)
 (painted_tile-3-1_white)
 (painted_tile-3-2_white)
 (painted_tile-3-3_white)
 (painted_tile-3-4_white)
 (painted_tile-4-1_white)
 (painted_tile-4-2_white)
 (painted_tile-4-3_white)
 (painted_tile-4-4_white)
 (painted_tile-0-1_black)
 (painted_tile-0-2_black)
 (painted_tile-0-3_black)
 (painted_tile-0-4_black)
 (painted_tile-0-1_white)
 (painted_tile-0-2_white)
 (painted_tile-0-3_white)
 (painted_tile-0-4_white)
 (clear_tile-0-1)
 (robot-at_robot1_tile-1-1)
 (robot-at_robot2_tile-1-1)
 (robot-at_robot1_tile-1-2)
 (robot-at_robot2_tile-1-2)
 (robot-at_robot1_tile-1-3)
 (robot-at_robot2_tile-1-3)
 (robot-at_robot1_tile-1-4)
 (robot-at_robot2_tile-1-4)
 (robot-at_robot1_tile-2-1)
 (robot-at_robot2_tile-2-1)
 (robot-at_robot1_tile-2-2)
 (robot-at_robot2_tile-2-2)
 (robot-at_robot1_tile-2-3)
 (robot-at_robot2_tile-2-3)
 (robot-at_robot1_tile-2-4)
 (robot-at_robot2_tile-2-4)
 (robot-at_robot1_tile-3-1)
 (robot-at_robot2_tile-3-1)
 (robot-at_robot1_tile-3-2)
 (robot-at_robot2_tile-3-2)
 (robot-at_robot2_tile-3-3)
 (robot-at_robot1_tile-3-4)
 (robot-at_robot2_tile-3-4)
 (robot-at_robot1_tile-4-1)
 (robot-at_robot2_tile-4-1)
 (robot-at_robot1_tile-4-2)
 (robot-at_robot2_tile-4-2)
 (clear_tile-3-3)
 (robot-at_robot1_tile-4-3)
 (robot-at_robot2_tile-4-3)
 (robot-at_robot1_tile-4-4)
 (robot-at_robot2_tile-4-4)
 (robot-at_robot1_tile-0-1)
 (robot-at_robot1_tile-0-2)
 (robot-at_robot2_tile-0-2)
 (robot-at_robot1_tile-0-3)
 (robot-at_robot2_tile-0-3)
 (robot-at_robot1_tile-0-4)
 (robot-at_robot2_tile-0-4)
)

(:durative-action _change-color_robot1_black_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot1_black))
 :effect (and
  (at start (not (robot-has_robot1_black)))
  (at end (robot-has_robot1_black))
 )
)
(:durative-action _change-color_robot2_black_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot2_black))
 :effect (and
  (at start (not (robot-has_robot2_black)))
  (at end (robot-has_robot2_black))
 )
)
(:durative-action _change-color_robot1_white_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot1_white))
 :effect (and
  (at start (not (robot-has_robot1_white)))
  (at end (robot-has_robot1_black))
 )
)
(:durative-action _change-color_robot2_white_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot2_white))
 :effect (and
  (at start (not (robot-has_robot2_white)))
  (at end (robot-has_robot2_black))
 )
)
(:durative-action _change-color_robot1_black_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot1_black))
 :effect (and
  (at start (not (robot-has_robot1_black)))
  (at end (robot-has_robot1_white))
 )
)
(:durative-action _change-color_robot2_black_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot2_black))
 :effect (and
  (at start (not (robot-has_robot2_black)))
  (at end (robot-has_robot2_white))
 )
)
(:durative-action _change-color_robot1_white_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot1_white))
 :effect (and
  (at start (not (robot-has_robot1_white)))
  (at end (robot-has_robot1_white))
 )
)
(:durative-action _change-color_robot2_white_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 5)
   (<= ?duration 5)
  )
 :condition
  (at start (robot-has_robot2_white))
 :effect (and
  (at start (not (robot-has_robot2_white)))
  (at end (robot-has_robot2_white))
 )
)
(:durative-action _paint-up_robot1_tile-1-2_tile-0-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-0-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at end (painted_tile-1-2_black))
 )
)
(:durative-action _paint-up_robot2_tile-1-2_tile-0-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-0-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at end (painted_tile-1-2_black))
 )
)
(:durative-action _paint-up_robot1_tile-1-4_tile-0-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-0-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at end (painted_tile-1-4_black))
 )
)
(:durative-action _paint-up_robot2_tile-1-4_tile-0-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-0-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at end (painted_tile-1-4_black))
 )
)
(:durative-action _paint-up_robot1_tile-2-1_tile-1-1_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-1-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at end (painted_tile-2-1_black))
 )
)
(:durative-action _paint-up_robot2_tile-2-1_tile-1-1_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-1-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at end (painted_tile-2-1_black))
 )
)
(:durative-action _paint-up_robot1_tile-2-3_tile-1-3_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-1-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at end (painted_tile-2-3_black))
 )
)
(:durative-action _paint-up_robot2_tile-2-3_tile-1-3_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-1-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at end (painted_tile-2-3_black))
 )
)
(:durative-action _paint-up_robot1_tile-3-2_tile-2-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-2-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at end (painted_tile-3-2_black))
 )
)
(:durative-action _paint-up_robot2_tile-3-2_tile-2-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-2-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at end (painted_tile-3-2_black))
 )
)
(:durative-action _paint-up_robot1_tile-3-4_tile-2-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-2-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at end (painted_tile-3-4_black))
 )
)
(:durative-action _paint-up_robot2_tile-3-4_tile-2-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-2-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at end (painted_tile-3-4_black))
 )
)
(:durative-action _paint-up_robot1_tile-4-1_tile-3-1_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-3-1))
   (at start (clear_tile-4-1))
  )
 :effect (and
  (at start (not (clear_tile-4-1)))
  (at end (painted_tile-4-1_black))
 )
)
(:durative-action _paint-up_robot2_tile-4-1_tile-3-1_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-3-1))
   (at start (clear_tile-4-1))
  )
 :effect (and
  (at start (not (clear_tile-4-1)))
  (at end (painted_tile-4-1_black))
 )
)
(:durative-action _paint-up_robot1_tile-4-3_tile-3-3_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-3-3))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at end (painted_tile-4-3_black))
 )
)
(:durative-action _paint-up_robot2_tile-4-3_tile-3-3_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-3-3))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at end (painted_tile-4-3_black))
 )
)
(:durative-action _paint-up_robot1_tile-1-1_tile-0-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-0-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at end (painted_tile-1-1_white))
 )
)
(:durative-action _paint-up_robot2_tile-1-1_tile-0-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-0-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at end (painted_tile-1-1_white))
 )
)
(:durative-action _paint-up_robot1_tile-1-3_tile-0-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-0-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at end (painted_tile-1-3_white))
 )
)
(:durative-action _paint-up_robot2_tile-1-3_tile-0-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-0-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at end (painted_tile-1-3_white))
 )
)
(:durative-action _paint-up_robot1_tile-2-2_tile-1-2_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-1-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at end (painted_tile-2-2_white))
 )
)
(:durative-action _paint-up_robot2_tile-2-2_tile-1-2_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-1-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at end (painted_tile-2-2_white))
 )
)
(:durative-action _paint-up_robot1_tile-2-4_tile-1-4_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-1-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at end (painted_tile-2-4_white))
 )
)
(:durative-action _paint-up_robot2_tile-2-4_tile-1-4_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-1-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at end (painted_tile-2-4_white))
 )
)
(:durative-action _paint-up_robot1_tile-3-1_tile-2-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-2-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at end (painted_tile-3-1_white))
 )
)
(:durative-action _paint-up_robot2_tile-3-1_tile-2-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-2-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at end (painted_tile-3-1_white))
 )
)
(:durative-action _paint-up_robot1_tile-3-3_tile-2-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-2-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (clear_tile-3-3)))
  (at end (painted_tile-3-3_white))
 )
)
(:durative-action _paint-up_robot2_tile-3-3_tile-2-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-2-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (clear_tile-3-3)))
  (at end (painted_tile-3-3_white))
 )
)
(:durative-action _paint-up_robot1_tile-4-2_tile-3-2_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-3-2))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at end (painted_tile-4-2_white))
 )
)
(:durative-action _paint-up_robot2_tile-4-2_tile-3-2_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-3-2))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at end (painted_tile-4-2_white))
 )
)
(:durative-action _paint-up_robot1_tile-4-4_tile-3-4_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-3-4))
   (at start (clear_tile-4-4))
  )
 :effect (and
  (at start (not (clear_tile-4-4)))
  (at end (painted_tile-4-4_white))
 )
)
(:durative-action _paint-up_robot2_tile-4-4_tile-3-4_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-3-4))
   (at start (clear_tile-4-4))
  )
 :effect (and
  (at start (not (clear_tile-4-4)))
  (at end (painted_tile-4-4_white))
 )
)
(:durative-action _paint-down_robot1_tile-1-2_tile-2-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-2-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at end (painted_tile-1-2_black))
 )
)
(:durative-action _paint-down_robot2_tile-1-2_tile-2-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-2-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at end (painted_tile-1-2_black))
 )
)
(:durative-action _paint-down_robot1_tile-1-4_tile-2-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-2-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at end (painted_tile-1-4_black))
 )
)
(:durative-action _paint-down_robot2_tile-1-4_tile-2-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-2-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at end (painted_tile-1-4_black))
 )
)
(:durative-action _paint-down_robot1_tile-2-1_tile-3-1_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-3-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at end (painted_tile-2-1_black))
 )
)
(:durative-action _paint-down_robot2_tile-2-1_tile-3-1_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-3-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at end (painted_tile-2-1_black))
 )
)
(:durative-action _paint-down_robot1_tile-2-3_tile-3-3_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-3-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at end (painted_tile-2-3_black))
 )
)
(:durative-action _paint-down_robot2_tile-2-3_tile-3-3_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-3-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at end (painted_tile-2-3_black))
 )
)
(:durative-action _paint-down_robot1_tile-3-2_tile-4-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-4-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at end (painted_tile-3-2_black))
 )
)
(:durative-action _paint-down_robot2_tile-3-2_tile-4-2_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-4-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at end (painted_tile-3-2_black))
 )
)
(:durative-action _paint-down_robot1_tile-3-4_tile-4-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_black))
   (at start (robot-at_robot1_tile-4-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at end (painted_tile-3-4_black))
 )
)
(:durative-action _paint-down_robot2_tile-3-4_tile-4-4_black_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_black))
   (at start (robot-at_robot2_tile-4-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at end (painted_tile-3-4_black))
 )
)
(:durative-action _paint-down_robot1_tile-1-1_tile-2-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-2-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at end (painted_tile-1-1_white))
 )
)
(:durative-action _paint-down_robot2_tile-1-1_tile-2-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-2-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at end (painted_tile-1-1_white))
 )
)
(:durative-action _paint-down_robot1_tile-1-3_tile-2-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-2-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at end (painted_tile-1-3_white))
 )
)
(:durative-action _paint-down_robot2_tile-1-3_tile-2-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-2-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at end (painted_tile-1-3_white))
 )
)
(:durative-action _paint-down_robot1_tile-2-2_tile-3-2_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-3-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at end (painted_tile-2-2_white))
 )
)
(:durative-action _paint-down_robot2_tile-2-2_tile-3-2_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-3-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at end (painted_tile-2-2_white))
 )
)
(:durative-action _paint-down_robot1_tile-2-4_tile-3-4_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-3-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at end (painted_tile-2-4_white))
 )
)
(:durative-action _paint-down_robot2_tile-2-4_tile-3-4_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-3-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at end (painted_tile-2-4_white))
 )
)
(:durative-action _paint-down_robot1_tile-3-1_tile-4-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-4-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at end (painted_tile-3-1_white))
 )
)
(:durative-action _paint-down_robot2_tile-3-1_tile-4-1_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-4-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at end (painted_tile-3-1_white))
 )
)
(:durative-action _paint-down_robot1_tile-3-3_tile-4-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot1_white))
   (at start (robot-at_robot1_tile-4-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (clear_tile-3-3)))
  (at end (painted_tile-3-3_white))
 )
)
(:durative-action _paint-down_robot2_tile-3-3_tile-4-3_white_
 :parameters ()
 :duration
  (and
   (>= ?duration 2)
   (<= ?duration 2)
  )
 :condition
  (and
   (over all (robot-has_robot2_white))
   (at start (robot-at_robot2_tile-4-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (clear_tile-3-3)))
  (at end (painted_tile-3-3_white))
 )
)
(:durative-action _up_robot1_tile-0-1_tile-1-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at start (not (robot-at_robot1_tile-0-1)))
  (at end (clear_tile-0-1))
  (at end (robot-at_robot1_tile-1-1))
 )
)
(:durative-action _up_robot2_tile-0-1_tile-1-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (robot-at_robot2_tile-0-1)))
  (at start (not (clear_tile-1-1)))
  (at end (clear_tile-0-1))
  (at end (robot-at_robot2_tile-1-1))
 )
)
(:durative-action _up_robot1_tile-0-2_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot1_tile-0-2)))
  (at end (clear_tile-0-2))
  (at end (robot-at_robot1_tile-1-2))
 )
)
(:durative-action _up_robot2_tile-0-2_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot2_tile-0-2)))
  (at end (clear_tile-0-2))
  (at end (robot-at_robot2_tile-1-2))
 )
)
(:durative-action _up_robot1_tile-0-3_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot1_tile-0-3)))
  (at end (clear_tile-0-3))
  (at end (robot-at_robot1_tile-1-3))
 )
)
(:durative-action _up_robot2_tile-0-3_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot2_tile-0-3)))
  (at end (clear_tile-0-3))
  (at end (robot-at_robot2_tile-1-3))
 )
)
(:durative-action _up_robot1_tile-0-4_tile-1-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at start (not (robot-at_robot1_tile-0-4)))
  (at end (clear_tile-0-4))
  (at end (robot-at_robot1_tile-1-4))
 )
)
(:durative-action _up_robot2_tile-0-4_tile-1-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at start (not (robot-at_robot2_tile-0-4)))
  (at end (clear_tile-0-4))
  (at end (robot-at_robot2_tile-1-4))
 )
)
(:durative-action _up_robot1_tile-1-1_tile-2-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at start (not (robot-at_robot1_tile-1-1)))
  (at end (clear_tile-1-1))
  (at end (robot-at_robot1_tile-2-1))
 )
)
(:durative-action _up_robot2_tile-1-1_tile-2-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at start (not (robot-at_robot2_tile-1-1)))
  (at end (clear_tile-1-1))
  (at end (robot-at_robot2_tile-2-1))
 )
)
(:durative-action _up_robot1_tile-1-2_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot1_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot1_tile-2-2))
 )
)
(:durative-action _up_robot2_tile-1-2_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot2_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot2_tile-2-2))
 )
)
(:durative-action _up_robot1_tile-1-3_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot1_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot1_tile-2-3))
 )
)
(:durative-action _up_robot2_tile-1-3_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot2_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot2_tile-2-3))
 )
)
(:durative-action _up_robot1_tile-1-4_tile-2-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at start (not (robot-at_robot1_tile-1-4)))
  (at end (clear_tile-1-4))
  (at end (robot-at_robot1_tile-2-4))
 )
)
(:durative-action _up_robot2_tile-1-4_tile-2-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at start (not (robot-at_robot2_tile-1-4)))
  (at end (clear_tile-1-4))
  (at end (robot-at_robot2_tile-2-4))
 )
)
(:durative-action _up_robot1_tile-2-1_tile-3-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at start (not (robot-at_robot1_tile-2-1)))
  (at end (clear_tile-2-1))
  (at end (robot-at_robot1_tile-3-1))
 )
)
(:durative-action _up_robot2_tile-2-1_tile-3-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at start (not (robot-at_robot2_tile-2-1)))
  (at end (clear_tile-2-1))
  (at end (robot-at_robot2_tile-3-1))
 )
)
(:durative-action _up_robot1_tile-2-2_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot1_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot1_tile-3-2))
 )
)
(:durative-action _up_robot2_tile-2-2_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot2_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot2_tile-3-2))
 )
)
(:durative-action _up_robot1_tile-2-3_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-2-3)))
  (at start (not (clear_tile-3-3)))
  (at end (robot-at_robot1_tile-3-3))
  (at end (clear_tile-2-3))
 )
)
(:durative-action _up_robot2_tile-2-3_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (robot-at_robot2_tile-2-3)))
  (at start (not (clear_tile-3-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot2_tile-3-3))
 )
)
(:durative-action _up_robot1_tile-2-4_tile-3-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at start (not (robot-at_robot1_tile-2-4)))
  (at end (clear_tile-2-4))
  (at end (robot-at_robot1_tile-3-4))
 )
)
(:durative-action _up_robot2_tile-2-4_tile-3-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at start (not (robot-at_robot2_tile-2-4)))
  (at end (clear_tile-2-4))
  (at end (robot-at_robot2_tile-3-4))
 )
)
(:durative-action _up_robot1_tile-3-1_tile-4-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-1))
   (at start (clear_tile-4-1))
  )
 :effect (and
  (at start (not (clear_tile-4-1)))
  (at start (not (robot-at_robot1_tile-3-1)))
  (at end (clear_tile-3-1))
  (at end (robot-at_robot1_tile-4-1))
 )
)
(:durative-action _up_robot2_tile-3-1_tile-4-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-1))
   (at start (clear_tile-4-1))
  )
 :effect (and
  (at start (not (clear_tile-4-1)))
  (at start (not (robot-at_robot2_tile-3-1)))
  (at end (clear_tile-3-1))
  (at end (robot-at_robot2_tile-4-1))
 )
)
(:durative-action _up_robot1_tile-3-2_tile-4-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-2))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at start (not (robot-at_robot1_tile-3-2)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot1_tile-4-2))
 )
)
(:durative-action _up_robot2_tile-3-2_tile-4-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-2))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at start (not (robot-at_robot2_tile-3-2)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot2_tile-4-2))
 )
)
(:durative-action _up_robot1_tile-3-3_tile-4-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-3))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-3-3)))
  (at start (not (clear_tile-4-3)))
  (at end (clear_tile-3-3))
  (at end (robot-at_robot1_tile-4-3))
 )
)
(:durative-action _up_robot2_tile-3-3_tile-4-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-3))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at start (not (robot-at_robot2_tile-3-3)))
  (at end (clear_tile-3-3))
  (at end (robot-at_robot2_tile-4-3))
 )
)
(:durative-action _up_robot1_tile-3-4_tile-4-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-4))
   (at start (clear_tile-4-4))
  )
 :effect (and
  (at start (not (clear_tile-4-4)))
  (at start (not (robot-at_robot1_tile-3-4)))
  (at end (clear_tile-3-4))
  (at end (robot-at_robot1_tile-4-4))
 )
)
(:durative-action _up_robot2_tile-3-4_tile-4-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-4))
   (at start (clear_tile-4-4))
  )
 :effect (and
  (at start (not (clear_tile-4-4)))
  (at start (not (robot-at_robot2_tile-3-4)))
  (at end (clear_tile-3-4))
  (at end (robot-at_robot2_tile-4-4))
 )
)
(:durative-action _down_robot1_tile-1-1_tile-0-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-1))
   (at start (clear_tile-0-1))
  )
 :effect (and
  (at start (not (clear_tile-0-1)))
  (at start (not (robot-at_robot1_tile-1-1)))
  (at end (clear_tile-1-1))
  (at end (robot-at_robot1_tile-0-1))
 )
)
(:durative-action _down_robot2_tile-1-1_tile-0-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-1))
   (at start (clear_tile-0-1))
  )
 :effect (and
  (at start (not (clear_tile-0-1)))
  (at start (not (robot-at_robot2_tile-1-1)))
  (at end (robot-at_robot2_tile-0-1))
  (at end (clear_tile-1-1))
 )
)
(:durative-action _down_robot1_tile-1-2_tile-0-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-2))
   (at start (clear_tile-0-2))
  )
 :effect (and
  (at start (not (clear_tile-0-2)))
  (at start (not (robot-at_robot1_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot1_tile-0-2))
 )
)
(:durative-action _down_robot2_tile-1-2_tile-0-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-2))
   (at start (clear_tile-0-2))
  )
 :effect (and
  (at start (not (clear_tile-0-2)))
  (at start (not (robot-at_robot2_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot2_tile-0-2))
 )
)
(:durative-action _down_robot1_tile-1-3_tile-0-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-3))
   (at start (clear_tile-0-3))
  )
 :effect (and
  (at start (not (clear_tile-0-3)))
  (at start (not (robot-at_robot1_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot1_tile-0-3))
 )
)
(:durative-action _down_robot2_tile-1-3_tile-0-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-3))
   (at start (clear_tile-0-3))
  )
 :effect (and
  (at start (not (clear_tile-0-3)))
  (at start (not (robot-at_robot2_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot2_tile-0-3))
 )
)
(:durative-action _down_robot1_tile-1-4_tile-0-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-4))
   (at start (clear_tile-0-4))
  )
 :effect (and
  (at start (not (clear_tile-0-4)))
  (at start (not (robot-at_robot1_tile-1-4)))
  (at end (clear_tile-1-4))
  (at end (robot-at_robot1_tile-0-4))
 )
)
(:durative-action _down_robot2_tile-1-4_tile-0-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-4))
   (at start (clear_tile-0-4))
  )
 :effect (and
  (at start (not (clear_tile-0-4)))
  (at start (not (robot-at_robot2_tile-1-4)))
  (at end (clear_tile-1-4))
  (at end (robot-at_robot2_tile-0-4))
 )
)
(:durative-action _down_robot1_tile-2-1_tile-1-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at start (not (robot-at_robot1_tile-2-1)))
  (at end (clear_tile-2-1))
  (at end (robot-at_robot1_tile-1-1))
 )
)
(:durative-action _down_robot2_tile-2-1_tile-1-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-1))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at start (not (robot-at_robot2_tile-2-1)))
  (at end (clear_tile-2-1))
  (at end (robot-at_robot2_tile-1-1))
 )
)
(:durative-action _down_robot1_tile-2-2_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot1_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot1_tile-1-2))
 )
)
(:durative-action _down_robot2_tile-2-2_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-2))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot2_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot2_tile-1-2))
 )
)
(:durative-action _down_robot1_tile-2-3_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot1_tile-2-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot1_tile-1-3))
 )
)
(:durative-action _down_robot2_tile-2-3_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-3))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot2_tile-2-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot2_tile-1-3))
 )
)
(:durative-action _down_robot1_tile-2-4_tile-1-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at start (not (robot-at_robot1_tile-2-4)))
  (at end (clear_tile-2-4))
  (at end (robot-at_robot1_tile-1-4))
 )
)
(:durative-action _down_robot2_tile-2-4_tile-1-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-4))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at start (not (robot-at_robot2_tile-2-4)))
  (at end (clear_tile-2-4))
  (at end (robot-at_robot2_tile-1-4))
 )
)
(:durative-action _down_robot1_tile-3-1_tile-2-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at start (not (robot-at_robot1_tile-3-1)))
  (at end (clear_tile-3-1))
  (at end (robot-at_robot1_tile-2-1))
 )
)
(:durative-action _down_robot2_tile-3-1_tile-2-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-1))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at start (not (robot-at_robot2_tile-3-1)))
  (at end (clear_tile-3-1))
  (at end (robot-at_robot2_tile-2-1))
 )
)
(:durative-action _down_robot1_tile-3-2_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot1_tile-3-2)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot1_tile-2-2))
 )
)
(:durative-action _down_robot2_tile-3-2_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-2))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot2_tile-3-2)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot2_tile-2-2))
 )
)
(:durative-action _down_robot1_tile-3-3_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-3-3)))
  (at start (not (clear_tile-2-3)))
  (at end (robot-at_robot1_tile-2-3))
  (at end (clear_tile-3-3))
 )
)
(:durative-action _down_robot2_tile-3-3_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-3))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot2_tile-3-3)))
  (at end (robot-at_robot2_tile-2-3))
  (at end (clear_tile-3-3))
 )
)
(:durative-action _down_robot1_tile-3-4_tile-2-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at start (not (robot-at_robot1_tile-3-4)))
  (at end (clear_tile-3-4))
  (at end (robot-at_robot1_tile-2-4))
 )
)
(:durative-action _down_robot2_tile-3-4_tile-2-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-4))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at start (not (robot-at_robot2_tile-3-4)))
  (at end (clear_tile-3-4))
  (at end (robot-at_robot2_tile-2-4))
 )
)
(:durative-action _down_robot1_tile-4-1_tile-3-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at start (not (robot-at_robot1_tile-4-1)))
  (at end (clear_tile-4-1))
  (at end (robot-at_robot1_tile-3-1))
 )
)
(:durative-action _down_robot2_tile-4-1_tile-3-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-1))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at start (not (robot-at_robot2_tile-4-1)))
  (at end (clear_tile-4-1))
  (at end (robot-at_robot2_tile-3-1))
 )
)
(:durative-action _down_robot1_tile-4-2_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot1_tile-4-2)))
  (at end (clear_tile-4-2))
  (at end (robot-at_robot1_tile-3-2))
 )
)
(:durative-action _down_robot2_tile-4-2_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-2))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot2_tile-4-2)))
  (at end (clear_tile-4-2))
  (at end (robot-at_robot2_tile-3-2))
 )
)
(:durative-action _down_robot1_tile-4-3_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (clear_tile-3-3)))
  (at start (not (robot-at_robot1_tile-4-3)))
  (at end (robot-at_robot1_tile-3-3))
  (at end (clear_tile-4-3))
 )
)
(:durative-action _down_robot2_tile-4-3_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-3))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (clear_tile-3-3)))
  (at start (not (robot-at_robot2_tile-4-3)))
  (at end (clear_tile-4-3))
  (at end (robot-at_robot2_tile-3-3))
 )
)
(:durative-action _down_robot1_tile-4-4_tile-3-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at start (not (robot-at_robot1_tile-4-4)))
  (at end (clear_tile-4-4))
  (at end (robot-at_robot1_tile-3-4))
 )
)
(:durative-action _down_robot2_tile-4-4_tile-3-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-4))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at start (not (robot-at_robot2_tile-4-4)))
  (at end (clear_tile-4-4))
  (at end (robot-at_robot2_tile-3-4))
 )
)
(:durative-action _right_robot1_tile-0-1_tile-0-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-1))
   (at start (clear_tile-0-2))
  )
 :effect (and
  (at start (not (clear_tile-0-2)))
  (at start (not (robot-at_robot1_tile-0-1)))
  (at end (clear_tile-0-1))
  (at end (robot-at_robot1_tile-0-2))
 )
)
(:durative-action _right_robot2_tile-0-1_tile-0-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-1))
   (at start (clear_tile-0-2))
  )
 :effect (and
  (at start (not (robot-at_robot2_tile-0-1)))
  (at start (not (clear_tile-0-2)))
  (at end (clear_tile-0-1))
  (at end (robot-at_robot2_tile-0-2))
 )
)
(:durative-action _right_robot1_tile-0-2_tile-0-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-2))
   (at start (clear_tile-0-3))
  )
 :effect (and
  (at start (not (clear_tile-0-3)))
  (at start (not (robot-at_robot1_tile-0-2)))
  (at end (clear_tile-0-2))
  (at end (robot-at_robot1_tile-0-3))
 )
)
(:durative-action _right_robot2_tile-0-2_tile-0-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-2))
   (at start (clear_tile-0-3))
  )
 :effect (and
  (at start (not (clear_tile-0-3)))
  (at start (not (robot-at_robot2_tile-0-2)))
  (at end (clear_tile-0-2))
  (at end (robot-at_robot2_tile-0-3))
 )
)
(:durative-action _right_robot1_tile-0-3_tile-0-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-3))
   (at start (clear_tile-0-4))
  )
 :effect (and
  (at start (not (clear_tile-0-4)))
  (at start (not (robot-at_robot1_tile-0-3)))
  (at end (clear_tile-0-3))
  (at end (robot-at_robot1_tile-0-4))
 )
)
(:durative-action _right_robot2_tile-0-3_tile-0-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-3))
   (at start (clear_tile-0-4))
  )
 :effect (and
  (at start (not (clear_tile-0-4)))
  (at start (not (robot-at_robot2_tile-0-3)))
  (at end (clear_tile-0-3))
  (at end (robot-at_robot2_tile-0-4))
 )
)
(:durative-action _right_robot1_tile-1-1_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-1))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot1_tile-1-1)))
  (at end (clear_tile-1-1))
  (at end (robot-at_robot1_tile-1-2))
 )
)
(:durative-action _right_robot2_tile-1-1_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-1))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot2_tile-1-1)))
  (at end (clear_tile-1-1))
  (at end (robot-at_robot2_tile-1-2))
 )
)
(:durative-action _right_robot1_tile-1-2_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-2))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot1_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot1_tile-1-3))
 )
)
(:durative-action _right_robot2_tile-1-2_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-2))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot2_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot2_tile-1-3))
 )
)
(:durative-action _right_robot1_tile-1-3_tile-1-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-3))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at start (not (robot-at_robot1_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot1_tile-1-4))
 )
)
(:durative-action _right_robot2_tile-1-3_tile-1-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-3))
   (at start (clear_tile-1-4))
  )
 :effect (and
  (at start (not (clear_tile-1-4)))
  (at start (not (robot-at_robot2_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot2_tile-1-4))
 )
)
(:durative-action _right_robot1_tile-2-1_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-1))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot1_tile-2-1)))
  (at end (clear_tile-2-1))
  (at end (robot-at_robot1_tile-2-2))
 )
)
(:durative-action _right_robot2_tile-2-1_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-1))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot2_tile-2-1)))
  (at end (clear_tile-2-1))
  (at end (robot-at_robot2_tile-2-2))
 )
)
(:durative-action _right_robot1_tile-2-2_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-2))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot1_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot1_tile-2-3))
 )
)
(:durative-action _right_robot2_tile-2-2_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-2))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot2_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot2_tile-2-3))
 )
)
(:durative-action _right_robot1_tile-2-3_tile-2-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-3))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at start (not (robot-at_robot1_tile-2-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot1_tile-2-4))
 )
)
(:durative-action _right_robot2_tile-2-3_tile-2-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-3))
   (at start (clear_tile-2-4))
  )
 :effect (and
  (at start (not (clear_tile-2-4)))
  (at start (not (robot-at_robot2_tile-2-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot2_tile-2-4))
 )
)
(:durative-action _right_robot1_tile-3-1_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-1))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot1_tile-3-1)))
  (at end (clear_tile-3-1))
  (at end (robot-at_robot1_tile-3-2))
 )
)
(:durative-action _right_robot2_tile-3-1_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-1))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot2_tile-3-1)))
  (at end (clear_tile-3-1))
  (at end (robot-at_robot2_tile-3-2))
 )
)
(:durative-action _right_robot1_tile-3-2_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-2))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-3-2)))
  (at start (not (clear_tile-3-3)))
  (at end (robot-at_robot1_tile-3-3))
  (at end (clear_tile-3-2))
 )
)
(:durative-action _right_robot2_tile-3-2_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-2))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (robot-at_robot2_tile-3-2)))
  (at start (not (clear_tile-3-3)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot2_tile-3-3))
 )
)
(:durative-action _right_robot1_tile-3-3_tile-3-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-3))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-3-3)))
  (at start (not (clear_tile-3-4)))
  (at end (robot-at_robot1_tile-3-4))
  (at end (clear_tile-3-3))
 )
)
(:durative-action _right_robot2_tile-3-3_tile-3-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-3))
   (at start (clear_tile-3-4))
  )
 :effect (and
  (at start (not (clear_tile-3-4)))
  (at start (not (robot-at_robot2_tile-3-3)))
  (at end (robot-at_robot2_tile-3-4))
  (at end (clear_tile-3-3))
 )
)
(:durative-action _right_robot1_tile-4-1_tile-4-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-1))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at start (not (robot-at_robot1_tile-4-1)))
  (at end (clear_tile-4-1))
  (at end (robot-at_robot1_tile-4-2))
 )
)
(:durative-action _right_robot2_tile-4-1_tile-4-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-1))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at start (not (robot-at_robot2_tile-4-1)))
  (at end (clear_tile-4-1))
  (at end (robot-at_robot2_tile-4-2))
 )
)
(:durative-action _right_robot1_tile-4-2_tile-4-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-2))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at start (not (robot-at_robot1_tile-4-2)))
  (at end (clear_tile-4-2))
  (at end (robot-at_robot1_tile-4-3))
 )
)
(:durative-action _right_robot2_tile-4-2_tile-4-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-2))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at start (not (robot-at_robot2_tile-4-2)))
  (at end (clear_tile-4-2))
  (at end (robot-at_robot2_tile-4-3))
 )
)
(:durative-action _right_robot1_tile-4-3_tile-4-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-3))
   (at start (clear_tile-4-4))
  )
 :effect (and
  (at start (not (clear_tile-4-4)))
  (at start (not (robot-at_robot1_tile-4-3)))
  (at end (clear_tile-4-3))
  (at end (robot-at_robot1_tile-4-4))
 )
)
(:durative-action _right_robot2_tile-4-3_tile-4-4_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-3))
   (at start (clear_tile-4-4))
  )
 :effect (and
  (at start (not (clear_tile-4-4)))
  (at start (not (robot-at_robot2_tile-4-3)))
  (at end (clear_tile-4-3))
  (at end (robot-at_robot2_tile-4-4))
 )
)
(:durative-action _left_robot1_tile-0-2_tile-0-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-2))
   (at start (clear_tile-0-1))
  )
 :effect (and
  (at start (not (clear_tile-0-1)))
  (at start (not (robot-at_robot1_tile-0-2)))
  (at end (clear_tile-0-2))
  (at end (robot-at_robot1_tile-0-1))
 )
)
(:durative-action _left_robot2_tile-0-2_tile-0-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-2))
   (at start (clear_tile-0-1))
  )
 :effect (and
  (at start (not (clear_tile-0-1)))
  (at start (not (robot-at_robot2_tile-0-2)))
  (at end (robot-at_robot2_tile-0-1))
  (at end (clear_tile-0-2))
 )
)
(:durative-action _left_robot1_tile-0-3_tile-0-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-3))
   (at start (clear_tile-0-2))
  )
 :effect (and
  (at start (not (clear_tile-0-2)))
  (at start (not (robot-at_robot1_tile-0-3)))
  (at end (clear_tile-0-3))
  (at end (robot-at_robot1_tile-0-2))
 )
)
(:durative-action _left_robot2_tile-0-3_tile-0-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-3))
   (at start (clear_tile-0-2))
  )
 :effect (and
  (at start (not (clear_tile-0-2)))
  (at start (not (robot-at_robot2_tile-0-3)))
  (at end (clear_tile-0-3))
  (at end (robot-at_robot2_tile-0-2))
 )
)
(:durative-action _left_robot1_tile-0-4_tile-0-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-0-4))
   (at start (clear_tile-0-3))
  )
 :effect (and
  (at start (not (clear_tile-0-3)))
  (at start (not (robot-at_robot1_tile-0-4)))
  (at end (clear_tile-0-4))
  (at end (robot-at_robot1_tile-0-3))
 )
)
(:durative-action _left_robot2_tile-0-4_tile-0-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-0-4))
   (at start (clear_tile-0-3))
  )
 :effect (and
  (at start (not (clear_tile-0-3)))
  (at start (not (robot-at_robot2_tile-0-4)))
  (at end (clear_tile-0-4))
  (at end (robot-at_robot2_tile-0-3))
 )
)
(:durative-action _left_robot1_tile-1-2_tile-1-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-2))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at start (not (robot-at_robot1_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot1_tile-1-1))
 )
)
(:durative-action _left_robot2_tile-1-2_tile-1-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-2))
   (at start (clear_tile-1-1))
  )
 :effect (and
  (at start (not (clear_tile-1-1)))
  (at start (not (robot-at_robot2_tile-1-2)))
  (at end (clear_tile-1-2))
  (at end (robot-at_robot2_tile-1-1))
 )
)
(:durative-action _left_robot1_tile-1-3_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-3))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot1_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot1_tile-1-2))
 )
)
(:durative-action _left_robot2_tile-1-3_tile-1-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-3))
   (at start (clear_tile-1-2))
  )
 :effect (and
  (at start (not (clear_tile-1-2)))
  (at start (not (robot-at_robot2_tile-1-3)))
  (at end (clear_tile-1-3))
  (at end (robot-at_robot2_tile-1-2))
 )
)
(:durative-action _left_robot1_tile-1-4_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-1-4))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot1_tile-1-4)))
  (at end (clear_tile-1-4))
  (at end (robot-at_robot1_tile-1-3))
 )
)
(:durative-action _left_robot2_tile-1-4_tile-1-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-1-4))
   (at start (clear_tile-1-3))
  )
 :effect (and
  (at start (not (clear_tile-1-3)))
  (at start (not (robot-at_robot2_tile-1-4)))
  (at end (clear_tile-1-4))
  (at end (robot-at_robot2_tile-1-3))
 )
)
(:durative-action _left_robot1_tile-2-2_tile-2-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-2))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at start (not (robot-at_robot1_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot1_tile-2-1))
 )
)
(:durative-action _left_robot2_tile-2-2_tile-2-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-2))
   (at start (clear_tile-2-1))
  )
 :effect (and
  (at start (not (clear_tile-2-1)))
  (at start (not (robot-at_robot2_tile-2-2)))
  (at end (clear_tile-2-2))
  (at end (robot-at_robot2_tile-2-1))
 )
)
(:durative-action _left_robot1_tile-2-3_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-3))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot1_tile-2-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot1_tile-2-2))
 )
)
(:durative-action _left_robot2_tile-2-3_tile-2-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-3))
   (at start (clear_tile-2-2))
  )
 :effect (and
  (at start (not (clear_tile-2-2)))
  (at start (not (robot-at_robot2_tile-2-3)))
  (at end (clear_tile-2-3))
  (at end (robot-at_robot2_tile-2-2))
 )
)
(:durative-action _left_robot1_tile-2-4_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-2-4))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot1_tile-2-4)))
  (at end (clear_tile-2-4))
  (at end (robot-at_robot1_tile-2-3))
 )
)
(:durative-action _left_robot2_tile-2-4_tile-2-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-2-4))
   (at start (clear_tile-2-3))
  )
 :effect (and
  (at start (not (clear_tile-2-3)))
  (at start (not (robot-at_robot2_tile-2-4)))
  (at end (clear_tile-2-4))
  (at end (robot-at_robot2_tile-2-3))
 )
)
(:durative-action _left_robot1_tile-3-2_tile-3-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-2))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at start (not (robot-at_robot1_tile-3-2)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot1_tile-3-1))
 )
)
(:durative-action _left_robot2_tile-3-2_tile-3-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-2))
   (at start (clear_tile-3-1))
  )
 :effect (and
  (at start (not (clear_tile-3-1)))
  (at start (not (robot-at_robot2_tile-3-2)))
  (at end (clear_tile-3-2))
  (at end (robot-at_robot2_tile-3-1))
 )
)
(:durative-action _left_robot1_tile-3-3_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-3))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-3-3)))
  (at start (not (clear_tile-3-2)))
  (at end (robot-at_robot1_tile-3-2))
  (at end (clear_tile-3-3))
 )
)
(:durative-action _left_robot2_tile-3-3_tile-3-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-3))
   (at start (clear_tile-3-2))
  )
 :effect (and
  (at start (not (clear_tile-3-2)))
  (at start (not (robot-at_robot2_tile-3-3)))
  (at end (robot-at_robot2_tile-3-2))
  (at end (clear_tile-3-3))
 )
)
(:durative-action _left_robot1_tile-3-4_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-3-4))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (robot-at_robot1_tile-3-4)))
  (at start (not (clear_tile-3-3)))
  (at end (robot-at_robot1_tile-3-3))
  (at end (clear_tile-3-4))
 )
)
(:durative-action _left_robot2_tile-3-4_tile-3-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-3-4))
   (at start (clear_tile-3-3))
  )
 :effect (and
  (at start (not (robot-at_robot2_tile-3-4)))
  (at start (not (clear_tile-3-3)))
  (at end (clear_tile-3-4))
  (at end (robot-at_robot2_tile-3-3))
 )
)
(:durative-action _left_robot1_tile-4-2_tile-4-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-2))
   (at start (clear_tile-4-1))
  )
 :effect (and
  (at start (not (clear_tile-4-1)))
  (at start (not (robot-at_robot1_tile-4-2)))
  (at end (clear_tile-4-2))
  (at end (robot-at_robot1_tile-4-1))
 )
)
(:durative-action _left_robot2_tile-4-2_tile-4-1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-2))
   (at start (clear_tile-4-1))
  )
 :effect (and
  (at start (not (clear_tile-4-1)))
  (at start (not (robot-at_robot2_tile-4-2)))
  (at end (clear_tile-4-2))
  (at end (robot-at_robot2_tile-4-1))
 )
)
(:durative-action _left_robot1_tile-4-3_tile-4-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-3))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at start (not (robot-at_robot1_tile-4-3)))
  (at end (clear_tile-4-3))
  (at end (robot-at_robot1_tile-4-2))
 )
)
(:durative-action _left_robot2_tile-4-3_tile-4-2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-3))
   (at start (clear_tile-4-2))
  )
 :effect (and
  (at start (not (clear_tile-4-2)))
  (at start (not (robot-at_robot2_tile-4-3)))
  (at end (clear_tile-4-3))
  (at end (robot-at_robot2_tile-4-2))
 )
)
(:durative-action _left_robot1_tile-4-4_tile-4-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot1_tile-4-4))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at start (not (robot-at_robot1_tile-4-4)))
  (at end (clear_tile-4-4))
  (at end (robot-at_robot1_tile-4-3))
 )
)
(:durative-action _left_robot2_tile-4-4_tile-4-3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (robot-at_robot2_tile-4-4))
   (at start (clear_tile-4-3))
  )
 :effect (and
  (at start (not (clear_tile-4-3)))
  (at start (not (robot-at_robot2_tile-4-4)))
  (at end (clear_tile-4-4))
  (at end (robot-at_robot2_tile-4-3))
 )
)
)
