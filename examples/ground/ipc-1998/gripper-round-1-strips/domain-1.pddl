(define (domain ground)
(:requirements :strips)
(:predicates
 (at-robby_rooma)
 (free_left)
 (free_right)
 (at_ball4_rooma)
 (at_ball3_rooma)
 (at_ball2_rooma)
 (at_ball1_rooma)
 (at-robby_roomb)
 (carry_ball1_left)
 (carry_ball2_left)
 (carry_ball3_left)
 (carry_ball4_left)
 (carry_ball1_right)
 (carry_ball2_right)
 (carry_ball3_right)
 (carry_ball4_right)
 (at_ball1_roomb)
 (at_ball2_roomb)
 (at_ball3_roomb)
 (at_ball4_roomb)
)

(:action _move_rooma_rooma_
 :parameters ()
 :precondition
  (at-robby_rooma)
 :effect (and
  (not (at-robby_rooma))
  (at-robby_rooma)
 )
)
(:action _move_roomb_rooma_
 :parameters ()
 :precondition
  (at-robby_roomb)
 :effect (and
  (not (at-robby_roomb))
  (at-robby_rooma)
 )
)
(:action _move_rooma_roomb_
 :parameters ()
 :precondition
  (at-robby_rooma)
 :effect (and
  (not (at-robby_rooma))
  (at-robby_roomb)
 )
)
(:action _move_roomb_roomb_
 :parameters ()
 :precondition
  (at-robby_roomb)
 :effect (and
  (not (at-robby_roomb))
  (at-robby_roomb)
 )
)
(:action _pick_ball1_rooma_left_
 :parameters ()
 :precondition
  (and
   (at_ball1_rooma)
   (at-robby_rooma)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball1_rooma))
  (carry_ball1_left)
 )
)
(:action _pick_ball2_rooma_left_
 :parameters ()
 :precondition
  (and
   (at_ball2_rooma)
   (at-robby_rooma)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball2_rooma))
  (carry_ball2_left)
 )
)
(:action _pick_ball3_rooma_left_
 :parameters ()
 :precondition
  (and
   (at_ball3_rooma)
   (at-robby_rooma)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball3_rooma))
  (carry_ball3_left)
 )
)
(:action _pick_ball4_rooma_left_
 :parameters ()
 :precondition
  (and
   (at_ball4_rooma)
   (at-robby_rooma)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball4_rooma))
  (carry_ball4_left)
 )
)
(:action _pick_ball1_roomb_left_
 :parameters ()
 :precondition
  (and
   (at_ball1_roomb)
   (at-robby_roomb)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball1_roomb))
  (carry_ball1_left)
 )
)
(:action _pick_ball2_roomb_left_
 :parameters ()
 :precondition
  (and
   (at_ball2_roomb)
   (at-robby_roomb)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball2_roomb))
  (carry_ball2_left)
 )
)
(:action _pick_ball3_roomb_left_
 :parameters ()
 :precondition
  (and
   (at_ball3_roomb)
   (at-robby_roomb)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball3_roomb))
  (carry_ball3_left)
 )
)
(:action _pick_ball4_roomb_left_
 :parameters ()
 :precondition
  (and
   (at_ball4_roomb)
   (at-robby_roomb)
   (free_left)
  )
 :effect (and
  (not (free_left))
  (not (at_ball4_roomb))
  (carry_ball4_left)
 )
)
(:action _pick_ball1_rooma_right_
 :parameters ()
 :precondition
  (and
   (at_ball1_rooma)
   (at-robby_rooma)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball1_rooma))
  (carry_ball1_right)
 )
)
(:action _pick_ball2_rooma_right_
 :parameters ()
 :precondition
  (and
   (at_ball2_rooma)
   (at-robby_rooma)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball2_rooma))
  (carry_ball2_right)
 )
)
(:action _pick_ball3_rooma_right_
 :parameters ()
 :precondition
  (and
   (at_ball3_rooma)
   (at-robby_rooma)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball3_rooma))
  (carry_ball3_right)
 )
)
(:action _pick_ball4_rooma_right_
 :parameters ()
 :precondition
  (and
   (at_ball4_rooma)
   (at-robby_rooma)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball4_rooma))
  (carry_ball4_right)
 )
)
(:action _pick_ball1_roomb_right_
 :parameters ()
 :precondition
  (and
   (at_ball1_roomb)
   (at-robby_roomb)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball1_roomb))
  (carry_ball1_right)
 )
)
(:action _pick_ball2_roomb_right_
 :parameters ()
 :precondition
  (and
   (at_ball2_roomb)
   (at-robby_roomb)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball2_roomb))
  (carry_ball2_right)
 )
)
(:action _pick_ball3_roomb_right_
 :parameters ()
 :precondition
  (and
   (at_ball3_roomb)
   (at-robby_roomb)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball3_roomb))
  (carry_ball3_right)
 )
)
(:action _pick_ball4_roomb_right_
 :parameters ()
 :precondition
  (and
   (at_ball4_roomb)
   (at-robby_roomb)
   (free_right)
  )
 :effect (and
  (not (free_right))
  (not (at_ball4_roomb))
  (carry_ball4_right)
 )
)
(:action _drop_ball1_rooma_left_
 :parameters ()
 :precondition
  (and
   (carry_ball1_left)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball1_left))
  (free_left)
  (at_ball1_rooma)
 )
)
(:action _drop_ball2_rooma_left_
 :parameters ()
 :precondition
  (and
   (carry_ball2_left)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball2_left))
  (free_left)
  (at_ball2_rooma)
 )
)
(:action _drop_ball3_rooma_left_
 :parameters ()
 :precondition
  (and
   (carry_ball3_left)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball3_left))
  (free_left)
  (at_ball3_rooma)
 )
)
(:action _drop_ball4_rooma_left_
 :parameters ()
 :precondition
  (and
   (carry_ball4_left)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball4_left))
  (free_left)
  (at_ball4_rooma)
 )
)
(:action _drop_ball1_roomb_left_
 :parameters ()
 :precondition
  (and
   (carry_ball1_left)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball1_left))
  (free_left)
  (at_ball1_roomb)
 )
)
(:action _drop_ball2_roomb_left_
 :parameters ()
 :precondition
  (and
   (carry_ball2_left)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball2_left))
  (free_left)
  (at_ball2_roomb)
 )
)
(:action _drop_ball3_roomb_left_
 :parameters ()
 :precondition
  (and
   (carry_ball3_left)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball3_left))
  (free_left)
  (at_ball3_roomb)
 )
)
(:action _drop_ball4_roomb_left_
 :parameters ()
 :precondition
  (and
   (carry_ball4_left)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball4_left))
  (free_left)
  (at_ball4_roomb)
 )
)
(:action _drop_ball1_rooma_right_
 :parameters ()
 :precondition
  (and
   (carry_ball1_right)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball1_right))
  (free_right)
  (at_ball1_rooma)
 )
)
(:action _drop_ball2_rooma_right_
 :parameters ()
 :precondition
  (and
   (carry_ball2_right)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball2_right))
  (free_right)
  (at_ball2_rooma)
 )
)
(:action _drop_ball3_rooma_right_
 :parameters ()
 :precondition
  (and
   (carry_ball3_right)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball3_right))
  (free_right)
  (at_ball3_rooma)
 )
)
(:action _drop_ball4_rooma_right_
 :parameters ()
 :precondition
  (and
   (carry_ball4_right)
   (at-robby_rooma)
  )
 :effect (and
  (not (carry_ball4_right))
  (free_right)
  (at_ball4_rooma)
 )
)
(:action _drop_ball1_roomb_right_
 :parameters ()
 :precondition
  (and
   (carry_ball1_right)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball1_right))
  (free_right)
  (at_ball1_roomb)
 )
)
(:action _drop_ball2_roomb_right_
 :parameters ()
 :precondition
  (and
   (carry_ball2_right)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball2_right))
  (free_right)
  (at_ball2_roomb)
 )
)
(:action _drop_ball3_roomb_right_
 :parameters ()
 :precondition
  (and
   (carry_ball3_right)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball3_right))
  (free_right)
  (at_ball3_roomb)
 )
)
(:action _drop_ball4_roomb_right_
 :parameters ()
 :precondition
  (and
   (carry_ball4_right)
   (at-robby_roomb)
  )
 :effect (and
  (not (carry_ball4_right))
  (free_right)
  (at_ball4_roomb)
 )
)
)
