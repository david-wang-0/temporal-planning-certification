(define (domain ground)
(:requirements :strips)
(:predicates
 (at-robby_rooma)
 (free_right)
 (at_ball1_rooma)
 (at-robby_roomb)
 (carry_ball1_right)
 (at_ball1_roomb)
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
)
