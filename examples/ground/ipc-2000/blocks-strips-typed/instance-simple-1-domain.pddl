(define (domain ground)
(:requirements :strips)
(:predicates
 (clear_a)
 (clear_b)
 (ontable_a)
 (ontable_b)
 (handempty)
 (holding_a)
 (holding_b)
 (on_a_a)
 (on_b_a)
 (on_a_b)
 (on_b_b)
)

(:action _pick-up_a_
 :parameters ()
 :precondition
  (and
   (clear_a)
   (ontable_a)
   (handempty)
  )
 :effect (and
  (not (clear_a))
  (not (ontable_a))
  (not (handempty))
  (holding_a)
 )
)
(:action _pick-up_b_
 :parameters ()
 :precondition
  (and
   (clear_b)
   (ontable_b)
   (handempty)
  )
 :effect (and
  (not (clear_b))
  (not (ontable_b))
  (not (handempty))
  (holding_b)
 )
)
(:action _put-down_a_
 :parameters ()
 :precondition
  (holding_a)
 :effect (and
  (not (holding_a))
  (clear_a)
  (ontable_a)
  (handempty)
 )
)
(:action _put-down_b_
 :parameters ()
 :precondition
  (holding_b)
 :effect (and
  (not (holding_b))
  (clear_b)
  (ontable_b)
  (handempty)
 )
)
(:action _stack_a_a_
 :parameters ()
 :precondition
  (and
   (holding_a)
   (clear_a)
  )
 :effect (and
  (not (clear_a))
  (not (holding_a))
  (clear_a)
  (handempty)
  (on_a_a)
 )
)
(:action _stack_b_a_
 :parameters ()
 :precondition
  (and
   (holding_b)
   (clear_a)
  )
 :effect (and
  (not (clear_a))
  (not (holding_b))
  (clear_b)
  (handempty)
  (on_b_a)
 )
)
(:action _stack_a_b_
 :parameters ()
 :precondition
  (and
   (holding_a)
   (clear_b)
  )
 :effect (and
  (not (clear_b))
  (not (holding_a))
  (clear_a)
  (handempty)
  (on_a_b)
 )
)
(:action _stack_b_b_
 :parameters ()
 :precondition
  (and
   (holding_b)
   (clear_b)
  )
 :effect (and
  (not (clear_b))
  (not (holding_b))
  (clear_b)
  (handempty)
  (on_b_b)
 )
)
(:action _unstack_a_a_
 :parameters ()
 :precondition
  (and
   (on_a_a)
   (clear_a)
   (handempty)
  )
 :effect (and
  (not (clear_a))
  (not (handempty))
  (not (on_a_a))
  (clear_a)
  (holding_a)
 )
)
(:action _unstack_b_a_
 :parameters ()
 :precondition
  (and
   (on_b_a)
   (clear_b)
   (handempty)
  )
 :effect (and
  (not (clear_b))
  (not (handempty))
  (not (on_b_a))
  (clear_a)
  (holding_b)
 )
)
(:action _unstack_a_b_
 :parameters ()
 :precondition
  (and
   (on_a_b)
   (clear_a)
   (handempty)
  )
 :effect (and
  (not (clear_a))
  (not (handempty))
  (not (on_a_b))
  (clear_b)
  (holding_a)
 )
)
(:action _unstack_b_b_
 :parameters ()
 :precondition
  (and
   (on_b_b)
   (clear_b)
   (handempty)
  )
 :effect (and
  (not (clear_b))
  (not (handempty))
  (not (on_b_b))
  (clear_b)
  (holding_b)
 )
)
)
