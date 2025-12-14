(define (domain ground)
(:requirements :strips)
(:predicates
 (on-table_a)
 (on-table_b)
 (clear_a)
 (clear_b)
 (arm-empty)
 (holding_a)
 (holding_b)
 (on_a_a)
 (on_b_a)
 (on_a_b)
 (on_b_b)
)

(:durative-action _pickup_a_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (over all (arm-empty))
   (at start (on-table_a))
   (at start (clear_a))
  )
 :effect (and
  (at start (not (on-table_a)))
  (at start (not (clear_a)))
  (at start (not (arm-empty)))
  (at end (holding_a))
 )
)
(:durative-action _pickup_b_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (over all (arm-empty))
   (at start (on-table_b))
   (at start (clear_b))
  )
 :effect (and
  (at start (not (on-table_b)))
  (at start (not (clear_b)))
  (at start (not (arm-empty)))
  (at end (holding_b))
 )
)
(:durative-action _putdown_a_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (at start (holding_a))
 :effect (and
  (at start (not (holding_a)))
  (at end (on-table_a))
  (at end (clear_a))
  (at end (arm-empty))
 )
)
(:durative-action _putdown_b_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (at start (holding_b))
 :effect (and
  (at start (not (holding_b)))
  (at end (on-table_b))
  (at end (clear_b))
  (at end (arm-empty))
 )
)
(:durative-action _stack_a_a_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (over all (holding_a))
   (at start (clear_a))
  )
 :effect (and
  (at end (not (clear_a)))
  (at end (not (holding_a)))
  (at end (clear_a))
  (at end (arm-empty))
  (at end (on_a_a))
 )
)
(:durative-action _stack_b_a_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (over all (holding_b))
   (at start (clear_a))
  )
 :effect (and
  (at end (not (clear_a)))
  (at end (not (holding_b)))
  (at end (clear_b))
  (at end (arm-empty))
  (at end (on_b_a))
 )
)
(:durative-action _stack_a_b_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (over all (holding_a))
   (at start (clear_b))
  )
 :effect (and
  (at end (not (clear_b)))
  (at end (not (holding_a)))
  (at end (clear_a))
  (at end (arm-empty))
  (at end (on_a_b))
 )
)
(:durative-action _stack_b_b_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (over all (holding_b))
   (at start (clear_b))
  )
 :effect (and
  (at end (not (clear_b)))
  (at end (not (holding_b)))
  (at end (clear_b))
  (at end (arm-empty))
  (at end (on_b_b))
 )
)
(:durative-action _unstack_a_a_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (on_a_a))
   (at start (clear_a))
   (at start (arm-empty))
  )
 :effect (and
  (at start (not (clear_a)))
  (at start (not (arm-empty)))
  (at start (not (on_a_a)))
  (at end (clear_a))
  (at end (holding_a))
 )
)
(:durative-action _unstack_b_a_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (on_b_a))
   (at start (clear_b))
   (at start (arm-empty))
  )
 :effect (and
  (at start (not (clear_b)))
  (at start (not (arm-empty)))
  (at start (not (on_b_a)))
  (at end (clear_a))
  (at end (holding_b))
 )
)
(:durative-action _unstack_a_b_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (on_a_b))
   (at start (clear_a))
   (at start (arm-empty))
  )
 :effect (and
  (at start (not (clear_a)))
  (at start (not (arm-empty)))
  (at start (not (on_a_b)))
  (at end (clear_b))
  (at end (holding_a))
 )
)
(:durative-action _unstack_b_b_
 :parameters ()
 :duration
  (and
   (>= ?duration 1)
   (<= ?duration 1)
  )
 :condition
  (and
   (at start (on_b_b))
   (at start (clear_b))
   (at start (arm-empty))
  )
 :effect (and
  (at start (not (clear_b)))
  (at start (not (arm-empty)))
  (at start (not (on_b_b)))
  (at end (clear_b))
  (at end (holding_b))
 )
)
)
