(define (domain ground)
(:requirements :strips)
(:predicates
 (robot_at_r0_p4)
 (robot_free_r0)
 (battery_level_r0_five)
 (pallet_at_b0_p4)
 (pallet_at_b1_p4)
 (position_free_p4)
 (robot_at_r0_p0)
 (battery_level_r0_four)
 (robot_at_r0_p1)
 (robot_at_r0_p2)
 (robot_at_r0_p3)
 (battery_level_r0_three)
 (battery_level_r0_zero)
 (battery_level_r0_two)
 (battery_level_r0_one)
 (robot_has_r0_b0)
 (robot_has_r0_b1)
 (unload_ended_b0_p0_t0)
 (unload_started_b0_p0_t0)
 (pallet_at_b0_p0)
 (unload_ended_b1_p0_t0)
 (unload_started_b1_p0_t0)
 (pallet_at_b1_p0)
 (unload_ended_b0_p1_t1)
 (unload_started_b0_p1_t1)
 (pallet_at_b0_p1)
 (unload_ended_b1_p1_t1)
 (unload_started_b1_p1_t1)
 (pallet_at_b1_p1)
 (unload_max_timeout_can_start_b0_p0_t0)
 (unload_min_timeout_can_start_b0_p0_t0)
 (unload_clip_started_b0_p0_t0)
 (unload_max_timeout_can_start_b1_p0_t0)
 (unload_min_timeout_can_start_b1_p0_t0)
 (unload_clip_started_b1_p0_t0)
 (unload_max_timeout_can_start_b0_p1_t1)
 (unload_min_timeout_can_start_b0_p1_t1)
 (unload_clip_started_b0_p1_t1)
 (unload_max_timeout_can_start_b1_p1_t1)
 (unload_min_timeout_can_start_b1_p1_t1)
 (unload_clip_started_b1_p1_t1)
 (ready_b0_p0_t0)
 (unload_min_timeout_started_b0_p0_t0)
 (ready_b1_p0_t0)
 (unload_min_timeout_started_b1_p0_t0)
 (ready_b0_p1_t1)
 (unload_min_timeout_started_b0_p1_t1)
 (ready_b1_p1_t1)
 (unload_min_timeout_started_b1_p1_t1)
 (unload_max_timeout_started_b0_p0_t0)
 (unload_max_timeout_started_b1_p0_t0)
 (unload_max_timeout_started_b0_p1_t1)
 (unload_max_timeout_started_b1_p1_t1)
 (treated_b0_t0)
 (position_free_p0)
 (treated_b1_t0)
 (treated_b0_t1)
 (position_free_p1)
 (treated_b1_t1)
)

(:action _move_r0_p1_p0_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p1))
  (robot_at_r0_p0)
  (battery_level_r0_four)
 )
)
(:action _move_r0_p0_p1_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p0))
  (battery_level_r0_four)
  (robot_at_r0_p1)
 )
)
(:action _move_r0_p2_p1_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p2))
  (battery_level_r0_four)
  (robot_at_r0_p1)
 )
)
(:action _move_r0_p1_p2_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p1))
  (battery_level_r0_four)
  (robot_at_r0_p2)
 )
)
(:action _move_r0_p3_p2_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p3))
  (battery_level_r0_four)
  (robot_at_r0_p2)
 )
)
(:action _move_r0_p2_p3_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p2))
  (battery_level_r0_four)
  (robot_at_r0_p3)
 )
)
(:action _move_r0_p4_p3_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_five)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_five))
  (battery_level_r0_four)
  (robot_at_r0_p3)
 )
)
(:action _move_r0_p3_p4_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_five)
  )
 :effect (and
  (not (battery_level_r0_five))
  (not (robot_at_r0_p3))
  (robot_at_r0_p4)
  (battery_level_r0_four)
 )
)
(:action _move_r0_p1_p0_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_four)
  )
 :effect (and
  (not (battery_level_r0_four))
  (not (robot_at_r0_p1))
  (robot_at_r0_p0)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p0_p1_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_four)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_four))
  (robot_at_r0_p1)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p2_p1_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_four)
  )
 :effect (and
  (not (battery_level_r0_four))
  (not (robot_at_r0_p2))
  (robot_at_r0_p1)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p1_p2_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_four)
  )
 :effect (and
  (not (battery_level_r0_four))
  (not (robot_at_r0_p1))
  (robot_at_r0_p2)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p3_p2_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_four)
  )
 :effect (and
  (not (battery_level_r0_four))
  (not (robot_at_r0_p3))
  (robot_at_r0_p2)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p2_p3_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_four)
  )
 :effect (and
  (not (battery_level_r0_four))
  (not (robot_at_r0_p2))
  (robot_at_r0_p3)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p4_p3_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_four)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_four))
  (robot_at_r0_p3)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p3_p4_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_four)
  )
 :effect (and
  (not (battery_level_r0_four))
  (not (robot_at_r0_p3))
  (robot_at_r0_p4)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p1_p0_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_one))
  (robot_at_r0_p0)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p0_p1_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_one))
  (robot_at_r0_p1)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p2_p1_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_one))
  (robot_at_r0_p1)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p1_p2_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_one))
  (robot_at_r0_p2)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p3_p2_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_one))
  (robot_at_r0_p2)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p2_p3_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_one))
  (robot_at_r0_p3)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p4_p3_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_one))
  (robot_at_r0_p3)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p3_p4_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_one))
  (robot_at_r0_p4)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p1_p0_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_three))
  (robot_at_r0_p0)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p0_p1_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_three))
  (robot_at_r0_p1)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p2_p1_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_three))
  (robot_at_r0_p1)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p1_p2_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_three))
  (robot_at_r0_p2)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p3_p2_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_three))
  (robot_at_r0_p2)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p2_p3_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_three))
  (robot_at_r0_p3)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p4_p3_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_three))
  (robot_at_r0_p3)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p3_p4_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_three))
  (robot_at_r0_p4)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p1_p0_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_two))
  (robot_at_r0_p0)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p0_p1_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_two))
  (robot_at_r0_p1)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p2_p1_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_two))
  (robot_at_r0_p1)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p1_p2_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_two))
  (robot_at_r0_p2)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p3_p2_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_two))
  (robot_at_r0_p2)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p2_p3_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_two))
  (robot_at_r0_p3)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p4_p3_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_two))
  (robot_at_r0_p3)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p3_p4_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_two))
  (robot_at_r0_p4)
  (battery_level_r0_one)
 )
)
(:action _unload_at_depot_r0_b0_p4_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (robot_has_r0_b0)
  )
 :effect (and
  (not (robot_has_r0_b0))
  (robot_free_r0)
  (pallet_at_b0_p4)
 )
)
(:action _unload_at_depot_r0_b1_p4_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (robot_has_r0_b1)
  )
 :effect (and
  (not (robot_has_r0_b1))
  (robot_free_r0)
  (pallet_at_b1_p4)
 )
)
(:action _load_from_depot_r0_b0_p4_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (robot_free_r0)
   (pallet_at_b0_p4)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b0_p4))
  (robot_has_r0_b0)
 )
)
(:action _load_from_depot_r0_b1_p4_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (robot_free_r0)
   (pallet_at_b1_p4)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b1_p4))
  (robot_has_r0_b1)
 )
)
(:durative-action _unload_r0_b0_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p0))
   (at start (robot_at_r0_p0))
   (at start (robot_has_r0_b0))
   (at end (unload_clip_started_b0_p0_t0))
  )
 :effect (and
  (at start (not (robot_has_r0_b0)))
  (at start (not (position_free_p0)))
  (at start (unload_started_b0_p0_t0))
  (at end (robot_free_r0))
  (at end (unload_ended_b0_p0_t0))
  (at end (pallet_at_b0_p0))
 )
)
(:durative-action _unload_r0_b1_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p0))
   (at start (robot_at_r0_p0))
   (at start (robot_has_r0_b1))
   (at end (unload_clip_started_b1_p0_t0))
  )
 :effect (and
  (at start (not (robot_has_r0_b1)))
  (at start (not (position_free_p0)))
  (at start (unload_started_b1_p0_t0))
  (at end (robot_free_r0))
  (at end (unload_ended_b1_p0_t0))
  (at end (pallet_at_b1_p0))
 )
)
(:durative-action _unload_r0_b0_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p1))
   (at start (robot_at_r0_p1))
   (at start (robot_has_r0_b0))
   (at end (unload_clip_started_b0_p1_t1))
  )
 :effect (and
  (at start (not (robot_has_r0_b0)))
  (at start (not (position_free_p1)))
  (at start (unload_started_b0_p1_t1))
  (at end (robot_free_r0))
  (at end (unload_ended_b0_p1_t1))
  (at end (pallet_at_b0_p1))
 )
)
(:durative-action _unload_r0_b1_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p1))
   (at start (robot_at_r0_p1))
   (at start (robot_has_r0_b1))
   (at end (unload_clip_started_b1_p1_t1))
  )
 :effect (and
  (at start (not (robot_has_r0_b1)))
  (at start (not (position_free_p1)))
  (at start (unload_started_b1_p1_t1))
  (at end (robot_free_r0))
  (at end (unload_ended_b1_p1_t1))
  (at end (pallet_at_b1_p1))
 )
)
(:durative-action _unload_clip_b0_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b0_p0_t0))
   (at end (unload_ended_b0_p0_t0))
   (at end (unload_min_timeout_started_b0_p0_t0))
   (at end (unload_max_timeout_started_b0_p0_t0))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b0_p0_t0))
  (at start (unload_min_timeout_can_start_b0_p0_t0))
  (at start (unload_clip_started_b0_p0_t0))
  (at end (not (unload_min_timeout_started_b0_p0_t0)))
  (at end (not (unload_max_timeout_started_b0_p0_t0)))
 )
)
(:durative-action _unload_clip_b1_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b1_p0_t0))
   (at end (unload_ended_b1_p0_t0))
   (at end (unload_min_timeout_started_b1_p0_t0))
   (at end (unload_max_timeout_started_b1_p0_t0))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b1_p0_t0))
  (at start (unload_min_timeout_can_start_b1_p0_t0))
  (at start (unload_clip_started_b1_p0_t0))
  (at end (not (unload_min_timeout_started_b1_p0_t0)))
  (at end (not (unload_max_timeout_started_b1_p0_t0)))
 )
)
(:durative-action _unload_clip_b0_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b0_p1_t1))
   (at end (unload_ended_b0_p1_t1))
   (at end (unload_min_timeout_started_b0_p1_t1))
   (at end (unload_max_timeout_started_b0_p1_t1))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b0_p1_t1))
  (at start (unload_min_timeout_can_start_b0_p1_t1))
  (at start (unload_clip_started_b0_p1_t1))
  (at end (not (unload_min_timeout_started_b0_p1_t1)))
  (at end (not (unload_max_timeout_started_b0_p1_t1)))
 )
)
(:durative-action _unload_clip_b1_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b1_p1_t1))
   (at end (unload_ended_b1_p1_t1))
   (at end (unload_min_timeout_started_b1_p1_t1))
   (at end (unload_max_timeout_started_b1_p1_t1))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b1_p1_t1))
  (at start (unload_min_timeout_can_start_b1_p1_t1))
  (at start (unload_clip_started_b1_p1_t1))
  (at end (not (unload_min_timeout_started_b1_p1_t1)))
  (at end (not (unload_max_timeout_started_b1_p1_t1)))
 )
)
(:durative-action _unload_min_timeout_b0_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b0_p0_t0))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b0_p0_t0)))
  (at start (unload_min_timeout_started_b0_p0_t0))
  (at end (ready_b0_p0_t0))
 )
)
(:durative-action _unload_min_timeout_b1_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b1_p0_t0))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b1_p0_t0)))
  (at start (unload_min_timeout_started_b1_p0_t0))
  (at end (ready_b1_p0_t0))
 )
)
(:durative-action _unload_min_timeout_b0_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b0_p1_t1))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b0_p1_t1)))
  (at start (unload_min_timeout_started_b0_p1_t1))
  (at end (ready_b0_p1_t1))
 )
)
(:durative-action _unload_min_timeout_b1_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b1_p1_t1))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b1_p1_t1)))
  (at start (unload_min_timeout_started_b1_p1_t1))
  (at end (ready_b1_p1_t1))
 )
)
(:durative-action _unload_max_timeout_b0_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b0_p0_t0))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b0_p0_t0)))
  (at start (unload_max_timeout_started_b0_p0_t0))
  (at end (not (ready_b0_p0_t0)))
 )
)
(:durative-action _unload_max_timeout_b1_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b1_p0_t0))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b1_p0_t0)))
  (at start (unload_max_timeout_started_b1_p0_t0))
  (at end (not (ready_b1_p0_t0)))
 )
)
(:durative-action _unload_max_timeout_b0_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b0_p1_t1))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b0_p1_t1)))
  (at start (unload_max_timeout_started_b0_p1_t1))
  (at end (not (ready_b0_p1_t1)))
 )
)
(:durative-action _unload_max_timeout_b1_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b1_p1_t1))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b1_p1_t1)))
  (at start (unload_max_timeout_started_b1_p1_t1))
  (at end (not (ready_b1_p1_t1)))
 )
)
(:action _load_r0_b0_p0_t0_
 :parameters ()
 :precondition
  (and
   (pallet_at_b0_p0)
   (robot_free_r0)
   (robot_at_r0_p0)
   (ready_b0_p0_t0)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b0_p0))
  (not (ready_b0_p0_t0))
  (robot_has_r0_b0)
  (treated_b0_t0)
  (position_free_p0)
 )
)
(:action _load_r0_b1_p0_t0_
 :parameters ()
 :precondition
  (and
   (pallet_at_b1_p0)
   (robot_free_r0)
   (robot_at_r0_p0)
   (ready_b1_p0_t0)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b1_p0))
  (not (ready_b1_p0_t0))
  (robot_has_r0_b1)
  (position_free_p0)
  (treated_b1_t0)
 )
)
(:action _load_r0_b0_p1_t1_
 :parameters ()
 :precondition
  (and
   (pallet_at_b0_p1)
   (robot_free_r0)
   (robot_at_r0_p1)
   (ready_b0_p1_t1)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b0_p1))
  (not (ready_b0_p1_t1))
  (robot_has_r0_b0)
  (treated_b0_t1)
  (position_free_p1)
 )
)
(:action _load_r0_b1_p1_t1_
 :parameters ()
 :precondition
  (and
   (pallet_at_b1_p1)
   (robot_free_r0)
   (robot_at_r0_p1)
   (ready_b1_p1_t1)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b1_p1))
  (not (ready_b1_p1_t1))
  (robot_has_r0_b1)
  (position_free_p1)
  (treated_b1_t1)
 )
)
)
