(define (domain ground)
(:requirements :strips)
(:predicates
 (robot_at_r0_p5)
 (robot_free_r0)
 (battery_level_r0_sixteen)
 (pallet_at_b0_p5)
 (pallet_at_b1_p5)
 (pallet_at_b2_p5)
 (position_free_p5)
 (robot_at_r0_p0)
 (battery_level_r0_seven)
 (robot_at_r0_p1)
 (robot_at_r0_p2)
 (robot_at_r0_p3)
 (robot_at_r0_p4)
 (battery_level_r0_ten)
 (battery_level_r0_fourteen)
 (battery_level_r0_four)
 (battery_level_r0_three)
 (battery_level_r0_thirteen)
 (battery_level_r0_eight)
 (battery_level_r0_zero)
 (battery_level_r0_six)
 (battery_level_r0_five)
 (battery_level_r0_fifteen)
 (battery_level_r0_nine)
 (battery_level_r0_twelve)
 (battery_level_r0_two)
 (battery_level_r0_eleven)
 (battery_level_r0_one)
 (robot_has_r0_b0)
 (robot_has_r0_b1)
 (robot_has_r0_b2)
 (unload_ended_b0_p0_t0)
 (unload_started_b0_p0_t0)
 (pallet_at_b0_p0)
 (unload_ended_b1_p0_t0)
 (unload_started_b1_p0_t0)
 (pallet_at_b1_p0)
 (unload_ended_b2_p0_t0)
 (unload_started_b2_p0_t0)
 (pallet_at_b2_p0)
 (unload_ended_b0_p1_t1)
 (unload_started_b0_p1_t1)
 (pallet_at_b0_p1)
 (unload_ended_b1_p1_t1)
 (unload_started_b1_p1_t1)
 (pallet_at_b1_p1)
 (unload_ended_b2_p1_t1)
 (unload_started_b2_p1_t1)
 (pallet_at_b2_p1)
 (unload_ended_b0_p2_t2)
 (unload_started_b0_p2_t2)
 (pallet_at_b0_p2)
 (unload_ended_b1_p2_t2)
 (unload_started_b1_p2_t2)
 (pallet_at_b1_p2)
 (unload_ended_b2_p2_t2)
 (unload_started_b2_p2_t2)
 (pallet_at_b2_p2)
 (unload_ended_b0_p3_t3)
 (unload_started_b0_p3_t3)
 (pallet_at_b0_p3)
 (unload_ended_b1_p3_t3)
 (unload_started_b1_p3_t3)
 (pallet_at_b1_p3)
 (unload_ended_b2_p3_t3)
 (unload_started_b2_p3_t3)
 (pallet_at_b2_p3)
 (unload_max_timeout_can_start_b0_p0_t0)
 (unload_min_timeout_can_start_b0_p0_t0)
 (unload_clip_started_b0_p0_t0)
 (unload_max_timeout_can_start_b1_p0_t0)
 (unload_min_timeout_can_start_b1_p0_t0)
 (unload_clip_started_b1_p0_t0)
 (unload_max_timeout_can_start_b2_p0_t0)
 (unload_min_timeout_can_start_b2_p0_t0)
 (unload_clip_started_b2_p0_t0)
 (unload_max_timeout_can_start_b0_p1_t1)
 (unload_min_timeout_can_start_b0_p1_t1)
 (unload_clip_started_b0_p1_t1)
 (unload_max_timeout_can_start_b1_p1_t1)
 (unload_min_timeout_can_start_b1_p1_t1)
 (unload_clip_started_b1_p1_t1)
 (unload_max_timeout_can_start_b2_p1_t1)
 (unload_min_timeout_can_start_b2_p1_t1)
 (unload_clip_started_b2_p1_t1)
 (unload_max_timeout_can_start_b0_p2_t2)
 (unload_min_timeout_can_start_b0_p2_t2)
 (unload_clip_started_b0_p2_t2)
 (unload_max_timeout_can_start_b1_p2_t2)
 (unload_min_timeout_can_start_b1_p2_t2)
 (unload_clip_started_b1_p2_t2)
 (unload_max_timeout_can_start_b2_p2_t2)
 (unload_min_timeout_can_start_b2_p2_t2)
 (unload_clip_started_b2_p2_t2)
 (unload_max_timeout_can_start_b0_p3_t3)
 (unload_min_timeout_can_start_b0_p3_t3)
 (unload_clip_started_b0_p3_t3)
 (unload_max_timeout_can_start_b1_p3_t3)
 (unload_min_timeout_can_start_b1_p3_t3)
 (unload_clip_started_b1_p3_t3)
 (unload_max_timeout_can_start_b2_p3_t3)
 (unload_min_timeout_can_start_b2_p3_t3)
 (unload_clip_started_b2_p3_t3)
 (ready_b0_p0_t0)
 (unload_min_timeout_started_b0_p0_t0)
 (ready_b1_p0_t0)
 (unload_min_timeout_started_b1_p0_t0)
 (ready_b2_p0_t0)
 (unload_min_timeout_started_b2_p0_t0)
 (ready_b0_p1_t1)
 (unload_min_timeout_started_b0_p1_t1)
 (ready_b1_p1_t1)
 (unload_min_timeout_started_b1_p1_t1)
 (ready_b2_p1_t1)
 (unload_min_timeout_started_b2_p1_t1)
 (ready_b0_p2_t2)
 (unload_min_timeout_started_b0_p2_t2)
 (ready_b1_p2_t2)
 (unload_min_timeout_started_b1_p2_t2)
 (ready_b2_p2_t2)
 (unload_min_timeout_started_b2_p2_t2)
 (ready_b0_p3_t3)
 (unload_min_timeout_started_b0_p3_t3)
 (ready_b1_p3_t3)
 (unload_min_timeout_started_b1_p3_t3)
 (ready_b2_p3_t3)
 (unload_min_timeout_started_b2_p3_t3)
 (unload_max_timeout_started_b0_p0_t0)
 (unload_max_timeout_started_b1_p0_t0)
 (unload_max_timeout_started_b2_p0_t0)
 (unload_max_timeout_started_b0_p1_t1)
 (unload_max_timeout_started_b1_p1_t1)
 (unload_max_timeout_started_b2_p1_t1)
 (unload_max_timeout_started_b0_p2_t2)
 (unload_max_timeout_started_b1_p2_t2)
 (unload_max_timeout_started_b2_p2_t2)
 (unload_max_timeout_started_b0_p3_t3)
 (unload_max_timeout_started_b1_p3_t3)
 (unload_max_timeout_started_b2_p3_t3)
 (treated_b0_t0)
 (position_free_p0)
 (treated_b1_t0)
 (treated_b2_t0)
 (treated_b0_t1)
 (position_free_p1)
 (treated_b1_t1)
 (treated_b2_t1)
 (treated_b0_t2)
 (position_free_p2)
 (treated_b1_t2)
 (treated_b2_t2)
 (treated_b0_t3)
 (position_free_p3)
 (treated_b1_t3)
 (treated_b2_t3)
)

(:action _move_r0_p1_p0_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_eight))
  (robot_at_r0_p0)
  (battery_level_r0_seven)
 )
)
(:action _move_r0_p0_p1_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p1)
 )
)
(:action _move_r0_p2_p1_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p1)
 )
)
(:action _move_r0_p1_p2_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p2)
 )
)
(:action _move_r0_p3_p2_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p2)
 )
)
(:action _move_r0_p2_p3_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p3)
 )
)
(:action _move_r0_p4_p3_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p3)
 )
)
(:action _move_r0_p3_p4_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p4)
 )
)
(:action _move_r0_p5_p4_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_eight))
  (battery_level_r0_seven)
  (robot_at_r0_p4)
 )
)
(:action _move_r0_p4_p5_seven_eight_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_eight)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_eight))
  (robot_at_r0_p5)
  (battery_level_r0_seven)
 )
)
(:action _move_r0_p1_p0_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p0)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p0_p1_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p1)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p2_p1_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p1)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p1_p2_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p2)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p3_p2_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p2)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p2_p3_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p3)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p4_p3_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p3)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p3_p4_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p4)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p5_p4_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p4)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p4_p5_ten_eleven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_eleven)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_eleven))
  (robot_at_r0_p5)
  (battery_level_r0_ten)
 )
)
(:action _move_r0_p1_p0_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p0)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p0_p1_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p1)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p2_p1_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p1)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p1_p2_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p2)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p3_p2_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p2)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p2_p3_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p3)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p4_p3_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p3)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p3_p4_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p4)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p5_p4_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p4)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p4_p5_fourteen_fifteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_fifteen)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_fifteen))
  (robot_at_r0_p5)
  (battery_level_r0_fourteen)
 )
)
(:action _move_r0_p1_p0_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_five)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_five))
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
  (not (robot_at_r0_p0))
  (not (battery_level_r0_five))
  (robot_at_r0_p1)
  (battery_level_r0_four)
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
  (not (robot_at_r0_p2))
  (not (battery_level_r0_five))
  (robot_at_r0_p1)
  (battery_level_r0_four)
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
  (not (robot_at_r0_p1))
  (not (battery_level_r0_five))
  (robot_at_r0_p2)
  (battery_level_r0_four)
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
  (not (robot_at_r0_p3))
  (not (battery_level_r0_five))
  (robot_at_r0_p2)
  (battery_level_r0_four)
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
  (not (robot_at_r0_p2))
  (not (battery_level_r0_five))
  (robot_at_r0_p3)
  (battery_level_r0_four)
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
  (robot_at_r0_p3)
  (battery_level_r0_four)
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
  (not (robot_at_r0_p3))
  (not (battery_level_r0_five))
  (robot_at_r0_p4)
  (battery_level_r0_four)
 )
)
(:action _move_r0_p5_p4_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_five)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_five))
  (robot_at_r0_p4)
  (battery_level_r0_four)
 )
)
(:action _move_r0_p4_p5_four_five_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_five)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_five))
  (robot_at_r0_p5)
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
  (not (robot_at_r0_p1))
  (not (battery_level_r0_four))
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
  (not (robot_at_r0_p2))
  (not (battery_level_r0_four))
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
  (not (robot_at_r0_p1))
  (not (battery_level_r0_four))
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
  (not (robot_at_r0_p3))
  (not (battery_level_r0_four))
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
  (not (robot_at_r0_p2))
  (not (battery_level_r0_four))
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
  (not (robot_at_r0_p3))
  (not (battery_level_r0_four))
  (robot_at_r0_p4)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p5_p4_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_four)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_four))
  (robot_at_r0_p4)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p4_p5_three_four_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_four)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_four))
  (robot_at_r0_p5)
  (battery_level_r0_three)
 )
)
(:action _move_r0_p1_p0_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p0)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p0_p1_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p1)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p2_p1_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p1)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p1_p2_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p2)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p3_p2_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p2)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p2_p3_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p3)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p4_p3_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p3)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p3_p4_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p4)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p5_p4_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p4)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p4_p5_thirteen_fourteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_fourteen)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_fourteen))
  (robot_at_r0_p5)
  (battery_level_r0_thirteen)
 )
)
(:action _move_r0_p1_p0_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_nine))
  (robot_at_r0_p0)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p0_p1_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_nine))
  (robot_at_r0_p1)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p2_p1_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_nine))
  (robot_at_r0_p1)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p1_p2_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_nine))
  (robot_at_r0_p2)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p3_p2_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_nine))
  (robot_at_r0_p2)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p2_p3_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_nine))
  (robot_at_r0_p3)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p4_p3_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_nine))
  (robot_at_r0_p3)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p3_p4_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_nine))
  (robot_at_r0_p4)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p5_p4_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_nine))
  (robot_at_r0_p4)
  (battery_level_r0_eight)
 )
)
(:action _move_r0_p4_p5_eight_nine_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_nine)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_nine))
  (robot_at_r0_p5)
  (battery_level_r0_eight)
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
(:action _move_r0_p5_p4_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_one))
  (robot_at_r0_p4)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p4_p5_zero_one_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_one)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_one))
  (robot_at_r0_p5)
  (battery_level_r0_zero)
 )
)
(:action _move_r0_p1_p0_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p1))
  (robot_at_r0_p0)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p0_p1_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_seven))
  (robot_at_r0_p1)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p2_p1_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p2))
  (robot_at_r0_p1)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p1_p2_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p1))
  (robot_at_r0_p2)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p3_p2_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p3))
  (robot_at_r0_p2)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p2_p3_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p2))
  (robot_at_r0_p3)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p4_p3_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p4))
  (robot_at_r0_p3)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p3_p4_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p3))
  (robot_at_r0_p4)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p5_p4_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_seven))
  (robot_at_r0_p4)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p4_p5_six_seven_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_seven)
  )
 :effect (and
  (not (battery_level_r0_seven))
  (not (robot_at_r0_p4))
  (robot_at_r0_p5)
  (battery_level_r0_six)
 )
)
(:action _move_r0_p1_p0_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_six))
  (robot_at_r0_p0)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p0_p1_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_six))
  (robot_at_r0_p1)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p2_p1_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_six))
  (robot_at_r0_p1)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p1_p2_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_six))
  (robot_at_r0_p2)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p3_p2_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_six))
  (robot_at_r0_p2)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p2_p3_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_six))
  (robot_at_r0_p3)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p4_p3_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_six))
  (robot_at_r0_p3)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p3_p4_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_six))
  (robot_at_r0_p4)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p5_p4_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_six))
  (robot_at_r0_p4)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p4_p5_five_six_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_six)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_six))
  (robot_at_r0_p5)
  (battery_level_r0_five)
 )
)
(:action _move_r0_p1_p0_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p1))
  (robot_at_r0_p0)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p0_p1_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p0))
  (robot_at_r0_p1)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p2_p1_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p2))
  (robot_at_r0_p1)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p1_p2_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p1))
  (robot_at_r0_p2)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p3_p2_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p3))
  (robot_at_r0_p2)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p2_p3_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p2))
  (robot_at_r0_p3)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p4_p3_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p4))
  (robot_at_r0_p3)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p3_p4_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p3))
  (robot_at_r0_p4)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p5_p4_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_sixteen))
  (robot_at_r0_p4)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p4_p5_fifteen_sixteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_sixteen)
  )
 :effect (and
  (not (battery_level_r0_sixteen))
  (not (robot_at_r0_p4))
  (robot_at_r0_p5)
  (battery_level_r0_fifteen)
 )
)
(:action _move_r0_p1_p0_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_ten))
  (robot_at_r0_p0)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p0_p1_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_ten))
  (robot_at_r0_p1)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p2_p1_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_ten))
  (robot_at_r0_p1)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p1_p2_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_ten))
  (robot_at_r0_p2)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p3_p2_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_ten))
  (robot_at_r0_p2)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p2_p3_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_ten))
  (robot_at_r0_p3)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p4_p3_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_ten))
  (robot_at_r0_p3)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p3_p4_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_ten))
  (robot_at_r0_p4)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p5_p4_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_ten))
  (robot_at_r0_p4)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p4_p5_nine_ten_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_ten)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_ten))
  (robot_at_r0_p5)
  (battery_level_r0_nine)
 )
)
(:action _move_r0_p1_p0_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p0)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p0_p1_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p1)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p2_p1_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p1)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p1_p2_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p2)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p3_p2_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p2)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p2_p3_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p3)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p4_p3_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p3)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p3_p4_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p4)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p5_p4_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p4)
  (battery_level_r0_twelve)
 )
)
(:action _move_r0_p4_p5_twelve_thirteen_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_thirteen)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_thirteen))
  (robot_at_r0_p5)
  (battery_level_r0_twelve)
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
(:action _move_r0_p5_p4_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_three))
  (robot_at_r0_p4)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p4_p5_two_three_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_three)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_three))
  (robot_at_r0_p5)
  (battery_level_r0_two)
 )
)
(:action _move_r0_p1_p0_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p0)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p0_p1_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p0)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p0))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p1)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p2_p1_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p1)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p1_p2_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p1)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p1))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p2)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p3_p2_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p2)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p2_p3_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p2)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p2))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p3)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p4_p3_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p3)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p3_p4_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p3)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p3))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p4)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p5_p4_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p4)
  (battery_level_r0_eleven)
 )
)
(:action _move_r0_p4_p5_eleven_twelve_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_twelve)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_twelve))
  (robot_at_r0_p5)
  (battery_level_r0_eleven)
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
(:action _move_r0_p5_p4_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p5))
  (not (battery_level_r0_two))
  (robot_at_r0_p4)
  (battery_level_r0_one)
 )
)
(:action _move_r0_p4_p5_one_two_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p4)
   (battery_level_r0_two)
  )
 :effect (and
  (not (robot_at_r0_p4))
  (not (battery_level_r0_two))
  (robot_at_r0_p5)
  (battery_level_r0_one)
 )
)
(:action _unload_at_depot_r0_b0_p5_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (robot_has_r0_b0)
  )
 :effect (and
  (not (robot_has_r0_b0))
  (robot_free_r0)
  (pallet_at_b0_p5)
 )
)
(:action _unload_at_depot_r0_b1_p5_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (robot_has_r0_b1)
  )
 :effect (and
  (not (robot_has_r0_b1))
  (robot_free_r0)
  (pallet_at_b1_p5)
 )
)
(:action _unload_at_depot_r0_b2_p5_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (robot_has_r0_b2)
  )
 :effect (and
  (not (robot_has_r0_b2))
  (robot_free_r0)
  (pallet_at_b2_p5)
 )
)
(:action _load_from_depot_r0_b0_p5_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (robot_free_r0)
   (pallet_at_b0_p5)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b0_p5))
  (robot_has_r0_b0)
 )
)
(:action _load_from_depot_r0_b1_p5_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (robot_free_r0)
   (pallet_at_b1_p5)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b1_p5))
  (robot_has_r0_b1)
 )
)
(:action _load_from_depot_r0_b2_p5_
 :parameters ()
 :precondition
  (and
   (robot_at_r0_p5)
   (robot_free_r0)
   (pallet_at_b2_p5)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b2_p5))
  (robot_has_r0_b2)
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
(:durative-action _unload_r0_b2_p0_t0_
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
   (at start (robot_has_r0_b2))
   (at end (unload_clip_started_b2_p0_t0))
  )
 :effect (and
  (at start (not (robot_has_r0_b2)))
  (at start (not (position_free_p0)))
  (at start (unload_started_b2_p0_t0))
  (at end (robot_free_r0))
  (at end (unload_ended_b2_p0_t0))
  (at end (pallet_at_b2_p0))
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
(:durative-action _unload_r0_b2_p1_t1_
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
   (at start (robot_has_r0_b2))
   (at end (unload_clip_started_b2_p1_t1))
  )
 :effect (and
  (at start (not (robot_has_r0_b2)))
  (at start (not (position_free_p1)))
  (at start (unload_started_b2_p1_t1))
  (at end (robot_free_r0))
  (at end (unload_ended_b2_p1_t1))
  (at end (pallet_at_b2_p1))
 )
)
(:durative-action _unload_r0_b0_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p2))
   (at start (robot_at_r0_p2))
   (at start (robot_has_r0_b0))
   (at end (unload_clip_started_b0_p2_t2))
  )
 :effect (and
  (at start (not (robot_has_r0_b0)))
  (at start (not (position_free_p2)))
  (at start (unload_started_b0_p2_t2))
  (at end (robot_free_r0))
  (at end (unload_ended_b0_p2_t2))
  (at end (pallet_at_b0_p2))
 )
)
(:durative-action _unload_r0_b1_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p2))
   (at start (robot_at_r0_p2))
   (at start (robot_has_r0_b1))
   (at end (unload_clip_started_b1_p2_t2))
  )
 :effect (and
  (at start (not (robot_has_r0_b1)))
  (at start (not (position_free_p2)))
  (at start (unload_started_b1_p2_t2))
  (at end (robot_free_r0))
  (at end (unload_ended_b1_p2_t2))
  (at end (pallet_at_b1_p2))
 )
)
(:durative-action _unload_r0_b2_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p2))
   (at start (robot_at_r0_p2))
   (at start (robot_has_r0_b2))
   (at end (unload_clip_started_b2_p2_t2))
  )
 :effect (and
  (at start (not (robot_has_r0_b2)))
  (at start (not (position_free_p2)))
  (at start (unload_started_b2_p2_t2))
  (at end (robot_free_r0))
  (at end (unload_ended_b2_p2_t2))
  (at end (pallet_at_b2_p2))
 )
)
(:durative-action _unload_r0_b0_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p3))
   (at start (robot_at_r0_p3))
   (at start (robot_has_r0_b0))
   (at end (unload_clip_started_b0_p3_t3))
  )
 :effect (and
  (at start (not (robot_has_r0_b0)))
  (at start (not (position_free_p3)))
  (at start (unload_started_b0_p3_t3))
  (at end (robot_free_r0))
  (at end (unload_ended_b0_p3_t3))
  (at end (pallet_at_b0_p3))
 )
)
(:durative-action _unload_r0_b1_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p3))
   (at start (robot_at_r0_p3))
   (at start (robot_has_r0_b1))
   (at end (unload_clip_started_b1_p3_t3))
  )
 :effect (and
  (at start (not (robot_has_r0_b1)))
  (at start (not (position_free_p3)))
  (at start (unload_started_b1_p3_t3))
  (at end (robot_free_r0))
  (at end (unload_ended_b1_p3_t3))
  (at end (pallet_at_b1_p3))
 )
)
(:durative-action _unload_r0_b2_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 10)
   (<= ?duration 10)
  )
 :condition
  (and
   (at start (position_free_p3))
   (at start (robot_at_r0_p3))
   (at start (robot_has_r0_b2))
   (at end (unload_clip_started_b2_p3_t3))
  )
 :effect (and
  (at start (not (robot_has_r0_b2)))
  (at start (not (position_free_p3)))
  (at start (unload_started_b2_p3_t3))
  (at end (robot_free_r0))
  (at end (unload_ended_b2_p3_t3))
  (at end (pallet_at_b2_p3))
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
(:durative-action _unload_clip_b2_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b2_p0_t0))
   (at end (unload_ended_b2_p0_t0))
   (at end (unload_min_timeout_started_b2_p0_t0))
   (at end (unload_max_timeout_started_b2_p0_t0))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b2_p0_t0))
  (at start (unload_min_timeout_can_start_b2_p0_t0))
  (at start (unload_clip_started_b2_p0_t0))
  (at end (not (unload_min_timeout_started_b2_p0_t0)))
  (at end (not (unload_max_timeout_started_b2_p0_t0)))
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
(:durative-action _unload_clip_b2_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b2_p1_t1))
   (at end (unload_ended_b2_p1_t1))
   (at end (unload_min_timeout_started_b2_p1_t1))
   (at end (unload_max_timeout_started_b2_p1_t1))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b2_p1_t1))
  (at start (unload_min_timeout_can_start_b2_p1_t1))
  (at start (unload_clip_started_b2_p1_t1))
  (at end (not (unload_min_timeout_started_b2_p1_t1)))
  (at end (not (unload_max_timeout_started_b2_p1_t1)))
 )
)
(:durative-action _unload_clip_b0_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b0_p2_t2))
   (at end (unload_ended_b0_p2_t2))
   (at end (unload_min_timeout_started_b0_p2_t2))
   (at end (unload_max_timeout_started_b0_p2_t2))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b0_p2_t2))
  (at start (unload_min_timeout_can_start_b0_p2_t2))
  (at start (unload_clip_started_b0_p2_t2))
  (at end (not (unload_min_timeout_started_b0_p2_t2)))
  (at end (not (unload_max_timeout_started_b0_p2_t2)))
 )
)
(:durative-action _unload_clip_b1_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b1_p2_t2))
   (at end (unload_ended_b1_p2_t2))
   (at end (unload_min_timeout_started_b1_p2_t2))
   (at end (unload_max_timeout_started_b1_p2_t2))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b1_p2_t2))
  (at start (unload_min_timeout_can_start_b1_p2_t2))
  (at start (unload_clip_started_b1_p2_t2))
  (at end (not (unload_min_timeout_started_b1_p2_t2)))
  (at end (not (unload_max_timeout_started_b1_p2_t2)))
 )
)
(:durative-action _unload_clip_b2_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b2_p2_t2))
   (at end (unload_ended_b2_p2_t2))
   (at end (unload_min_timeout_started_b2_p2_t2))
   (at end (unload_max_timeout_started_b2_p2_t2))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b2_p2_t2))
  (at start (unload_min_timeout_can_start_b2_p2_t2))
  (at start (unload_clip_started_b2_p2_t2))
  (at end (not (unload_min_timeout_started_b2_p2_t2)))
  (at end (not (unload_max_timeout_started_b2_p2_t2)))
 )
)
(:durative-action _unload_clip_b0_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b0_p3_t3))
   (at end (unload_ended_b0_p3_t3))
   (at end (unload_min_timeout_started_b0_p3_t3))
   (at end (unload_max_timeout_started_b0_p3_t3))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b0_p3_t3))
  (at start (unload_min_timeout_can_start_b0_p3_t3))
  (at start (unload_clip_started_b0_p3_t3))
  (at end (not (unload_min_timeout_started_b0_p3_t3)))
  (at end (not (unload_max_timeout_started_b0_p3_t3)))
 )
)
(:durative-action _unload_clip_b1_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b1_p3_t3))
   (at end (unload_ended_b1_p3_t3))
   (at end (unload_min_timeout_started_b1_p3_t3))
   (at end (unload_max_timeout_started_b1_p3_t3))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b1_p3_t3))
  (at start (unload_min_timeout_can_start_b1_p3_t3))
  (at start (unload_clip_started_b1_p3_t3))
  (at end (not (unload_min_timeout_started_b1_p3_t3)))
  (at end (not (unload_max_timeout_started_b1_p3_t3)))
 )
)
(:durative-action _unload_clip_b2_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 3)
   (<= ?duration 3)
  )
 :condition
  (and
   (at start (unload_started_b2_p3_t3))
   (at end (unload_ended_b2_p3_t3))
   (at end (unload_min_timeout_started_b2_p3_t3))
   (at end (unload_max_timeout_started_b2_p3_t3))
  )
 :effect (and
  (at start (unload_max_timeout_can_start_b2_p3_t3))
  (at start (unload_min_timeout_can_start_b2_p3_t3))
  (at start (unload_clip_started_b2_p3_t3))
  (at end (not (unload_min_timeout_started_b2_p3_t3)))
  (at end (not (unload_max_timeout_started_b2_p3_t3)))
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
(:durative-action _unload_min_timeout_b2_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b2_p0_t0))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b2_p0_t0)))
  (at start (unload_min_timeout_started_b2_p0_t0))
  (at end (ready_b2_p0_t0))
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
(:durative-action _unload_min_timeout_b2_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b2_p1_t1))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b2_p1_t1)))
  (at start (unload_min_timeout_started_b2_p1_t1))
  (at end (ready_b2_p1_t1))
 )
)
(:durative-action _unload_min_timeout_b0_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b0_p2_t2))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b0_p2_t2)))
  (at start (unload_min_timeout_started_b0_p2_t2))
  (at end (ready_b0_p2_t2))
 )
)
(:durative-action _unload_min_timeout_b1_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b1_p2_t2))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b1_p2_t2)))
  (at start (unload_min_timeout_started_b1_p2_t2))
  (at end (ready_b1_p2_t2))
 )
)
(:durative-action _unload_min_timeout_b2_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b2_p2_t2))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b2_p2_t2)))
  (at start (unload_min_timeout_started_b2_p2_t2))
  (at end (ready_b2_p2_t2))
 )
)
(:durative-action _unload_min_timeout_b0_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b0_p3_t3))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b0_p3_t3)))
  (at start (unload_min_timeout_started_b0_p3_t3))
  (at end (ready_b0_p3_t3))
 )
)
(:durative-action _unload_min_timeout_b1_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b1_p3_t3))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b1_p3_t3)))
  (at start (unload_min_timeout_started_b1_p3_t3))
  (at end (ready_b1_p3_t3))
 )
)
(:durative-action _unload_min_timeout_b2_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 1000)
   (<= ?duration 1000)
  )
 :condition
  (at start (unload_min_timeout_can_start_b2_p3_t3))
 :effect (and
  (at start (not (unload_min_timeout_can_start_b2_p3_t3)))
  (at start (unload_min_timeout_started_b2_p3_t3))
  (at end (ready_b2_p3_t3))
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
(:durative-action _unload_max_timeout_b2_p0_t0_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b2_p0_t0))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b2_p0_t0)))
  (at start (unload_max_timeout_started_b2_p0_t0))
  (at end (not (ready_b2_p0_t0)))
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
(:durative-action _unload_max_timeout_b2_p1_t1_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b2_p1_t1))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b2_p1_t1)))
  (at start (unload_max_timeout_started_b2_p1_t1))
  (at end (not (ready_b2_p1_t1)))
 )
)
(:durative-action _unload_max_timeout_b0_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b0_p2_t2))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b0_p2_t2)))
  (at start (unload_max_timeout_started_b0_p2_t2))
  (at end (not (ready_b0_p2_t2)))
 )
)
(:durative-action _unload_max_timeout_b1_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b1_p2_t2))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b1_p2_t2)))
  (at start (unload_max_timeout_started_b1_p2_t2))
  (at end (not (ready_b1_p2_t2)))
 )
)
(:durative-action _unload_max_timeout_b2_p2_t2_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b2_p2_t2))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b2_p2_t2)))
  (at start (unload_max_timeout_started_b2_p2_t2))
  (at end (not (ready_b2_p2_t2)))
 )
)
(:durative-action _unload_max_timeout_b0_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b0_p3_t3))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b0_p3_t3)))
  (at start (unload_max_timeout_started_b0_p3_t3))
  (at end (not (ready_b0_p3_t3)))
 )
)
(:durative-action _unload_max_timeout_b1_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b1_p3_t3))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b1_p3_t3)))
  (at start (unload_max_timeout_started_b1_p3_t3))
  (at end (not (ready_b1_p3_t3)))
 )
)
(:durative-action _unload_max_timeout_b2_p3_t3_
 :parameters ()
 :duration
  (and
   (>= ?duration 2000)
   (<= ?duration 2000)
  )
 :condition
  (at start (unload_max_timeout_can_start_b2_p3_t3))
 :effect (and
  (at start (not (unload_max_timeout_can_start_b2_p3_t3)))
  (at start (unload_max_timeout_started_b2_p3_t3))
  (at end (not (ready_b2_p3_t3)))
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
(:action _load_r0_b2_p0_t0_
 :parameters ()
 :precondition
  (and
   (pallet_at_b2_p0)
   (robot_free_r0)
   (robot_at_r0_p0)
   (ready_b2_p0_t0)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b2_p0))
  (not (ready_b2_p0_t0))
  (robot_has_r0_b2)
  (position_free_p0)
  (treated_b2_t0)
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
(:action _load_r0_b2_p1_t1_
 :parameters ()
 :precondition
  (and
   (pallet_at_b2_p1)
   (robot_free_r0)
   (robot_at_r0_p1)
   (ready_b2_p1_t1)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b2_p1))
  (not (ready_b2_p1_t1))
  (robot_has_r0_b2)
  (position_free_p1)
  (treated_b2_t1)
 )
)
(:action _load_r0_b0_p2_t2_
 :parameters ()
 :precondition
  (and
   (pallet_at_b0_p2)
   (robot_free_r0)
   (robot_at_r0_p2)
   (ready_b0_p2_t2)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b0_p2))
  (not (ready_b0_p2_t2))
  (robot_has_r0_b0)
  (treated_b0_t2)
  (position_free_p2)
 )
)
(:action _load_r0_b1_p2_t2_
 :parameters ()
 :precondition
  (and
   (pallet_at_b1_p2)
   (robot_free_r0)
   (robot_at_r0_p2)
   (ready_b1_p2_t2)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b1_p2))
  (not (ready_b1_p2_t2))
  (robot_has_r0_b1)
  (position_free_p2)
  (treated_b1_t2)
 )
)
(:action _load_r0_b2_p2_t2_
 :parameters ()
 :precondition
  (and
   (pallet_at_b2_p2)
   (robot_free_r0)
   (robot_at_r0_p2)
   (ready_b2_p2_t2)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b2_p2))
  (not (ready_b2_p2_t2))
  (robot_has_r0_b2)
  (position_free_p2)
  (treated_b2_t2)
 )
)
(:action _load_r0_b0_p3_t3_
 :parameters ()
 :precondition
  (and
   (pallet_at_b0_p3)
   (robot_free_r0)
   (robot_at_r0_p3)
   (ready_b0_p3_t3)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b0_p3))
  (not (ready_b0_p3_t3))
  (robot_has_r0_b0)
  (treated_b0_t3)
  (position_free_p3)
 )
)
(:action _load_r0_b1_p3_t3_
 :parameters ()
 :precondition
  (and
   (pallet_at_b1_p3)
   (robot_free_r0)
   (robot_at_r0_p3)
   (ready_b1_p3_t3)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b1_p3))
  (not (ready_b1_p3_t3))
  (robot_has_r0_b1)
  (position_free_p3)
  (treated_b1_t3)
 )
)
(:action _load_r0_b2_p3_t3_
 :parameters ()
 :precondition
  (and
   (pallet_at_b2_p3)
   (robot_free_r0)
   (robot_at_r0_p3)
   (ready_b2_p3_t3)
  )
 :effect (and
  (not (robot_free_r0))
  (not (pallet_at_b2_p3))
  (not (ready_b2_p3_t3))
  (robot_has_r0_b2)
  (position_free_p3)
  (treated_b2_t3)
 )
)
)
