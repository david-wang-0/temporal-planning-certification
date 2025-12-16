(define (domain ground)
(:requirements :strips)
(:predicates
 (at_apn1_apt2)
 (at_tru1_pos1)
 (at_obj1_pos1)
 (at_tru2_pos2)
 (in_obj1_tru1)
 (in_obj1_tru2)
 (in_obj1_apn1)
 (at_obj1_apt1)
 (at_obj1_apt2)
 (at_obj1_pos2)
 (at_tru1_apt1)
 (at_tru2_apt1)
 (at_tru2_pos1)
 (at_tru1_apt2)
 (at_tru2_apt2)
 (at_tru1_pos2)
 (at_apn1_apt1)
)

(:action _load-truck_obj1_tru1_apt1_
 :parameters ()
 :precondition
  (and
   (at_tru1_apt1)
   (at_obj1_apt1)
  )
 :effect (and
  (not (at_obj1_apt1))
  (in_obj1_tru1)
 )
)
(:action _load-truck_obj1_tru2_apt1_
 :parameters ()
 :precondition
  (and
   (at_tru2_apt1)
   (at_obj1_apt1)
  )
 :effect (and
  (not (at_obj1_apt1))
  (in_obj1_tru2)
 )
)
(:action _load-truck_obj1_tru1_apt2_
 :parameters ()
 :precondition
  (and
   (at_tru1_apt2)
   (at_obj1_apt2)
  )
 :effect (and
  (not (at_obj1_apt2))
  (in_obj1_tru1)
 )
)
(:action _load-truck_obj1_tru2_apt2_
 :parameters ()
 :precondition
  (and
   (at_tru2_apt2)
   (at_obj1_apt2)
  )
 :effect (and
  (not (at_obj1_apt2))
  (in_obj1_tru2)
 )
)
(:action _load-truck_obj1_tru1_pos1_
 :parameters ()
 :precondition
  (and
   (at_tru1_pos1)
   (at_obj1_pos1)
  )
 :effect (and
  (not (at_obj1_pos1))
  (in_obj1_tru1)
 )
)
(:action _load-truck_obj1_tru2_pos1_
 :parameters ()
 :precondition
  (and
   (at_tru2_pos1)
   (at_obj1_pos1)
  )
 :effect (and
  (not (at_obj1_pos1))
  (in_obj1_tru2)
 )
)
(:action _load-truck_obj1_tru1_pos2_
 :parameters ()
 :precondition
  (and
   (at_tru1_pos2)
   (at_obj1_pos2)
  )
 :effect (and
  (not (at_obj1_pos2))
  (in_obj1_tru1)
 )
)
(:action _load-truck_obj1_tru2_pos2_
 :parameters ()
 :precondition
  (and
   (at_tru2_pos2)
   (at_obj1_pos2)
  )
 :effect (and
  (not (at_obj1_pos2))
  (in_obj1_tru2)
 )
)
(:action _load-airplane_obj1_apn1_apt1_
 :parameters ()
 :precondition
  (and
   (at_obj1_apt1)
   (at_apn1_apt1)
  )
 :effect (and
  (not (at_obj1_apt1))
  (in_obj1_apn1)
 )
)
(:action _load-airplane_obj1_apn1_apt2_
 :parameters ()
 :precondition
  (and
   (at_obj1_apt2)
   (at_apn1_apt2)
  )
 :effect (and
  (not (at_obj1_apt2))
  (in_obj1_apn1)
 )
)
(:action _unload-truck_obj1_tru1_apt1_
 :parameters ()
 :precondition
  (and
   (at_tru1_apt1)
   (in_obj1_tru1)
  )
 :effect (and
  (not (in_obj1_tru1))
  (at_obj1_apt1)
 )
)
(:action _unload-truck_obj1_tru2_apt1_
 :parameters ()
 :precondition
  (and
   (at_tru2_apt1)
   (in_obj1_tru2)
  )
 :effect (and
  (not (in_obj1_tru2))
  (at_obj1_apt1)
 )
)
(:action _unload-truck_obj1_tru1_apt2_
 :parameters ()
 :precondition
  (and
   (at_tru1_apt2)
   (in_obj1_tru1)
  )
 :effect (and
  (not (in_obj1_tru1))
  (at_obj1_apt2)
 )
)
(:action _unload-truck_obj1_tru2_apt2_
 :parameters ()
 :precondition
  (and
   (at_tru2_apt2)
   (in_obj1_tru2)
  )
 :effect (and
  (not (in_obj1_tru2))
  (at_obj1_apt2)
 )
)
(:action _unload-truck_obj1_tru1_pos1_
 :parameters ()
 :precondition
  (and
   (at_tru1_pos1)
   (in_obj1_tru1)
  )
 :effect (and
  (not (in_obj1_tru1))
  (at_obj1_pos1)
 )
)
(:action _unload-truck_obj1_tru2_pos1_
 :parameters ()
 :precondition
  (and
   (at_tru2_pos1)
   (in_obj1_tru2)
  )
 :effect (and
  (not (in_obj1_tru2))
  (at_obj1_pos1)
 )
)
(:action _unload-truck_obj1_tru1_pos2_
 :parameters ()
 :precondition
  (and
   (at_tru1_pos2)
   (in_obj1_tru1)
  )
 :effect (and
  (not (in_obj1_tru1))
  (at_obj1_pos2)
 )
)
(:action _unload-truck_obj1_tru2_pos2_
 :parameters ()
 :precondition
  (and
   (at_tru2_pos2)
   (in_obj1_tru2)
  )
 :effect (and
  (not (in_obj1_tru2))
  (at_obj1_pos2)
 )
)
(:action _unload-airplane_obj1_apn1_apt1_
 :parameters ()
 :precondition
  (and
   (in_obj1_apn1)
   (at_apn1_apt1)
  )
 :effect (and
  (not (in_obj1_apn1))
  (at_obj1_apt1)
 )
)
(:action _unload-airplane_obj1_apn1_apt2_
 :parameters ()
 :precondition
  (and
   (in_obj1_apn1)
   (at_apn1_apt2)
  )
 :effect (and
  (not (in_obj1_apn1))
  (at_obj1_apt2)
 )
)
(:action _drive-truck_tru1_apt1_apt1_cit1_
 :parameters ()
 :precondition
  (at_tru1_apt1)
 :effect (and
  (not (at_tru1_apt1))
  (at_tru1_apt1)
 )
)
(:action _drive-truck_tru2_apt1_apt1_cit1_
 :parameters ()
 :precondition
  (at_tru2_apt1)
 :effect (and
  (not (at_tru2_apt1))
  (at_tru2_apt1)
 )
)
(:action _drive-truck_tru1_pos1_apt1_cit1_
 :parameters ()
 :precondition
  (at_tru1_pos1)
 :effect (and
  (not (at_tru1_pos1))
  (at_tru1_apt1)
 )
)
(:action _drive-truck_tru2_pos1_apt1_cit1_
 :parameters ()
 :precondition
  (at_tru2_pos1)
 :effect (and
  (not (at_tru2_pos1))
  (at_tru2_apt1)
 )
)
(:action _drive-truck_tru1_apt1_pos1_cit1_
 :parameters ()
 :precondition
  (at_tru1_apt1)
 :effect (and
  (not (at_tru1_apt1))
  (at_tru1_pos1)
 )
)
(:action _drive-truck_tru2_apt1_pos1_cit1_
 :parameters ()
 :precondition
  (at_tru2_apt1)
 :effect (and
  (not (at_tru2_apt1))
  (at_tru2_pos1)
 )
)
(:action _drive-truck_tru1_pos1_pos1_cit1_
 :parameters ()
 :precondition
  (at_tru1_pos1)
 :effect (and
  (not (at_tru1_pos1))
  (at_tru1_pos1)
 )
)
(:action _drive-truck_tru2_pos1_pos1_cit1_
 :parameters ()
 :precondition
  (at_tru2_pos1)
 :effect (and
  (not (at_tru2_pos1))
  (at_tru2_pos1)
 )
)
(:action _drive-truck_tru1_apt2_apt2_cit2_
 :parameters ()
 :precondition
  (at_tru1_apt2)
 :effect (and
  (not (at_tru1_apt2))
  (at_tru1_apt2)
 )
)
(:action _drive-truck_tru2_apt2_apt2_cit2_
 :parameters ()
 :precondition
  (at_tru2_apt2)
 :effect (and
  (not (at_tru2_apt2))
  (at_tru2_apt2)
 )
)
(:action _drive-truck_tru1_pos2_apt2_cit2_
 :parameters ()
 :precondition
  (at_tru1_pos2)
 :effect (and
  (not (at_tru1_pos2))
  (at_tru1_apt2)
 )
)
(:action _drive-truck_tru2_pos2_apt2_cit2_
 :parameters ()
 :precondition
  (at_tru2_pos2)
 :effect (and
  (not (at_tru2_pos2))
  (at_tru2_apt2)
 )
)
(:action _drive-truck_tru1_apt2_pos2_cit2_
 :parameters ()
 :precondition
  (at_tru1_apt2)
 :effect (and
  (not (at_tru1_apt2))
  (at_tru1_pos2)
 )
)
(:action _drive-truck_tru2_apt2_pos2_cit2_
 :parameters ()
 :precondition
  (at_tru2_apt2)
 :effect (and
  (not (at_tru2_apt2))
  (at_tru2_pos2)
 )
)
(:action _drive-truck_tru1_pos2_pos2_cit2_
 :parameters ()
 :precondition
  (at_tru1_pos2)
 :effect (and
  (not (at_tru1_pos2))
  (at_tru1_pos2)
 )
)
(:action _drive-truck_tru2_pos2_pos2_cit2_
 :parameters ()
 :precondition
  (at_tru2_pos2)
 :effect (and
  (not (at_tru2_pos2))
  (at_tru2_pos2)
 )
)
(:action _fly-airplane_apn1_apt1_apt1_
 :parameters ()
 :precondition
  (at_apn1_apt1)
 :effect (and
  (not (at_apn1_apt1))
  (at_apn1_apt1)
 )
)
(:action _fly-airplane_apn1_apt2_apt1_
 :parameters ()
 :precondition
  (at_apn1_apt2)
 :effect (and
  (not (at_apn1_apt2))
  (at_apn1_apt1)
 )
)
(:action _fly-airplane_apn1_apt1_apt2_
 :parameters ()
 :precondition
  (at_apn1_apt1)
 :effect (and
  (not (at_apn1_apt1))
  (at_apn1_apt2)
 )
)
(:action _fly-airplane_apn1_apt2_apt2_
 :parameters ()
 :precondition
  (at_apn1_apt2)
 :effect (and
  (not (at_apn1_apt2))
  (at_apn1_apt2)
 )
)
)
