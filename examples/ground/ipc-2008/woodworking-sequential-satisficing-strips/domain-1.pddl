(define (domain ground)
(:requirements :strips)
(:predicates
 (empty_highspeed-saw0)
 (available_p0)
 (colour_p0_red)
 (wood_p0_pine)
 (surface-condition_p0_smooth)
 (treatment_p0_varnished)
 (unused_p1)
 (available_p2)
 (colour_p2_natural)
 (wood_p2_teak)
 (surface-condition_p2_verysmooth)
 (treatment_p2_varnished)
 (boardsize_b0_s3)
 (wood_b0_pine)
 (surface-condition_b0_rough)
 (available_b0)
 (colour_p0_natural)
 (treatment_p1_varnished)
 (colour_p1_natural)
 (colour_p1_red)
 (colour_p2_red)
 (treatment_p0_glazed)
 (treatment_p1_glazed)
 (treatment_p2_glazed)
 (surface-condition_p0_verysmooth)
 (treatment_p0_colourfragments)
 (surface-condition_p1_verysmooth)
 (treatment_p1_colourfragments)
 (treatment_p2_colourfragments)
 (treatment_p0_untreated)
 (treatment_p1_untreated)
 (treatment_p2_untreated)
 (surface-condition_p1_smooth)
 (surface-condition_p2_smooth)
 (in-highspeed-saw_b0_highspeed-saw0)
 (available_p1)
 (wood_p1_pine)
 (surface-condition_p1_rough)
 (boardsize_b0_s1)
)

(:action _do-immersion-varnish_p0_immersion-varnisher0_natural_smooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (treatment_p0_varnished)
  (colour_p0_natural)
 )
)
(:action _do-immersion-varnish_p1_immersion-varnisher0_natural_smooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_natural)
 )
)
(:action _do-immersion-varnish_p2_immersion-varnisher0_natural_smooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_varnished)

 )
)
(:action _do-immersion-varnish_p0_immersion-varnisher0_red_smooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_red)
  (treatment_p0_varnished)

 )
)
(:action _do-immersion-varnish_p1_immersion-varnisher0_red_smooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_red)

 )
)
(:action _do-immersion-varnish_p2_immersion-varnisher0_red_smooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (treatment_p2_varnished)
  (colour_p2_red)

 )
)
(:action _do-immersion-varnish_p0_immersion-varnisher0_natural_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (treatment_p0_varnished)
  (colour_p0_natural)

 )
)
(:action _do-immersion-varnish_p1_immersion-varnisher0_natural_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_natural)

 )
)
(:action _do-immersion-varnish_p2_immersion-varnisher0_natural_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_varnished)

 )
)
(:action _do-immersion-varnish_p0_immersion-varnisher0_red_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_red)
  (treatment_p0_varnished)

 )
)
(:action _do-immersion-varnish_p1_immersion-varnisher0_red_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_red)

 )
)
(:action _do-immersion-varnish_p2_immersion-varnisher0_red_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (treatment_p2_varnished)
  (colour_p2_red)

 )
)
(:action _do-spray-varnish_p0_spray-varnisher0_natural_smooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (treatment_p0_varnished)
  (colour_p0_natural)
  
 )
)
(:action _do-spray-varnish_p1_spray-varnisher0_natural_smooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_natural)

 )
)
(:action _do-spray-varnish_p2_spray-varnisher0_natural_smooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_varnished)
  
 )
)
(:action _do-spray-varnish_p0_spray-varnisher0_red_smooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_red)
  (treatment_p0_varnished)
  
 )
)
(:action _do-spray-varnish_p1_spray-varnisher0_red_smooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_red)

 )
)
(:action _do-spray-varnish_p2_spray-varnisher0_red_smooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (treatment_p2_varnished)
  (colour_p2_red)
  
 )
)
(:action _do-spray-varnish_p0_spray-varnisher0_natural_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (treatment_p0_varnished)
  (colour_p0_natural)
  
 )
)
(:action _do-spray-varnish_p1_spray-varnisher0_natural_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_natural)

 )
)
(:action _do-spray-varnish_p2_spray-varnisher0_natural_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_varnished)
  
 )
)
(:action _do-spray-varnish_p0_spray-varnisher0_red_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_red)
  (treatment_p0_varnished)
  
 )
)
(:action _do-spray-varnish_p1_spray-varnisher0_red_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (treatment_p1_varnished)
  (colour_p1_red)

 )
)
(:action _do-spray-varnish_p2_spray-varnisher0_red_verysmooth_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (treatment_p2_varnished)
  (colour_p2_red)
  
 )
)
(:action _do-glaze_p0_glazer0_natural_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_natural)
  (treatment_p0_glazed)

 )
)
(:action _do-glaze_p1_glazer0_natural_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (colour_p1_natural)
  (treatment_p1_glazed)
  
 )
)
(:action _do-glaze_p2_glazer0_natural_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_glazed)
  
 )
)
(:action _do-glaze_p0_glazer0_red_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_red)
  (treatment_p0_glazed)

 )
)
(:action _do-glaze_p1_glazer0_red_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (colour_p1_red)
  (treatment_p1_glazed)
  
 )
)
(:action _do-glaze_p2_glazer0_red_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (colour_p2_red)
  (treatment_p2_glazed)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_natural_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_natural)
   (treatment_p0_varnished)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_varnished))
  (not (colour_p0_natural))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_colourfragments)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_natural_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_natural)
   (treatment_p1_varnished)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_natural))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_colourfragments)

 )
)
(:action _do-grind_p2_grinder0_smooth_natural_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_natural)
   (treatment_p2_varnished)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_varnished))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_colourfragments)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_natural_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_natural)
   (treatment_p0_varnished)
  )
 :effect (and
  (not (treatment_p0_varnished))
  (not (colour_p0_natural))
  (not (surface-condition_p0_verysmooth))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_colourfragments)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_natural_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_natural)
   (treatment_p1_varnished)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_natural))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_colourfragments)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_natural_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_natural)
   (treatment_p2_varnished)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_varnished))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_colourfragments)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_red_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_red)
   (treatment_p0_varnished)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_varnished))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_colourfragments)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_red_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_red)
   (treatment_p1_varnished)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_red))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_colourfragments)

 )
)
(:action _do-grind_p2_grinder0_smooth_red_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_red)
   (treatment_p2_varnished)
  )
 :effect (and
  (not (treatment_p2_varnished))
  (not (colour_p2_red))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_colourfragments)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_red_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_red)
   (treatment_p0_varnished)
  )
 :effect (and
  (not (colour_p0_red))
  (not (treatment_p0_varnished))
  (not (surface-condition_p0_verysmooth))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_colourfragments)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_red_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_red)
   (treatment_p1_varnished)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_red))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_colourfragments)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_red_varnished_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_red)
   (treatment_p2_varnished)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_varnished))
  (not (colour_p2_red))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_colourfragments)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_natural_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_natural)
   (treatment_p0_colourfragments)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (colour_p0_natural))
  (not (treatment_p0_colourfragments))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_natural_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_natural)
   (treatment_p1_colourfragments)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_colourfragments))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_smooth_natural_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_natural)
   (treatment_p2_colourfragments)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_colourfragments))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_natural_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_natural)
   (treatment_p0_colourfragments)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_colourfragments))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_natural_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_natural)
   (treatment_p1_colourfragments)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_colourfragments))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_natural_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_natural)
   (treatment_p2_colourfragments)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_colourfragments))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_red_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_red)
   (treatment_p0_colourfragments)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_colourfragments))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_red_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_red)
   (treatment_p1_colourfragments)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_colourfragments))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_smooth_red_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_red)
   (treatment_p2_colourfragments)
  )
 :effect (and
  (not (colour_p2_red))
  (not (treatment_p2_colourfragments))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_red_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_red)
   (treatment_p0_colourfragments)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_colourfragments))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_red_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_red)
   (treatment_p1_colourfragments)
  )
 :effect (and
  (not (colour_p1_red))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_colourfragments))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_red_colourfragments_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_red)
   (treatment_p2_colourfragments)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (colour_p2_red))
  (not (treatment_p2_colourfragments))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_natural_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_natural)
   (treatment_p0_glazed)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (colour_p0_natural))
  (not (treatment_p0_glazed))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_natural_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_natural)
   (treatment_p1_glazed)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_smooth_natural_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_natural)
   (treatment_p2_glazed)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_glazed))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_natural_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_natural)
   (treatment_p0_glazed)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_glazed))
  (not (surface-condition_p0_verysmooth))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_natural_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_natural)
   (treatment_p1_glazed)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_natural_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_natural)
   (treatment_p2_glazed)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_glazed))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_red_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_red)
   (treatment_p0_glazed)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_glazed))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_red_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_red)
   (treatment_p1_glazed)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_smooth_red_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_red)
   (treatment_p2_glazed)
  )
 :effect (and
  (not (colour_p2_red))
  (not (treatment_p2_glazed))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_red_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_red)
   (treatment_p0_glazed)
  )
 :effect (and
  (not (colour_p0_red))
  (not (treatment_p0_glazed))
  (not (surface-condition_p0_verysmooth))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_red_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_red)
   (treatment_p1_glazed)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_red_glazed_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_red)
   (treatment_p2_glazed)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (colour_p2_red))
  (not (treatment_p2_glazed))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_natural_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_natural)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_natural_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_natural)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_smooth_natural_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_natural)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_natural_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_natural)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_untreated))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_natural_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_natural)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_untreated))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_natural_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_natural)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_smooth_red_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (colour_p0_red)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_untreated))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_smooth_red_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (colour_p1_red)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_untreated))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_smooth_red_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (colour_p2_red)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (colour_p2_red))
  (not (treatment_p2_untreated))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-grind_p0_grinder0_verysmooth_red_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (colour_p0_red)
   (treatment_p0_untreated)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_untreated))
  (colour_p0_natural)
  (surface-condition_p0_verysmooth)
  (treatment_p0_untreated)
  
 )
)
(:action _do-grind_p1_grinder0_verysmooth_red_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (colour_p1_red)
   (treatment_p1_untreated)
  )
 :effect (and
  (not (colour_p1_red))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_untreated))
  (colour_p1_natural)
  (surface-condition_p1_verysmooth)
  (treatment_p1_untreated)

 )
)
(:action _do-grind_p2_grinder0_verysmooth_red_untreated_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (colour_p2_red)
   (treatment_p2_untreated)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (colour_p2_red))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (surface-condition_p2_verysmooth)
  (treatment_p2_untreated)
  
 )
)
(:action _do-plane_p1_planer0_rough_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_colourfragments)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_colourfragments))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_colourfragments)
   (colour_p0_natural)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (colour_p0_natural))
  (not (treatment_p0_colourfragments))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_colourfragments)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_colourfragments))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_colourfragments)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_colourfragments))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_colourfragments)
   (colour_p0_natural)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_colourfragments))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_colourfragments)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_colourfragments))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_natural_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_colourfragments)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_colourfragments))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_colourfragments)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_colourfragments))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_colourfragments)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_colourfragments))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_colourfragments)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_colourfragments))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_colourfragments)
   (colour_p2_red)
  )
 :effect (and
  (not (colour_p2_red))
  (not (treatment_p2_colourfragments))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_colourfragments)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_colourfragments))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_colourfragments)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_colourfragments))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_red_colourfragments_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_colourfragments)
   (colour_p2_red)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (colour_p2_red))
  (not (treatment_p2_colourfragments))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_glazed)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_glazed)
   (colour_p0_natural)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (colour_p0_natural))
  (not (treatment_p0_glazed))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_glazed)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_glazed)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_glazed))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_glazed)
   (colour_p0_natural)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (treatment_p0_glazed))
  (not (surface-condition_p0_verysmooth))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_glazed)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_natural_glazed_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_glazed)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_glazed))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_glazed)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_glazed)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_glazed))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_glazed)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_glazed)
   (colour_p2_red)
  )
 :effect (and
  (not (colour_p2_red))
  (not (treatment_p2_glazed))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_glazed)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (treatment_p0_glazed))
  (not (surface-condition_p0_verysmooth))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_glazed)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_glazed))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_red_glazed_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_glazed)
   (colour_p2_red)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (colour_p2_red))
  (not (treatment_p2_glazed))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_untreated)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_untreated)
   (colour_p0_natural)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (colour_p0_natural))
  (not (treatment_p0_untreated))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_untreated)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (treatment_p1_untreated))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_untreated)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_untreated))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_untreated)
   (colour_p0_natural)
  )
 :effect (and
  (not (colour_p0_natural))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_untreated))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_untreated)
   (colour_p1_natural)
  )
 :effect (and
  (not (colour_p1_natural))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_untreated))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_natural_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_untreated)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_untreated)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_untreated))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_untreated)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_untreated))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_untreated)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (treatment_p1_untreated))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_untreated)
   (colour_p2_red)
  )
 :effect (and
  (not (colour_p2_red))
  (not (treatment_p2_untreated))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_untreated)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_verysmooth))
  (not (treatment_p0_untreated))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_untreated)
   (colour_p1_red)
  )
 :effect (and
  (not (colour_p1_red))
  (not (surface-condition_p1_verysmooth))
  (not (treatment_p1_untreated))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_red_untreated_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_untreated)
   (colour_p2_red)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (colour_p2_red))
  (not (treatment_p2_untreated))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_varnished)
   (colour_p1_natural)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_natural))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_varnished)
   (colour_p0_natural)
  )
 :effect (and
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_varnished))
  (not (colour_p0_natural))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_varnished)
   (colour_p1_natural)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_natural))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_varnished)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (treatment_p2_varnished))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_varnished)
   (colour_p0_natural)
  )
 :effect (and
  (not (treatment_p0_varnished))
  (not (colour_p0_natural))
  (not (surface-condition_p0_verysmooth))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_varnished)
   (colour_p1_natural)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_natural))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_natural_varnished_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_varnished)
   (colour_p2_natural)
  )
 :effect (and
  (not (colour_p2_natural))
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_varnished))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p1_planer0_rough_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_rough)
   (treatment_p1_varnished)
   (colour_p1_red)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_red))
  (not (surface-condition_p1_rough))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p0_planer0_smooth_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_smooth)
   (treatment_p0_varnished)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (surface-condition_p0_smooth))
  (not (treatment_p0_varnished))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_smooth_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_smooth)
   (treatment_p1_varnished)
   (colour_p1_red)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_red))
  (not (surface-condition_p1_smooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_smooth_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_smooth)
   (treatment_p2_varnished)
   (colour_p2_red)
  )
 :effect (and
  (not (treatment_p2_varnished))
  (not (colour_p2_red))
  (not (surface-condition_p2_smooth))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _do-plane_p0_planer0_verysmooth_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p0)
   (surface-condition_p0_verysmooth)
   (treatment_p0_varnished)
   (colour_p0_red)
  )
 :effect (and
  (not (colour_p0_red))
  (not (treatment_p0_varnished))
  (not (surface-condition_p0_verysmooth))
  (surface-condition_p0_smooth)
  (colour_p0_natural)
  (treatment_p0_untreated)

 )
)
(:action _do-plane_p1_planer0_verysmooth_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p1)
   (surface-condition_p1_verysmooth)
   (treatment_p1_varnished)
   (colour_p1_red)
  )
 :effect (and
  (not (treatment_p1_varnished))
  (not (colour_p1_red))
  (not (surface-condition_p1_verysmooth))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (surface-condition_p1_smooth)
  
 )
)
(:action _do-plane_p2_planer0_verysmooth_red_varnished_
 :parameters ()
 :precondition
  (and
   (available_p2)
   (surface-condition_p2_verysmooth)
   (treatment_p2_varnished)
   (colour_p2_red)
  )
 :effect (and
  (not (surface-condition_p2_verysmooth))
  (not (treatment_p2_varnished))
  (not (colour_p2_red))
  (colour_p2_natural)
  (treatment_p2_untreated)
  (surface-condition_p2_smooth)

 )
)
(:action _load-highspeed-saw_b0_highspeed-saw0_
 :parameters ()
 :precondition
  (and
   (empty_highspeed-saw0)
   (available_b0)
  )
 :effect (and
  (not (empty_highspeed-saw0))
  (not (available_b0))
  (in-highspeed-saw_b0_highspeed-saw0)

 )
)
(:action _unload-highspeed-saw_b0_highspeed-saw0_
 :parameters ()
 :precondition
  (in-highspeed-saw_b0_highspeed-saw0)
 :effect (and
  (not (in-highspeed-saw_b0_highspeed-saw0))
  (empty_highspeed-saw0)
  (available_b0)

 )
)
(:action _cut-board-medium_b0_p1_highspeed-saw0_pine_rough_s3_s2_s1_
 :parameters ()
 :precondition
  (and
   (unused_p1)
   (in-highspeed-saw_b0_highspeed-saw0)
   (wood_b0_pine)
   (surface-condition_b0_rough)
   (boardsize_b0_s3)
  )
 :effect (and
  (not (unused_p1))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (available_p1)
  (wood_p1_pine)
  (surface-condition_p1_rough)
  (boardsize_b0_s1)

 )
)
(:action _do-saw-medium_b0_p1_saw0_pine_rough_s3_s2_s1_
 :parameters ()
 :precondition
  (and
   (unused_p1)
   (available_b0)
   (wood_b0_pine)
   (surface-condition_b0_rough)
   (boardsize_b0_s3)
  )
 :effect (and
  (not (unused_p1))
  (colour_p1_natural)
  (treatment_p1_untreated)
  (available_p1)
  (wood_p1_pine)
  (surface-condition_p1_rough)
  (boardsize_b0_s1)

 )
)
)
