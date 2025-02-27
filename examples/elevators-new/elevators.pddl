(define (domain elevators)
  (:requirements :typing :durative-actions :numeric-fluents)
  (:types elevator person floor - object)
  (:predicates 
    (person-on-floor ?p - person ?f - floor)
    (stopped ?e - elevator)
    (person-in-elevator ?p - person ?e - elevator)
    (elevator-on-floor ?e - elevator ?f - floor)
  )
          
  (:functions 
    (dur-enter ?p - person)
    (dur-exit ?p - person)
    (travel-dur ?e - elevator ?f_from ?f_to - floor)
  )

  (:durative-action enter-elevator
   :parameters (?p - person ?e - elevator ?f - floor)
   :duration  (= ?duration (dur-enter ?p))
   :condition (and (over all (and (elevator-on-floor ?e ?f) (stopped ?e)))
                   (at start (person-on-floor ?p ?f))
                   )
   :effect    (and (at start (not (person-on-floor ?p ?f)))
                   (at end (person-in-elevator ?p ?e))
                   )
   )

  (:durative-action leave-elevator
   :parameters (?p - person ?e - elevator ?f - floor)
   :duration  (= ?duration (dur-exit ?p))
   :condition (and (over all (and (elevator-on-floor ?e ?f) (stopped ?e)))
                   (at start (person-in-elevator ?p ?e))
                   )
   :effect    (and (at start (not (person-in-elevator ?p ?e)))
                   (at end (person-on-floor ?p ?f))
                   )
   )


  (:durative-action move-elevator
   :parameters (?e - elevator ?f ?g - floor)
   :duration  (= ?duration (travel-dur ?e ?f ?g))
   :condition (and (at start (elevator-on-floor ?e ?f))
                   )
   :effect    (and (at start (and (not (elevator-on-floor ?e ?f)) (not (stopped ?e))))
                   (at end (and (elevator-on-floor ?e ?g) (stopped ?e)))
                   )
   )
)