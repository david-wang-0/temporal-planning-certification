(define (domain elevators)
    (:requirements :typing :negative-preconditions :durative-actions :duration-inequalities)
    (:types floor - object elevator - object passenger - object)

    (:predicates
        (elevator-at ?e - elevator ?f - floor)
        (passenger-at ?e - passenger ?f - floor)
        (in-elevator ?p - passenger ?e - elevator)
        (elevator-door-open ?e - elevator)
    )
    
    (:functions (elevator-duration ?from - floor ?to - floor) - number)

    (:durative-action move-elevator
        :parameters (?e - elevator ?from - floor ?to - floor)
        :duration (= ?duration (elevator-duration ?from ?to))
        :condition (and (at start (elevator-at ?e ?from))
                        (over all (not (elevator-door-open ?e))))
        :effect (and (at start (not (elevator-at ?e ?from))) 
                     (at end (elevator-at ?e ?to)))
    )

    (:durative-action open-elevator-door
        :parameters (?e - elevator)
        :duration (= ?duration 1)
        :condition (at start (not (elevator-door-open ?e)))
        :effect (at end (elevator-door-open ?e))
    )

    (:durative-action close-elevator-door
        :parameters (?e - elevator)
        :duration (= ?duration 1)
        :condition (at start (elevator-door-open ?e))
        :effect (at end (not (elevator-door-open ?e)))
    )
    
    (:durative-action enter-elevator
        :parameters (?p - passenger ?e - elevator ?f - floor)
        :duration (<= ?duration 1)
        :condition (and (at start (and (passenger-at ?p ?f) 
                                  (elevator-at ?e ?f)))
                        (over all (elevator-door-open ?e)))
        :effect (and (at start (not (passenger-at ?p ?f))) 
                     (at end (in-elevator ?p ?e)))
    )
    
    (:durative-action exit-elevator
        :parameters (?p - passenger ?e - elevator ?f - floor)
        :duration (<= ?duration 1)
        :condition (and (at start (and (in-elevator ?p ?e) 
                                  (elevator-at ?e ?f)))
                        (over all (elevator-door-open ?e)))
        :effect (and (at start (not (in-elevator ?p ?e)))
                     (at end (passenger-at ?p ?f)))
    )
)