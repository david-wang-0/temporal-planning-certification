(define (domain elevators)
    (:requirements :typing :negative-preconditions :durative-actions)
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
        :duration (= ?duration 1)
        :condition (and (at start (and (passenger-at ?p ?f) 
                                  (elevator-at ?e ?f)))
                        (over all (elevator-door-open ?e)))
        :effect (and (at start (not (passenger-at ?p ?f))) 
                     (at end (in-elevator ?p ?e)))
    )
    
    (:durative-action exit-elevator
        :parameters (?p - passenger ?e - elevator ?f - floor)
        :duration (= ?duration 1)
        :condition (and (at start (and (in-elevator ?p ?e) 
                                  (elevator-at ?e ?f)))
                        (over all (elevator-door-open ?e)))
        :effect (and (at start (not (in-elevator ?p ?e)))
                     (at end (passenger-at ?p ?f)))
    )

    ; (:invariant
    ;     :name elevator-at-most-one-floor
    ;     :vars (?e - elevator ?f0 ?f1 - floor)
    ;     :set-constraint (or (not (elevator-at ?e ?f0)) (not (elevator-at ?e ?f1)) (= ?f0 ?f1))
    ; )

    ; ; (:invariant
    ; ;     :name passenger-at-most-one-floor
    ; ;     :vars (?p - passenger ?f0 ?f1 - floor)
    ; ;     :set-constraint (or (not (passenger-at ?p ?f0)) (not (passenger-at ?p ?f1)) (= ?f0 ?f1))
    ; ; )
      
    ; ; (:invariant
    ; ;     :name passenger-at-most-one-elevator
    ; ;     :vars (?p - passenger ?e0 ?e1 - elevator)
    ; ;     :set-constraint (or (not (in-elevator ?p ?e0)) (not (in-elevator ?p ?e1)) (= ?e0 ?e1))
    ; ; )

    ; ; (:invariant
    ; ;     :name passenger-either-at-floor-or-in-elevator
    ; ;     :vars (?p - passenger ?e - elevator ?f - floor)
    ; ;     :set-constraint (or (not (in-elevator ?p ?e)) (not (passenger-at ?p ?f)))
    ; ; )

    ; (:invariant
    ;     :name passenger-at-most-one-floor-elevator
    ;     :vars (?p - passenger ?f0 ?f1 - floor ?e0 ?e1 - elevator)
    ;     :set-constraint (and (or (not (passenger-at ?p ?f0)) (not (passenger-at ?p ?f1)) (= ?f0 ?f1))
    ;                           (or (not (in-elevator ?p ?e0)) (not (in-elevator ?p ?e1)) (= ?e0 ?e1))
    ;                           (or (not (in-elevator ?p ?e0)) (not (passenger-at ?p ?f0))))
    ; )
)