(define (domain test-dom)
  (:requirements :typing :durative-actions :disjunctive-preconditions)
  (:types thing - object)
  (:predicates 
      (p ?x - object)
      (q ?x - object)
      (r ?x - object)
      (s ?x - object)
    )
    (:durative-action a
    :parameters (?x - object)
    :duration  (= ?duration 10)
    :condition (and 
        (at start (not (r ?x)))
        (over all (or (p ?x) (q ?x)))
        (at end (r ?x))
    )
    :effect (and 
        (at start (p ?x))
        (at end (s ?x))
        )
    )
  
    (:durative-action b
        :parameters (?x - object)
        :duration (= ?duration 1)
        :condition (at start (p ?x))
        :effect (at start (and 
                (not (p ?x))
                (q ?x)
                (r ?x)
        ))
    )
)