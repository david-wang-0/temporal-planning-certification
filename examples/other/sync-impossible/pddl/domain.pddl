(define (domain sync)

  (:requirements :typing :durative-actions :strips :fluents :conditional-effects)

  (:types
        Robot - object
        Parallel - object
    )

    (:functions
     (dur_c1 ?r - Robot)
     (dur_c2 ?r - Robot)
     (dur_d ?r - Robot ?p - Parallel)
    )

    (:predicates
        (pA ?r - Robot)
        (pB ?r - Robot ?p - Parallel)
        (pX ?r - Robot ?p - Parallel)
        (pG ?r - Robot)
        (exD ?r - Robot)
        (exC ?r - Robot)
    )

    (:durative-action c1
        :parameters (?r - Robot)
        :duration (= ?duration (dur_c1 ?r))
        :condition
        (and
         (at start (exD ?r))
         (at start (exC ?r))
         (at end (forall (?p - Parallel) (pB ?r ?p)))
        )
        :effect
        (and
         (at start (not (exC ?r)))
         (at end (exC ?r))

         (forall (?p - Parallel) (at start (not (pB ?r ?p))))

         (at start (pA ?r))
         (at end (not (pA ?r)))
        )
    )

    (:durative-action c2
        :parameters (?r - Robot)
        :duration (= ?duration (dur_c2 ?r))
        :condition
        (and
         (at end (forall (?p - Parallel) (pX ?r ?p)))
         (at start (exC ?r))
        )
        :effect
        (and
         (at start (not (exC ?r)))
         (at end (exC ?r))

         (forall (?p - Parallel) (at start (not (pX ?r ?p))))
         (at end (pG ?r))
        )
    )

    (:durative-action d
        :parameters (?r - Robot ?p - Parallel)
        :duration (= ?duration (dur_d ?r ?p))
        :condition
        (and
         (at start (pA ?r))
        )
        :effect
        (and
         (at start (not (exD ?r)))
         (at end (exD ?r))
         (at start (pB ?r ?p))
         (at end (pX ?r ?p))
        )
    )

)
