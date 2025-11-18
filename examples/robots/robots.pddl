(define (domain blocksworld)
    (:requirements :strips :durative-actions :typing)
    (:predicates
        (in-room ?o ?r)
        (arm-empty)
        (holding ?r ?o)
        (idle ?r)
    )
    (:types
        robot block door room - object
    )
    (:durative-action pick-up
        :parameters (?r - robot ?b - block ?rm - room)
        :duration (= ?duration 2)
        :condition (and
            (at start (and
                    (idle ?r)
                    (in-room ?b ?rm)
                    (arm-empty ?r)
                ))
            (over all (and
                    (in-room ?r ?rm)
                )))
        :effect (and
            (at start (and
                    (not (in-room ?b ?rm))
                    (not (idle ?r))
                    (not (arm-empty ?r))
                ))
            (at end (and
                    (idle ?r)
                    (holding ?r ?b)
                )))
    )
)