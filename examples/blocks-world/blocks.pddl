(define (domain blocksworld)
    (:requirements :strips :durative-actions)
    (:predicates (clear ?x)
                (on-table ?x)
                (arm-empty)
                (holding ?x)
                (on ?x ?y))

    (:durative-action pickup
        :parameters (?ob)
        :duration (= ?duration 1)
        :condition (and 
            (over all (arm-empty))
            (at start (and (on-table ?ob) (clear ?ob)))
        )
        :effect (and 
            (at end (holding ?ob))
            (at start (and 
                (not (clear ?ob)) 
                (not (on-table ?ob))
                (not (arm-empty))
            ))
        )
    )
    (:durative-action putdown
        :parameters  (?ob)
        :duration (= ?duration 1)
        :condition (at start (holding ?ob))
        :effect (and 
            (at start (not (holding ?ob)))
            (at end (and 
                (on-table ?ob) 
                (clear ?ob) 
                (arm-empty)
            ))
        )
    )

    (:durative-action stack
        :parameters  (?ob ?underob)
        :duration (= ?duration 1)
        :condition (and 
            (over all (holding ?ob))
            (at start (clear ?underob))
        )
        :effect (at end (and 
            (arm-empty) 
            (clear ?ob) 
            (on ?ob ?underob)
            (not (clear ?underob)) 
            (not (holding ?ob))
        ))
    )

    (:durative-action unstack
        :parameters  (?ob ?underob)
        :duration (= ?duration 1)
        :condition (at start (and 
            (on ?ob ?underob) 
            (clear ?ob) 
            (arm-empty)
        ))
        :effect (and 
            (at start (and 
                (not (on ?ob ?underob)) 
                (not (clear ?ob)) 
                (not (arm-empty))
            ))
            (at end (and 
                (holding ?ob) 
                (clear ?underob))
            )
        )
    )
)