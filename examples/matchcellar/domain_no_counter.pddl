(define (domain matchcellar)
    (:requirements :typing :durative-actions :numeric-fluents)
    (:types
        match fuse
    )
    (:predicates
        (handfree)
        (unused ?match - match)
        (mended ?fuse - fuse)
        (light ?match - match)
    )
    (:functions
        (dur-lit-lb ?x - match)
        (dur-lit-ub ?x - match)
        (dur-mend ?x - fuse)
        (spare-fuses)
    )

    (:durative-action LIGHT_MATCH
        :parameters (?match - match)
        :duration (and
            (>= ?duration (dur-lit-lb ?match))
            (<= ?duration (dur-lit-ub ?match)))
        :condition (and
            (at start (unused ?match)))
        :effect (and
            (at start (not (unused ?match)))
            (at start (light ?match))
            (at end (not (light ?match))))
    )

    (:durative-action MEND_FUSE
        :parameters (?fuse - fuse ?match - match)
        :duration (= ?duration (dur-mend ?fuse))
        :condition (and
            (at start (handfree))
            (over all (light ?match))
            (at start (> (spare-fuses) 0)))
        :effect (and
            (at start (not (handfree)))
            (at start (decrease (spare-fuses) 1))
            (at end (mended ?fuse))
            (at end (handfree)))
    )
)