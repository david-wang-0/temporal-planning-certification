(define (problem instance)
 (:domain matchcellar)
 (:objects
    match0 - match
    fuse0 - fuse
)
 (:init
  (handfree)
  (unused match0)
  (= (dur-lit-lb match0) 5)
  (= (dur-lit-ub match0) 6)
  (= (dur-mend fuse0) 5)
  (= (spare-fuses) 2)
  (= (matches-lit) 0)
)
 (:goal
  (and
     (mended fuse0)
))
 (:metric minimize (matches-lit))
)
