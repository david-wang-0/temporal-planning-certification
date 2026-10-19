(define (problem instance)
 (:domain matchcellar)
 (:objects
    match0 - match
    fuse0 fuse1 fuse2 - fuse
)
 (:init
  (handfree)
  (unused match0)
  (= (dur-lit-lb match0) 5)
  (= (dur-lit-ub match0) 5)
  (= (dur-mend fuse0) 2)
  (= (dur-mend fuse1) 2)
  (= (dur-mend fuse2) 2)
  (= (spare-fuses) 3)
  (= (matches-lit) 0)
)
 (:goal
  (and
     (mended fuse0)
     (mended fuse1)
     (mended fuse2)
))
 (:metric minimize (matches-lit))
)
