(define (problem instance_1_4)
  (:domain sync)
  (:objects
  
    r0 - Robot
  
  
    p0 - Parallel
  
    p1 - Parallel
  
    p2 - Parallel
  
    p3 - Parallel
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 5)
    (= (dur_c2 r0) 4)
    
    (= (dur_d r0 p0) 15)
    
    (= (dur_d r0 p1) 29)
    
    (= (dur_d r0 p2) 38)
    
    (= (dur_d r0 p3) 18)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)