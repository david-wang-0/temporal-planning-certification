(define (problem instance_1_5)
  (:domain sync)
  (:objects
  
    r0 - Robot
  
  
    p0 - Parallel
  
    p1 - Parallel
  
    p2 - Parallel
  
    p3 - Parallel
  
    p4 - Parallel
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 2)
    (= (dur_c2 r0) 4)
    
    (= (dur_d r0 p0) 22)
    
    (= (dur_d r0 p1) 18)
    
    (= (dur_d r0 p2) 10)
    
    (= (dur_d r0 p3) 14)
    
    (= (dur_d r0 p4) 49)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)