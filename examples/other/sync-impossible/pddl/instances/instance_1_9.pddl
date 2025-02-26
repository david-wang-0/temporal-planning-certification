(define (problem instance_1_9)
  (:domain sync)
  (:objects
  
    r0 - Robot
  
  
    p0 - Parallel
  
    p1 - Parallel
  
    p2 - Parallel
  
    p3 - Parallel
  
    p4 - Parallel
  
    p5 - Parallel
  
    p6 - Parallel
  
    p7 - Parallel
  
    p8 - Parallel
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 1)
    (= (dur_c2 r0) 4)
    
    (= (dur_d r0 p0) 18)
    
    (= (dur_d r0 p1) 30)
    
    (= (dur_d r0 p2) 41)
    
    (= (dur_d r0 p3) 24)
    
    (= (dur_d r0 p4) 11)
    
    (= (dur_d r0 p5) 24)
    
    (= (dur_d r0 p6) 23)
    
    (= (dur_d r0 p7) 14)
    
    (= (dur_d r0 p8) 43)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)