(define (problem instance_1_7)
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
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 4)
    (= (dur_c2 r0) 5)
    
    (= (dur_d r0 p0) 8)
    
    (= (dur_d r0 p1) 25)
    
    (= (dur_d r0 p2) 6)
    
    (= (dur_d r0 p3) 36)
    
    (= (dur_d r0 p4) 19)
    
    (= (dur_d r0 p5) 41)
    
    (= (dur_d r0 p6) 40)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)