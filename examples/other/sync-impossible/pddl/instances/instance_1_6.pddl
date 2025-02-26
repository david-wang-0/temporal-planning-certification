(define (problem instance_1_6)
  (:domain sync)
  (:objects
  
    r0 - Robot
  
  
    p0 - Parallel
  
    p1 - Parallel
  
    p2 - Parallel
  
    p3 - Parallel
  
    p4 - Parallel
  
    p5 - Parallel
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 1)
    (= (dur_c2 r0) 1)
    
    (= (dur_d r0 p0) 25)
    
    (= (dur_d r0 p1) 7)
    
    (= (dur_d r0 p2) 23)
    
    (= (dur_d r0 p3) 23)
    
    (= (dur_d r0 p4) 39)
    
    (= (dur_d r0 p5) 17)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)