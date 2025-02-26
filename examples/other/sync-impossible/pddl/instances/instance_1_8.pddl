(define (problem instance_1_8)
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
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 5)
    (= (dur_c2 r0) 2)
    
    (= (dur_d r0 p0) 46)
    
    (= (dur_d r0 p1) 5)
    
    (= (dur_d r0 p2) 3)
    
    (= (dur_d r0 p3) 43)
    
    (= (dur_d r0 p4) 15)
    
    (= (dur_d r0 p5) 50)
    
    (= (dur_d r0 p6) 19)
    
    (= (dur_d r0 p7) 6)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)