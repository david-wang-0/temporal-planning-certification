(define (problem instance_1_2)
  (:domain sync)
  (:objects
  
    r0 - Robot
  
  
    p0 - Parallel
  
    p1 - Parallel
  
  )

  (:init
  
    (exD r0)
    (exC r0)
    (= (dur_c1 r0) 2)
    (= (dur_c2 r0) 1)
    
    (= (dur_d r0 p0) 44)
    
    (= (dur_d r0 p1) 48)
    
  
  )

  (:goal
    (and
    
      (pG r0)
    
    )
  )
)