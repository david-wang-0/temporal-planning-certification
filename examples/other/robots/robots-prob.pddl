

(define (problem rb)
    (:domain robots)
    (:objects 
        r1 r2 - robot 
        b - block 
        d - door 
        rm1 rm2 - room)   
    (:init 
        (connects d rm1 rm2) 
        (connects d rm2 rm1)
        (in-room r1 rm1)
        (in-room r2 rm2)
        (in-room b rm1)
        (idle r1) 
        (idle r2)
    )
    (:goal (and (in-room b rm2)))
)

