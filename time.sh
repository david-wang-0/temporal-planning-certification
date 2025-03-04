#!/bin/bash

run_example () {
    { { ./run_example.sh examples/elevators-new elevators.pddl instances/instance_${1}_${2}_${3}.pddl ; } 2>&1 ; } >> test.log
}
export -f run_example

# trap 'pkill -9 -P $$; echo Exit; exit' SIGINT SIGTERM

# while [[$x -lt $x_max || $y -lt $y_max]]
# do  
#     # do something
#     let "x1 = $x - 1"
#     let "y1 = $y + 1"
#     while [[text $x1 -lt 1 || $y1 -gt $y_max || $x1 -gt $x_max]]
#     do
#         if [[$x1 -lt 1]];
#         then
#             let "x1 = $y1"
#             let "y1 = 1"
#         else
#             let "x1 = $x1 - 1"
#             let "y1 = $y1 + 1"
#         fi
#     done
#     let "x = $x1"
#     let "y = $y1"
# done

# first do elevators
# diagonalise people and floors
for e in {1..3};
do
    let "p = 1"
    let "p_max = 9"
    let "f = 1"
    let "f_max = 8"
    while [ $p -lt $p_max ] || [ $f -lt $f_max ]
    do  
        f_act=$((f + 1))
        echo "Running instance: ${p}_${e}_${f_act}" >> test.log
        timeout -f 5m bash -c \
            '{ { time run_example ${0} ${1} ${2} ; } 2>&1 ; } >> test.log' \
            $p $e $f_act
        x1=$((p - 1))
        y1=$((f + 1))
        while [ $x1 -lt 1 ] || [ $x1 -gt $p_max ] || [ $y1 -gt $f_max ]
        do
            if [ $x1 -lt 1 ];
            then
                x1=$y1
                y1=1
            else
                x1=$((x1 - 1))
                y1=$((y1 + 1))
            fi
        done
        p=$x1
        f=$y1
    done
done
# wait