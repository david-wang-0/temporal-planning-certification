# Adapted from work by Stefan Panjkovic, Andrea Micheli and Alessandro Cimatti
# https://es-static.fbk.eu/people/amicheli/resources/aaai22/

from random import randint, seed, sample
from collections import namedtuple
from jinja2 import Template
from math import ceil
import itertools

PDDL_TEMPLATE = Template('''(define (problem {{problem_name}})
  (:domain elevators)
  (:objects
  {%- for e in elevators %} 
    {{e.name}} - elevator 
  {%- endfor %}
  {% for p in persons %} 
    {{p.name}} - person 
  {%- endfor %}
  {% for f in floors %} 
    {{f.name}} - floor
  {%- endfor %}
  )

  (:init
  {%- for p in persons %}
    (person-on-floor {{p.name}} {{p.init_loc}})
  {%- endfor %}
  {% for p in persons %}
    (= (dur-enter {{p.name}}) {{p.dur_enter}})
    (= (dur-exit {{p.name}}) {{p.dur_exit}})
  {%- endfor %}
  {% for e in elevators %}
    (elevator-on-floor {{e.name}} {{e.init_loc}})
    (stopped {{e.name}})
  {%- endfor %}
  {% for eff in effs %}
    (= (travel-dur {{eff.elevator_name}} {{eff.floor_from}} {{eff.floor_to}}) {{eff.time}})
    (= (travel-dur {{eff.elevator_name}} {{eff.floor_to}} {{eff.floor_from}}) {{eff.time}})
  {%- endfor %}
  )

  (:goal
    (and
    {%- for p in persons %}
      (person-on-floor {{p.name}} {{p.goal_loc}})
    {%- endfor %}
    {% for g in pgs %}
      (person-on-floor {{g.person}} {{g.goal_loc}})
    {%- endfor %}
   

    )
  )
)
''')

# {% for g in egs %}
#     (elevator-on-floor {{g.elevator}} {{g.goal_loc}})
# {%- endfor %}

Floor = namedtuple('Floor', ['name', 'level'])

Person = namedtuple('Person', ['name', 'dur_enter', 'dur_exit', 'init_loc', 'goal_loc'])

Elevator = namedtuple('Elevator', ['name', 'speed', 'init_loc'])

EFF = namedtuple('EFF', ['elevator_name', 'floor_from', 'floor_to', 'time'])

# Can be easily removed for solvable problems 
ElevatorLoc = namedtuple('ElevatorLoc', ['elevator', 'goal_loc'])
PersonLoc = namedtuple('PersonLoc', ['person', 'goal_loc'])

def is_possible(dur_c1, dur_c2, dur_d):
    return all(abs(dur_d2 - dur_d1) < (dur_c1 + dur_c2)
               for dur_d1 in dur_d for dur_d2 in dur_d)

def guess(n, lbound=1, ubound=50):
    return tuple(randint(lbound, ubound) for _ in range(n))

def calc_duration(l1, l2, speed):
    return ceil(abs(l1 - l2) / speed)

# From 
def guess_d(n, bound, possible):
    res = []
    m, M = None, None
    for _ in range(n):
        lb = 1
        ub = 50
        if m is not None and possible:
            ub = lb + bound - 1
            lb = ub - bound + 1
        d = randint(lb, ub)
        if m is None or d < m:
            m = d
        if M is None or d < M:
            M = d
        res.append(d)
    return res

def floor_name(n):
    return "f%s" % n

def rand_floor(n):
    return floor_name(randint(0, n - 1))

def mk_person(name, floors):
    dur_enter, dur_exit = guess(2, ubound=5)
    init_loc = rand_floor(floors)
    goal_loc = rand_floor(floors)
    return Person(name=name, dur_enter=dur_enter, dur_exit=dur_exit, init_loc=init_loc, goal_loc=goal_loc)

def mk_persons(n, floors):
    res = []
    for i in range(n):
        p = mk_person(("p%s" % i), floors)
        res.append(p)
    return res

def mk_elevator(name, floors):
    init_loc = rand_floor(floors)
    speed = randint(1, 3)
    return Elevator(name=name, speed=speed, init_loc=init_loc)

def mk_elevators(n, floors):
    res = []
    for i in range(n):
        e = mk_elevator(("e%s" % i), floors)
        res.append(e)
    return res

def mk_floor(n):
    return Floor(name=floor_name(n), level=n)

def mk_floors(n):
    res = []
    for i in range(n):
        f = mk_floor(i)
        res.append(f)
    return res

def mk_eff(floor_from, floor_to, elevator):
    time = calc_duration(floor_from.level, floor_to.level, elevator.speed)
    return EFF(elevator_name=elevator.name, floor_from=floor_from.name, floor_to=floor_to.name, time=time)

def mk_effs(elevators, floors):
    res = []
    for e in elevators:
        for floors in list(itertools.combinations(floors, 2)):
            (f_from, f_to) = floors
            eff = mk_eff(f_from, f_to, e)
            res.append(eff)
    return res

def mk_impossible_goal(persons, elevators, floors):
    # lock = randint(1, 3)
    egs = []
    pgs = []
    # if (lock & 0b1):
    p, *tail = sample(persons, 1)
    f1, f2, *tail = sample(floors, 2)
    pgs.append(PersonLoc(person=p.name, goal_loc=f1.name))
    pgs.append(PersonLoc(person=p.name, goal_loc=f2.name))
    # if (lock & 0b10):
    #     e, *tail = sample(elevators, 1)
    #     f1, f2, *tail = sample(floors, 2)
    #     egs.append(ElevatorLoc(elevator=e.name, goal_loc=f1.name))
    #     egs.append(ElevatorLoc(elevator=e.name, goal_loc=f2.name))
    return pgs, egs
        

def main():
    seed(42)

    for n in range(1, 10):
        for k in range(1, 4):
            for i in range(2, 10):
                pname = "instance_%d_%d_%d" % (n, k, i)
                persons = mk_persons(n, i)
                elevators = mk_elevators(k, i)
                floors = mk_floors(i)

                effs = mk_effs(elevators, floors)

                pgs, egs = mk_impossible_goal(persons, elevators, floors)

                txt = PDDL_TEMPLATE.render(
                    problem_name=pname,
                    persons=persons,
                    elevators=elevators,
                    floors=floors,
                    effs=effs,
                    pgs=pgs,
                    egs=egs
                )
                with open("instances/%s.pddl" % pname, 'wt') as fh:
                    fh.write(txt)


if __name__ == '__main__':
    main()
