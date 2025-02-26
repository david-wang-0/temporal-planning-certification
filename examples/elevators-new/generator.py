
from random import randint, seed
from collections import namedtuple
from jinja2 import Template
import itertools

PDDL_TEMPLATE = Template('''(define (problem {{problem_name}})
  (:domain elevators)
  (:objects
  {% for e in elevators %}
    {{e.name}} - elevator
  {% endfor %}
  {% for p in persons %}
    {{p.name}} - person
  {% endfor %}
  {% for f in floors %}
    {{f.name}} - floor
  {% endfor %}
  )

  (:init
  {% for r in robots %}
    (exD {{r.name}})
    (exC {{r.name}})
    (= (dur_c1 {{r.name}}) {{r.dur_c1}})
    (= (dur_c2 {{r.name}}) {{r.dur_c2}})
    {% for p in parallels %}
    (= (dur_d {{r.name}} {{p}}) {{r.dur_d[p]}})
    {% endfor %}
  {% endfor %}
  )

  (:goal
    (and
    {% for p in robots %}
      (pG {{r.name}})
    {% endfor %}
    )
  )
)
''')

Floor = namedtuple('Floor', ['name', 'level'])

Person = namedtuple('Person', ['name', 'dur_enter', 'dur_exit'])

Elevator = namedtuple('Elevator', ['name', 'speed', 'init_loc'])

EFF = namedtuple('EFF', ['elevator_name', 'floor_from', 'floor_to', 'time'])

def is_possible(dur_c1, dur_c2, dur_d):
    return all(abs(dur_d2 - dur_d1) < (dur_c1 + dur_c2)
               for dur_d1 in dur_d for dur_d2 in dur_d)

def guess(n, lbound=1, ubound=50):
    return tuple(randint(lbound, ubound) for _ in range(n))

def calc_duration(l1, l2, speed):
    return ceil(abs(l1 - l2) / speed)

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

def mk_person(name, floors):
    dur_enter, dur_exit = guess(2, ubound=5)
    return Person(name=name, dur_enter=dur_enter, dur_exit=dur_exit, init_loc=guess(1, ubound=floors))

def mk_persons(n, floors):
    res = []
    for i in range(n):
        p = mk_person(("p%s" % i), floors)
        res.append(p)
    return res

def mk_elevator(name, floors):
    return Elevator(name=name, speed=guess(1, ubound=2), init_loc=guess(1, ubound=floors))

def mk_elevators(n, floors):
    res = []
    for i in range(n):
        e = mk_elevator(("e%s" % i), floors)
        res.append(e)
    return res

def mk_floor(n):
    return Floor(name=("f%s" % n), level=n)

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
            eff = mk_eff(f_in, f_to, e)
            res.append(eff)
    return res

def main():
    seed(42)

    for n in range(1, 5):
        for k in range(1, 3):
            for i in range(1, 4)
            pname = "instance_%d_%d_%d" % (n, k, i)
            persons = mk_persons(n, i)
            elevator = mk_elevators(k, i)
            floors = mk_floors(i)

            effs = mk_effs(elevators, floors)

            txt = PDDL_TEMPLATE.render(
                problem_name=pname,
                persons=persons,
                elevators=elevators,
                floors=floors,
                effs=effs
            )
            with open("instances/%s.pddl" % pname, 'wt') as fh:
                fh.write(txt)


if __name__ == '__main__':
    main()
