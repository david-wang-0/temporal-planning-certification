from random import randint
from collections import namedtuple
from jinja2 import Template

TEMPLATE = Template('''(define (problem {{problem_name}})
  (:domain sync)
  (:objects
  {% for r in robots %}
    {{r.name}} - Robot
  {% endfor %}
  )

  (:init
  {% for r in robots %}
    (exD1 {{r.name}})
    (exD2 {{r.name}})
    (exC {{r.name}})
    (= (dur_c1 {{r.name}}) {{r.dur_c1}})
    (= (dur_c2 {{r.name}}) {{r.dur_c2}})
    (= (dur_d1 {{r.name}}) {{r.dur_d1}})
    (= (dur_d2 {{r.name}}) {{r.dur_d2}})
  {% endfor %}
  )

  (:goal
    (and
    {% for r in robots %}
      (pG {{r.name}})
    {% endfor %}
    )
  )
)
''')


Robot = namedtuple('Robot', ['name', 'dur_c1', 'dur_c2', 'dur_d1', 'dur_d2'])

def is_possible(dur_c1, dur_c2, dur_d1, dur_d2):
    return abs(dur_d2 - dur_d1) < (dur_c1 + dur_c2)

def guess():
    return tuple(randint(1, 30) for _ in range(4))

def mk_robot(name, possible):
    dur_c1, dur_c2, dur_d1, dur_d2 = guess()
    while is_possible(dur_c1, dur_c2, dur_d1, dur_d2) != possible:
        dur_c1, dur_c2, dur_d1, dur_d2 = guess()
    return Robot(name=name, dur_c1=dur_c1, dur_c2=dur_c2, dur_d1=dur_d1, dur_d2=dur_d2)

def mk_robots(n):
    res = []
    n_possible = 0 #randint(0, n-1)
    for i in range(n):
        r = mk_robot(("r%s" % i), (i < n_possible))
        res.append(r)
    return res

def main():
    for n in range(1, 5):
        for k in range(0, 3):
            pname = "instance_%d_%d" % (n, k)
            txt = TEMPLATE.render(robots=mk_robots(n), problem_name=pname)
            with open("instances/%s.pddl" % pname, 'wt') as fh:
                fh.write(txt)


if __name__ == '__main__':
    main()
