from random import randint, seed
from collections import namedtuple
from jinja2 import Template

PDDL_TEMPLATE = Template('''(define (problem {{problem_name}})
  (:domain sync)
  (:objects
  {% for r in robots %}
    {{r.name}} - Robot
  {% endfor %}
  {% for p in parallels %}
    {{p}} - Parallel
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
    {% for r in robots %}
      (pG {{r.name}})
    {% endfor %}
    )
  )
)
''')

ANML_TEMPLATE = Template('''
{% for r in robots %}
instance Robot {{r.name}};
{% endfor %}
{% for p in parallels %}
instance Parallel {{p}};
{% endfor %}

{% for r in robots %}
[start] exD({{r.name}}) := true;
[start] exC({{r.name}}) := true;
[start] pA({{r.name}}) := false;
[start] pG({{r.name}}) := false;

dur_c1({{r.name}}) := {{r.dur_c1}};
dur_c2({{r.name}}) := {{r.dur_c2}};

{% for p in parallels %}
[start] pB({{r.name}}, {{p}}) := false;
[start] pX({{r.name}}, {{p}}) := false;
dur_d({{r.name}}, {{p}}) := {{r.dur_d[p]}};
{% endfor %}

[end] pG({{r.name}});
{% endfor %}
''')

TPP_TEMPLATE = Template('''
(define (control-knowledge pddltaCk) (:domain sync) (:problem {{problem_name}})
    (:temporal-constraints
        (and
{% for r in robots %}
{% for p in parallels %}
            (t-forall (?s - (compiled_d_start {{r.name}} {{p}})) (t-exists (?e - (compiled_d_end {{r.name}} {{p}})) (and (>= (- ?e ?s) (dur_d {{r.name}} {{p}})) (<= (- ?e ?s) (dur_d {{r.name}} {{p}})))))
            (t-forall (?e - (compiled_d_end {{r.name}} {{p}})) (t-exists (?s - (compiled_d_start {{r.name}} {{p}})) (and (>= (- ?e ?s) (dur_d {{r.name}} {{p}})) (<= (- ?e ?s) (dur_d {{r.name}} {{p}})))))
{% endfor %}
            (t-forall (?s - (compiled_c1_start {{r.name}})) (t-exists (?e - (compiled_c1_end {{r.name}})) (and (>= (- ?e ?s) (dur_c1 {{r.name}})) (<= (- ?e ?s) (dur_c1 {{r.name}})))))
            (t-forall (?e - (compiled_c1_end {{r.name}})) (t-exists (?s - (compiled_c1_start {{r.name}})) (and (>= (- ?e ?s) (dur_c1 {{r.name}})) (<= (- ?e ?s) (dur_c1 {{r.name}})))))
            (t-forall (?s - (compiled_c2_start {{r.name}})) (t-exists (?e - (compiled_c2_end {{r.name}})) (and (>= (- ?e ?s) (dur_c2 {{r.name}})) (<= (- ?e ?s) (dur_c2 {{r.name}})))))
            (t-forall (?e - (compiled_c2_end {{r.name}})) (t-exists (?s - (compiled_c2_start {{r.name}}0)) (and (>= (- ?e ?s) (dur_c2 {{r.name}})) (<= (- ?e ?s) (dur_c2 {{r.name}})))))
{% endfor %}
        )
    )
)
''')

Robot = namedtuple('Robot', ['name', 'dur_c1', 'dur_c2', 'dur_d'])

def is_possible(dur_c1, dur_c2, dur_d):
    return all(abs(dur_d2 - dur_d1) < (dur_c1 + dur_c2)
               for dur_d1 in dur_d for dur_d2 in dur_d)

def guess(n, lbound=1, ubound=50):
    return tuple(randint(lbound, ubound) for _ in range(n))

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

def mk_robot(name, parallels, possible):
    dur_c1, dur_c2 = guess(2, ubound=5)
    dur_d = guess_d(len(parallels), dur_c1 + dur_c2, possible)
    while is_possible(dur_c1, dur_c2, dur_d) != possible:
        dur_c1, dur_c2 = guess(2, ubound=5)
        dur_d = guess_d(len(parallels), dur_c1 + dur_c2, possible)
    return Robot(name=name, dur_c1=dur_c1, dur_c2=dur_c2,
                 dur_d={p:dur_d[i] for i,p in enumerate(parallels)})

def mk_robots(n, parallels):
    res = []
    n_possible = randint(0, n-1)
    for i in range(n):
        r = mk_robot(("r%s" % i), parallels, (i < n_possible))
        res.append(r)
    return res

def mk_parallels(n):
    return ["p%d" % i for i in range(n)]

def main():
    seed(42)

    for n in range(1, 2):
        for k in range(2, 10):
            pname = "instance_%d_%d" % (n, k)
            pars = mk_parallels(k)
            robots = mk_robots(n, pars)

            txt = PDDL_TEMPLATE.render(robots=robots,
                                       problem_name=pname,
                                       parallels=pars)
            with open("pddl/instances/%s.pddl" % pname, 'wt') as fh:
                fh.write(txt)
            with open("tpp/instances/%s.pddl" % pname, 'wt') as fh:
                fh.write(txt)

            txt = ANML_TEMPLATE.render(robots=robots,
                                       problem_name=pname,
                                       parallels=pars)
            with open("anml/instances/%s.anml" % pname, 'wt') as fh:
                fh.write(txt)

            txt = TPP_TEMPLATE.render(robots=robots,
                                      problem_name=pname,
                                      parallels=pars)
            with open("tpp/instances/%s.ck.pddl" % pname, 'wt') as fh:
                fh.write(txt)


if __name__ == '__main__':
    main()
