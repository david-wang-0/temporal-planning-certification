import json
import sys
import re


def convert_update(s):
    s = s.replace(':=', '=')
    s = s.replace(',', ';')
    return s


def convert_expression(s):
    exp = r'([^=<>!&]+)=([^=<>!&]+)'
    return re.sub(exp, r'\1==\2', s)


def strip_action(s):
    exp = r'(.*)[?!]\s*'
    return re.sub(exp, r'\1', s)


def convert_action(s):
    return s.replace('?', '_in').replace('!', '_out')


def is_in(s):
    exp = r'(.*)[?]\s*'
    return True if re.match(exp, s) else False


def is_out(s):
    exp = r'(.*)[!]\s*'
    return True if re.match(exp, s) else False


template = \
    """system:{system_id}

{clocks}

{vars}

{actions}
event:_

{processes}

{sync}
"""

model_template = \
    """process:{process}

  {nodes}

  {edges}
"""


def dict_to_tchecker_string(d):

    def mk_clocks(clocks):
        clocks = clocks.split(",")
        clocks = [s.strip() for s in clocks]
        return ("\n".join("clock:1:{}".format(c) for c in clocks))

    def mk_vars(vars):
        def split_var(s):
            name, s = s.split('[')
            l, s = s.split(':')
            r, s = s.split(']')
            return name, l, r
        vars = vars.split(',')
        vars = [] if vars == [''] else vars
        vars = [split_var(v) for v in vars]
        return ("\n".join("int:1:{}:{}:0:{}".format(l, u, name) for (name, l, u) in vars))

    def mk_attributes(d):
        s = " : ".join("{}:{}".format(k, v) for k, v in d.items() if v != None)
        return "{{{}}}".format(s)

    def mk_loc(loc):
        return "l{}".format(loc)

    def mk_edge(process, edge):
        t = "edge:{process}:{source}:{target}:{action}{attributes}"
        update = convert_update(edge['update'])
        d = {
            'provided': convert_expression(edge['guard']) if edge['guard'] else None,
            'do': update if update else None
        }
        action = edge['label'] if edge['label'] else "_"
        return t.format(
            process=process,
            source=mk_loc(edge['source']),
            target=mk_loc(edge['target']),
            action=convert_action(action),
            attributes=mk_attributes(d)
        )

    def mk_actions(actions):
        return "\n".join("event:{}".format(convert_action(action)) for action in actions)

    def mk_location(process, node, committed, urgent, initial):
        t = "location:{process}:{id}{attributes}"
        d = {
            'initial': '' if initial else None,
            'labels': node['name'] if node['name'] else None,
            'invariant': convert_expression(node['invariant']) if node['invariant'] else None,
            'urgent': " " if urgent else None
        }

        return t.format(
            process=process,
            id=mk_loc(node['id']),
            attributes=mk_attributes(d)
        )

    def mk_automaton(automaton):
        process = automaton['name']

        def is_initial(id):
            return id == automaton['initial']

        def is_committed(id):
            committed = automaton['committed'] if 'committed' in automaton else [
            ]
            return id in committed

        def is_urgent(id):
            urgent = automaton['urgent'] if 'urgent' in automaton else []
            return id in urgent

        edges = [mk_edge(process, edge) for edge in automaton['edges']]
        nodes = [mk_location(process, node, is_committed(
            node['id']), is_urgent(node['id']), is_initial(node['id'])) for node in automaton['nodes']]

        return model_template.format(
            process=process,
            edges="\n  ".join(edges),
            nodes="\n  ".join(nodes)
        )

    def combs_to_sync(combs):
        combs = ["{}@{}{}".format(p, convert_action(
            a), "?" if weak else "") for p, a, weak in combs]
        return "sync:{}".format(":".join(combs))

    process_actions = [(automaton['name'], [edge['label']
                                            for edge in automaton['edges'] if edge['label']]) for automaton in d['automata']]

    broadcast = d['broadcast'] if 'broadcast' in d and d['broadcast'] else []

    def add(d, k, v):
        if k in d:
            d[k] += [v]
        else:
            d[k] = [v]

    broadcast_in = {}
    for p, actions in process_actions:
        for a in actions:
            if is_in(a) and strip_action(a) in broadcast:
                add(broadcast_in, strip_action(a), p)

    broadcast_out = {}
    for p, actions in process_actions:
        for a in actions:
            if is_out(a) and strip_action(a) in broadcast:
                add(broadcast_out, strip_action(a), p)

    binary_in = {}
    for p, actions in process_actions:
        for a in actions:
            if is_in(a) and strip_action(a) not in broadcast:
                add(binary_in, strip_action(a), p)

    binary_out = {}
    for p, actions in process_actions:
        for a in actions:
            if is_out(a) and strip_action(a) not in broadcast:
                add(binary_out, strip_action(a), p)

    broadcast_combs = []
    for a, ps in broadcast_out.items():
        if a not in broadcast_in or not broadcast_in[a]:
            print("Broadcast channel without receivers:", a)
            continue
        ins = sorted(set(broadcast_in[a]))
        ins = [(p, a + "?", True) for p in ins]
        for p in sorted(set(ps)):
            broadcast_combs.append([(p, a + "!", False)] + ins)

    binary_combs = []
    for a, ps in binary_out.items():
        if a not in binary_in or not binary_in[a]:
            print("Binary channel without receivers:", a)
            continue
        ins = sorted(set(binary_in[a]))
        for p in sorted(set(ps)):
            for q in ins:
                if p != q:
                    binary_combs.append(
                        [(p, a + "!", False), (q, a + "?", False)])

    sync = "\n".join(combs_to_sync(c) for c in broadcast_combs)
    sync += "\n".join(combs_to_sync(c) for c in binary_combs)

    actions = set([a for _, actions in process_actions for a in actions])

    automata = [mk_automaton(a) for a in d['automata']]

    return template.format(
        system_id='the_system',
        processes="\n\n".join(automata),
        clocks=mk_clocks(d['clocks']),
        vars=mk_vars(d['vars']),
        actions=mk_actions(actions),
        sync=sync)


def convert_from_file(input_file):
    with open(input_file) as f:
        d = json.load(f)
        return dict_to_tchecker_string(d)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: convert.py file_in file_out")
        sys.exit(0)

    s = convert_from_file(sys.argv[1])
    f = sys.argv[2]
    with open(f, 'w') as f:
        f.write(s)
