import json
import sys
import re

def convert_update(s):
    s = s.replace(':=', "'=")
    return s


def convert_expression(s):
    exp = r'(.*[^=<>!])=([^=<>!].*)'
    s = re.sub(exp, r'\1==\2', s)
    return s.replace('&&','&').replace('==','=')


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


model_template = \
    """(* convert-imi {system_id} *)

var
  {clocks}

  {vars}

{processes}

{init}
"""

process_template = \
    """automaton {process}

  {actions}
  
  {nodes}

end (* {process} *)
"""

def dict_to_imitator_string(d):

    def mk_clocks(clocks):
        clocks = clocks.split(",")
        clocks = [s.strip() for s in clocks]
        return (",".join("{}".format(c) for c in clocks) + ": clock;")

    def mk_vars(vars):
        def split_var(s):
            name, s = s.split('[')
            l, s = s.split(':')
            r, s = s.split(']')
            return name, l, r
        vars = vars.split(',')
        vars = [] if vars == [''] else vars
        if vars == []: return ""
        vars = [split_var(v) for v in vars]
        return (",".join(name for (name, l, u) in vars) + ": discrete;")

    def mk_attributes(d):
        s = " : ".join("{}:{}".format(k, v) for k, v in d.items() if v != None)
        return "{{{}}}".format(s)

    def mk_loc(loc):
        return "l{}".format(loc)

    def mk_edge(edge):
        t = "when {guard} {action} {update} goto {target};"
        update = 'do {'+convert_update(edge['update']) + '}' if edge['update'] else ''
        d = {
            'do': update if update else None
        }
        guard = convert_expression(edge['guard']) if edge['guard'] else 'True'
        action = 'sync '+edge['label'] if edge['label'] else ''
        return t.format(
            guard=guard,
            target=mk_loc(edge['target']),
            update=update,
            action=convert_action(action)
        )

    def mk_actions(actions):
        return 'synclabs: ' + ", ".join(list(set(convert_action(action) for action in actions))) + ";"

    def mk_location(process, node, urgent, committed, initial, accepting, edges):
        t = "{urgent}{accepting}loc {id}: while {invariant} wait (* {name}:{initial}{committed} *){edges}"
        d = {
            'initial': '' if initial else None,
        }
        invariant = convert_expression(node['invariant']) if node['invariant'] else 'True'
        edges = [mk_edge(edge) for edge in edges]
        
        return t.format(
            process=process,
            id=mk_loc(node['id']),
            attributes=mk_attributes(d),
            invariant=invariant,
            name=node['name'] if node['name'] else '',
            urgent='urgent ' if urgent else '',
            committed=' committed' if committed else '',
            initial=' initial' if initial else '',
            accepting='accepting ' if accepting else '',
            edges = "\n    "+"\n    ".join(edges)
        )

    def mk_automaton(automaton):
        def name(id):
            ns = [node['name'] for node in automaton['nodes'] if node['id']==id ]
            if len(ns)==1:
                return ns[0]
            else:
                return None
            
        def is_initial(id):
            return id == automaton['initial']

        def is_urgent(id):
            urgent = automaton['urgent'] if 'urgent' in automaton else []
            return id in urgent

        def is_committed(id):
            committed = automaton['committed'] if 'committed' in automaton else []
            return id in committed

        def is_accepting(id):
            accepting = automaton['accepting'] if 'accepting' in automaton else []
            return name(id) in accepting

        def filter_edges(id,all_edges):
            edges = [e for e in all_edges if e[u'source']==id]
            return edges

        process = automaton['name']

        nodes = [mk_location(process, node,
                     is_urgent(node['id']), is_committed(node['id']),is_initial(node['id']),
                     is_accepting(node['id']),filter_edges(node['id'],automaton['edges']))
                 for node in automaton['nodes']]

        actions = mk_actions([edge['label'] for edge in automaton['edges'] if edge['label']])
        
        return process_template.format(
            process=process,
            nodes="\n\n  ".join(nodes),
            actions=actions
        )

    def mk_init(d):
        inits = d['inits'].split(',')
        inits = "\n  & ".join(inits)
        return 'init := \n    {};'.format(inits)
        
    automata = [ mk_automaton(a) for a in d['automata']]

    return model_template.format(
        system_id=sys.argv[1],
        processes="\n\n".join(automata),
        clocks=mk_clocks(d['clocks']),
        vars=mk_vars(d['vars']),
        init=mk_init(d))

def munta_to_imi_style(d):
    """Transform the TA from MUNTA towards IMITATOR format (in dict d)
        - transform CCS communication a! | a? to CSP communication a_S_T | a_S_T
        - eliminate committed locations by introducing Boolean variables cmtd_S
        - add initialisation of locations and cmtd variables
        The syntax remains MUNTA syntax, except adding an 'init' field
    """
    def add(d, k, v):
        if k in d:
            if not v in d[k]:
                d[k] += [v]
        else:
            d[k] = [v]

    def extend(d,attribute,connective,update):
        if attribute in d and d[attribute]:
            new_attribute = d[attribute]+connective+update if update else d[attribute]
        else:
            new_attribute = update
        return d.update({attribute:new_attribute})

    def architecture(d):
        in_procs={}
        out_procs={}
        for a in d['automata']:
            proc = a['name']
            for e in a['edges']:
                label = e['label']
                if label:
                    if is_in(label):
                        add(in_procs,strip_action(label),proc)
                    elif is_out(label):
                        add(out_procs,strip_action(label),proc)
        return (in_procs,out_procs)

    procs_with_commit = [ a['name'] for a in d['automata'] if 'committed' in a and a['committed'] ]
    none_committed = " && ".join("cmtd_{}==0".format(p) for p in procs_with_commit)
        
    def copy_edge(proc,e,committed,ins,outs):

        def commit_edge(partner,e):
            if (e['source'] in committed) != (e['target'] in committed):
                commit_update = "cmtd_{proc}=1-cmtd_{proc}".format(proc=proc)
                extend(e,'update',',',commit_update)            
            if e['source'] in committed:
                return [e]
            else:
                e2 = dict(e)
                commit_guard = "{}".format(none_committed)
                extend(e,'guard',' & ',commit_guard)
                result = [e]
                if partner and partner in procs_with_commit:
                    commit_guard = "cmtd_{}==1".format(partner,commit_guard)
                    extend(e2,'guard',' & ',commit_guard)
                    result.append(e2)
                return result
 
        label = e['label']
        if label=="":
            return commit_edge(None,e)
        elif is_in(label):
            lab = strip_action(label)
            e_copies = []
            if lab in outs:
                for o in outs[lab]:
                    new_e = dict(e)
                    new_e['label'] = '{}_{}_{}'.format(lab,proc,o)
                    e_copies += commit_edge(o,new_e)
            else:
                print('WARNING: action {} has no output partner'.format(label)) 
            return e_copies
        elif is_out(label):
            lab = strip_action(label)
            e_copies = []
            if lab in ins:
                for i in ins[lab]:
                    new_e = dict(e)
                    new_e['label'] = '{}_{}_{}'.format(lab,i,proc)
                    e_copies += commit_edge(i,new_e)
            else:
                print('WARNING: action {} has no input partner'.format(label)) 
            return e_copies
        else:
            e.update(label='{}_{}'.format(label,proc))
            return commit_edge(None,e)
        
    def copy_edges(proc,edges,commmitted,ins,outs):
        return [new_e for old_e in edges
                        for new_e in copy_edge(proc,old_e,committed,ins,outs) ]

    def accepting_locs(s):
        exp = r'E<>(.*)'
        m = re.match(exp,s)
        if (m):
            s = m.group(1)
        else:
            print("WARNING: couldn't get accepting locations from formula {}".format(s))
            return []
        exp = r'\((.*)\)'
        m = re.match(exp,s.strip())
        if (m): s = m.group(1)
        result = []
        locs = [l.strip() for l in s.split('||')]
        exp = r'([a-zA-Z0-9_]+)\.([a-zA-Z0-9_]+)$'
        for l in locs:
            m = re.match(exp,l)
            if (m):
                result.append(m.group(1,2))
            else:
                print("WARNING: couldn't get accepting location from {}".format(l))
                return []
        return result
                       
    def filter_accepting(proc,accepting):
        return [ loc for (p,loc) in accepting if p==proc ]
    
    def init_clocks():
        clocks = d['clocks'].split(",")
        clocks = [s.strip() for s in clocks]
        for c in clocks:
            extend(d,'inits',',',"{} = 0".format(c))
    
    init_clocks()
    (ins,outs) = architecture(d)
    accepting = accepting_locs(d['formula']) if 'formula' in d else []
    
    for a in d['automata']:
        proc = a['name']
        committed = a['committed'] if 'committed' in a else []
        a.update(edges=copy_edges(proc,a['edges'],committed,ins,outs))
        extend(d,'inits',',',"loc[{}] = l{}".format(proc,a['initial']))
        if proc in procs_with_commit:
            extend(d,'vars',',',"cmtd_{}[0:1]".format(proc))
            init_commit = 1 if a['initial'] in committed else 0
            extend(d,'inits',',',"cmtd_{} = {}".format(proc,init_commit))
        a.update(accepting=filter_accepting(proc,accepting))

def convert_from_file(input_file):
    with open(input_file) as f:
        d = json.load(f)
        if 'broadcast' in d and d['broadcast']:
            sys.exit("ERROR: broadcast actions are NOT SUPPORTED")
        munta_to_imi_style(d)
        # print(json.dumps(d,indent=4))
        return dict_to_imitator_string(d)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: convert-imi.py file_in file_out")
        sys.exit(0)

    s = convert_from_file(sys.argv[1])
    f = sys.argv[2]
    with open(f, 'w') as f:
        f.write(s)
