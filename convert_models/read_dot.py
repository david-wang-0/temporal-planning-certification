import re
from .parsers import *


class Node:
    def __init__(self, id, initial, vars_asmt, loc_labels, loc_asmt, zones, num_opt):
        self.id = id
        self.initial = initial
        self.vars_asmt = vars_asmt
        self.loc_labels = loc_labels
        self.loc_asmt = loc_asmt
        self.zones = zones
        self.num_opt = num_opt

    def __repr__(self):
        return "Node({}, {}, {}, {}, {}, {}, {})".format(self.id,
            self.initial,
            self.vars_asmt,
            self.loc_labels,
            self.loc_asmt,
            self.zones,
            self.num_opt)


class Edge:
    def __init__(self, source, sink, attr=None):
        self.source = source
        self.sink = sink
        self.attribute = attr

    def __repr__(self):
        return "Edge({}, {}, {})".format(self.source, self.sink, self.attribute)


int_re = re.compile("-?[0-9]+")

class IntParser(Parser):
    def match(self, s):
        match = int_re.match(s)
        if match == None or match.start() != 0:
            return None

        try:
            return int(s[0:match.end()]), s[match.end():]
        except ValueError:
            return None

class StringParser(Parser):
    def match(self, s):
        if s.startswith('"'):
            for i in range(1,len(s)):
                c = s[i]
                if c == '"':
                    return s[1:i], s[i+1:]
            return None
        if s.startswith("'"):
            for i in range(1,len(s)):
                c = s[i]
                if c == "'":
                    return s[1:i], s[i+1:]
            return None
        return None

def key_val_parser(label):
    return Regex(label + r"\s*=\s*")\
    .then2(StringParser())

class AttributeParser(Parser):
    def match(self, s):
        if s.startswith('[') and s.endswith(']'):
            s = s[1:-1]
            return s, ""
        return None


re_identifier = re.compile("['\\w]+")

ident_parser = Regex(re_identifier)

attr_parser = AttributeParser()


def split_first(sep, s):
    i = s.find(sep)
    if i > 0:
        return s[:i], s[i:].lstrip(sep)
    return None


def exact(match):
    if match is None:
        return None
    x, s = match
    if s.strip() == "":
        return x
    return None


def to_node(x):
    id, (initial, vars_asmt, loc_labels, loc_asmt, zones, num_opt) = x
    return Node(id, initial, vars_asmt, loc_labels, loc_asmt, zones, num_opt)


def to_edge(x):
    ((l, arrow), r), attr = x
    return Edge(l, r, attr)


def convert_eq(s):
    a, b = split_first('=', s)
    return a, b


int_parser = IntParser()

double_constraint_re = re.compile(r"(-?[0-9]+)(\<=?)([\w\-]+)(\<=?)(-?[0-9]+)")
eq_add_constraint_re = re.compile(r"(\w+)=(\w+)(-|\+)([0-9]+)")
eq_constraint_re = re.compile(r"(\w+)=(-?[0-9]+)")
var_re = re.compile(r"[\w0-9_]+")

eq_add_constraint_re_imi = re.compile(r"(\w+)(\+)([0-9]+)=(\w+)$")
eq_constraint_re_imi = re.compile(r"(\w+)=(\-?[0-9]+)$")

cmp_re = re.compile(r"([\w0-9\+\-]+)(<=|<|==|=|>=|>)([\w0-9\+\-]+)")


def convert_constraint(is_imi, s):
    if not is_imi:
        return convert_constraint_tchecker(s)
    else:
        raise NotImplementedError("imitator not supported")


def convert_constraint_tchecker(s):
    def read_num(s):
        return exact(int_parser.match(s))

    def read_add(s):
        r = split_first('+', s)
        if r:
            a, b = r
            a = a.strip()
            b = b.strip()
            c = read_num(a)
            v = b
            if c == None:
                c = read_num(b)
                if c == None:
                    return None
                v = a
            return v, c
        return None

    def read_diff(s):
        match = split_first('-', s)
        if match == None:
           return None
        else:
            l, r = match
        if l == "" or r == "":
            return None
        return l, r

    s_orig = s

    def read_comp(s):
        match = cmp_re.match(s)
        if match == None:
            raise ValueError("Failed to read constraint: {}".format(s_orig))
        return match.groups()

    def ensure_var(v):
        if not isinstance(v, str) or not var_re.match(v):
            raise ValueError("Failed to read constraint: {}".format(s_orig))

    def ensure_int(v):
        if not isinstance(v, int):
            raise ValueError("Failed to read constraint: {}".format(s_orig))

    def is_int(v):
        i = read_num(v)
        if i is not None:
            return True
        else:
            return False

    # Convert constraint of the form
    # a + x `cmp` b to a list of DBM pairs
    def constraints(cmp, a, b, x):
        if a != 0 and a != "0":
            ensure_var(a)
        if b != 0 and b != "0":
            ensure_var(b)
        ensure_int(x)
        if cmp == ">=":
            return [(True, b, a, x)]
        elif cmp == ">":
            return [(False, b, a, x)]
        elif cmp == "=" or cmp == "==":
            return [(True, a, b, -x), (True, b, a, x)]
        elif cmp == "<=":
            return [(True, a, b, -x)]
        elif cmp == "<":
            return [(False, a, b, -x)]
        raise ValueError("Invalid comparison operator: {}".format(cmp))


    def convert_lcr(l, cmp, r):
        # all cases of l and r
        # a + b cmp c + d (invalid)
        # a - b cmp c - d (invalid)
        # a + b cmp c - d (invalid)
        # a - b cmp c + d (invalid)
        # x cmp y + c
        # x cmp y - c
        # x + c cmp y
        # x - c cmp y
        # x cmp y
        ld = read_diff(l)
        rd = read_diff(r)

        la = read_add(l) 
        ra = read_add(r)

        if ld is not None:
            a, x = ld
            if is_int(x): # a - x cmp r
                return constraints(cmp, a, r, -int(x))
            else: # a - x cmp r <--> a - r cmp x
                return constraints(cmp, a, x, -int(r))
        if rd is not None:
            b, y = rd
            if is_int(l): # l cmp b - y <--> y + l cmp b
                return constraints(cmp, y, b, int(l))
            else: # l cmp b - y <--> l + y cmp b
                return constraints(cmp, l, b, int(y))
        
        if la is not None: 
            a, x = la # a + x cmp r
            return constraints(cmp, a, r, int(x))
        if ra is not None: 
            b, y = ra # l cmp b + y <--> l - y comp b
            return constraints(cmp, l, b, -int(y))
        
        if is_int(l): # l cmp r <--> 0 + l cmp r
            return constraints(cmp, 0, r, int(l))
        elif is_int(r): # l cmp r <--> l - r cmp 0
            return constraints(cmp, l, 0, -int(r))
        else: # l cmp r <--> l + 0 cmp r
            return constraints(cmp, l, r, 0)

    s = s.replace(' ', '')
    if s == "True" or s == "true":
        return []

    match = double_constraint_re.match(s)
    if match:
        c1, cmp1, diff, cmp2, c2 = match.groups()
        return [convert_lcr(c1, cmp1, diff), convert_lcr(diff, cmp2, c2)]

    l, cmp, r = read_comp(s)
    return [convert_lcr(l, cmp, r)]
        


# TChecker certificates
locs_parser = Lift(Alt(Parens('<', '>'), Parens(
    '[', ']')), ListParser(',', ident_parser))
vars_regex = re.compile(r"[\w\-]+=[\w\-]+")
vars_parser = ListParser(',', Regex(vars_regex)).apply(
    lambda xs: list(map(convert_eq, xs)))
constraint_regex = re.compile(r"[\w=\<\-\+]+")
constraints_parser = Lift(Parens('(', ')'), ListParser('&&', Regex(constraint_regex))).apply(
    lambda ys: [x for xs in ys for xs1 in convert_constraint(False, xs) for x in xs1])
id_parser = String("#").then(int_parser).apply(lambda p: p[1])

# new
loc_label_parser = ListParser(',', ident_parser)

initial_parser = Optional(key_val_parser("initial"))
var_asmt_parser = key_val_parser("intval").lift(vars_parser)
loc_asmt_parser = key_val_parser("vloc").lift(locs_parser)
zone_parser = key_val_parser("zone").lift(constraints_parser)
loc_labels_parser = key_val_parser("labels").lift(loc_label_parser)


comma_parser = Regex(re.compile(r'[\s]*[,][\s]*'))


class InfoParser(Parser):
    init_parser = Optional(initial_parser.then1(comma_parser))\
        .apply(lambda x: True if x == "true" else False)

    inner_parser = init_parser\
        .then(var_asmt_parser)\
        .then1(comma_parser)\
        .then(loc_labels_parser)\
        .then1(comma_parser)\
        .then(loc_asmt_parser)\
        .then1(comma_parser)\
        .then(zone_parser)
    
    parser = Parens('[', ']')\
        .lift(inner_parser)\
        .flatten()

    def match(self, s):
        match = self.parser.match(s)
        if match is None:
            return None

        initial, vars_asmt, loc_labels, loc_asmt, zones = match[0]
        return (initial, vars_asmt, loc_labels, loc_asmt, zones, None), ""

        # todo: num_opt for scc number in buechi automata traces (not needed for now)
# end new

class StateParser(Parser):
    parser = Optional(id_parser)\
        .then(locs_parser)\
        .then(Optional(vars_parser))\
        .then(constraints_parser)\
        .then(Optional(int_parser))\
        .flatten()

    def match(self, s):
        match = self.parser.match(s)
        if match is None:
            return None

        id_opt, locs, vars_opt, constraints, num_opt = match[0]
        vars = [] if vars_opt == None else vars_opt
        return (locs, vars, constraints, num_opt), ""


node_parser = ident_parser.then(InfoParser()).apply(to_node)

arrow_parser = String("->")

edge_parser = ident_parser\
    .then(arrow_parser)\
    .then(ident_parser)\
    .then(attr_parser)\
    .apply(to_edge)

line_parser = Alt(node_parser, edge_parser)


# # Imitator Certificates
# val_regex = '\\w+\\s*=\\s*-?\\d+'
# loc_regex = '\\w+:\\s*\\w+'
# val_split_re = r'\s*=\s*'
# loc_split_re = r':\s*'


# def read_val(s):
#     var, i = val_split_re.split(s)
#     return "val", var, int(i)


# def read_loc(s):
#     proc, loc = loc_split_re.split(s)
#     return "loc", proc, loc


# def make_loc_val_vectors(tokens):
#     vals = [(a, b) for x, a, b in tokens if x == "val"]
#     locs = [b for x, a, b in tokens if x == "loc"]
#     val_spec = [a for x, a, b in tokens if x == "val"]
#     loc_spec = [a for x, a, b in tokens if x == "loc"]
#     return (locs, vals), (loc_spec, val_spec)


# val_parser = Regex(val_regex).apply(read_val)
# loc_parser = Regex(loc_regex).apply(read_loc)
# discrete_parser_imi = ListParser(
#     ', ', Alt(val_parser, loc_parser)).apply(make_loc_val_vectors)


# def convert_constraints_imi(ys):
#     return [x for s in ys for x in convert_constraint(True, s)]


# constraint_regex_imi = Regex("[\\w=<\\-\\+ >]+")
# constraints_parser_imi = Regex(
#     '&\\s*').then2(ListParser('&', constraint_regex_imi).apply(convert_constraints_imi))


# class SCC_Parser(Parser):
#     scc_regex = r'(SCC=)(\d+)'

#     def match(self, s):
#         match = self.scc_regex.match(s)
#         if match == None:
#             return None
#         _, x = match.groups()
#         l, r = match.span()
#         return int(x), s[r:].lstrip()


# state_parser_imi = SCC_Parser()\
#     .then(discrete_parser_imi.apply(lambda p: p[0]))\
#     .then1(Regex("\\s*==>\\s*"))\
#     .then(constraints_parser_imi)

# node_label_parser_imi = attr_parser.lift(
#     LabelParser("label").lift(state_parser_imi))


# def to_node_imi(x):
#     id, ((scc_num, (locs, vars)), constraints) = x
#     label = locs, vars, constraints, scc_num
#     return Node(id, label)


# node_parser_imi = ident_parser\
#     .then(node_label_parser_imi)\
#     .apply(to_node_imi)

# line_parser_imi = Alt(edge_parser, node_parser_imi)

# init_state_style_re = re.compile(r"\w+ \[shape=diamond\]")
# accepting_state_style_re = re.compile(r"\w+ \[peripheries=2\]")

# Interface functions


def read_line(line, is_imitator=False):
    if line.startswith('node'):
        return None

    line = line.rstrip(';')
    if is_imitator:
        if init_state_style_re.match(line) or accepting_state_style_re.match(line):
            return None
        match = line_parser_imi.match(line)
    else:
        match = line_parser.match(line)
    x = exact(match)
    if x is None:
        raise ValueError("Failed to read line: '{}'".format(line))

    return x


def read_string(string, is_imitator=False):
    start_re = "digraph \\S+ \\{\\s*"
    end_re = "\\s*\\}\\s*"
    lines = [line for line in string.split(';') if line.strip()]
    if len(lines) == 1:
        lines = [line for line in string.split('\n') if line.strip()]
    if re.match(start_re, lines[0]) is None:
        raise ValueError("Invalid start of dot file: '{}'".format(lines[0]))
    if re.match(end_re, lines[-1]) is None:
        raise ValueError("Invalid end of dot file: '{}'".format(lines[-1]))
    elements = []
    for line in lines[1:-1]:
        result = read_line(line.strip(), is_imitator)
        if not result is None:
            elements.append(result)
    return elements


if __name__ == "__main__":

    print("=" * 100)
    print("Running test cases for Tchecker .dot file reader!")
    print("=" * 100)

    test = "(x1==808)"
    parser = constraints_parser
    print(parser.match(test))
    test = "(x1<=808 && x1==y && 808=x1)"
    print(parser.match(test))
#     print(convert_constraints_imi(["x1>=808"]))

#     test = """& T >= 0
# & xA2 > 60 + T
# & T + 350 > xA2
# & 20 >= T
# & xA2 = 20 + trt3
# & xB2 = T
# & xB3 = 390 + T
# & trt2 = T
# & xB1 = 20 + T
# & xA1 = 370 + T
# & trt1 = 20 + T
# & xA2 = 20 + xA3"""

#     parser = constraints_parser_imi
#     print(parser.match(test))

#     test = "sender: next_frame, receiver: new_file, channelK: startK, channelL: startL, i = 1, rc = 2, b1 = 1, bN = 1, rb1 = 1, rbN = 0, ab = 0, rab = 0, exp_ab = 1"

#     print(constraint_regex_imi.match(' u >= 0'))

#     print(discrete_parser_imi.match(test))

#     test = """& v >= 23
#  & u >= 0
#  & 2 >= u
#  & u + 27 >= v
#  & x = u
#  & z = 0"""

#     print(constraints_parser_imi.match(test))

#     test = """SCC=475
#  sender: wait_ack, receiver: frame_received, channelK: startK, channelL: startL, i = 1, rc = 1, b1 = 1, bN = 0, rb1 = 1, rbN = 0, ab = 0, rab = 0, exp_ab = 0 ==>
#  & v >= 23
#  & u >= 0
#  & 2 >= u
#  & u + 27 >= v
#  & x = u
#  & z = 0"""

#     print(state_parser_imi.match(test))

#     test = """s_318 [label="SCC=475
#  sender: wait_ack, receiver: new_file, channelK: in_transitK, channelL: startL, i = 1, rc = 0, b1 = 1, bN = 0, rb1 = 0, rbN = 1, ab = 0, rab = 1, exp_ab = 0 ==>
#  & u >= 0
#  & z >= 8 + v
#  & v + 12 >= z
#  & 2 >= u
#  & v >= 45 + u
#  & x = u"]"""

#     print(line_parser_imi.match(test))

    p = zone_parser
    print(p.match('zone="(P1_x=P2_x && 6<P1_x && 4<P2_x && 2<P3_x && 6<P4_x && 2<P1_x-P2_x && 4<P1_x-P3_x && 0<=P1_x-P4_x && 2<P2_x-P3_x && P2_x-P4_x<-2 && P3_x-P4_x<-4)"'))

    zone_test1 = 'zone="(0<=start__light_match_match0_ && 0<=start__mend_fuse_fuse0_match0_ && 0<=start__mend_fuse_fuse1_match0_ && 0<=end__light_match_match0_ && 0<=end__mend_fuse_fuse0_match0_ && 0<=end__mend_fuse_fuse1_match0_ && 0<=start__mend_fuse_fuse0_match0_-end__light_match_match0_)"'
    print(p.match(zone_test1))

    p = initial_parser
    print(p.match('initial="true"'))

    print(p.match('initial="false"'))

    p = vars_parser
    test = "abc12-3=3"
    print(p.match(test))

    p = var_asmt_parser
    test = 'intval="acts_active=0,planning_lock=0,lock_handfree=0,lock_unused_match0=0,lock_light_match0=0,var_handfree=0,var_unused_match0=0,var_light_match0=0,var_mended_fuse0=0,var_mended_fuse1=0"'
    print(p.match(test))

    p = constraints_parser
    constraints_test = '(0<=start__light_match_match0_ && 0<=start__mend_fuse_fuse0_match0_ && 0<=start__mend_fuse_fuse1_match0_ && 0<=end__light_match_match0_ && 0<=end__mend_fuse_fuse0_match0_ && 0<=end__mend_fuse_fuse1_match0_)'
    print(p.match(constraints_test))

    p = zone_parser
    zone_test1 = 'zone="(0<=start__light_match_match0_ && 0<=start__mend_fuse_fuse0_match0_ && 0<=start__mend_fuse_fuse1_match0_ && 0<=end__light_match_match0_ && 0<=end__mend_fuse_fuse0_match0_ && 0<=end__mend_fuse_fuse1_match0_ && 0<=start__mend_fuse_fuse0_match0_-end__light_match_match0_)"'
    print(p.match(zone_test1))


    p = loc_labels_parser
    loc_labels_test = 'labels="init,off"'
    print(p.match(loc_labels_test))

    p = loc_asmt_parser
    loc_asmt_test = 'vloc="<l0,l1,l2,l3>"'
    print(p.match(loc_asmt_test))

    p = InfoParser()
    loc_info_test = '[initial="true", intval="acts_active=0,planning_lock=0,lock_handfree=0,lock_unused_match0=0,lock_light_match0=0,var_handfree=0,var_unused_match0=0,var_light_match0=0,var_mended_fuse0=0,var_mended_fuse1=0", labels="init,off", vloc="<l0,l0,l0,l0>", zone="(0<=start__light_match_match0_ && 0<=start__mend_fuse_fuse0_match0_ && 0<=start__mend_fuse_fuse1_match0_ && 0<=end__light_match_match0_ && 0<=end__mend_fuse_fuse0_match0_ && 0<=end__mend_fuse_fuse1_match0_)"]'
    print(p.match(loc_info_test))

    test = '0 [initial="true", intval="acts_active=0,planning_lock=0,lock_handfree=0,lock_unused_match0=0,lock_light_match0=0,var_handfree=0,var_unused_match0=0,var_light_match0=0,var_mended_fuse0=0,var_mended_fuse1=0", labels="init,off", vloc="<l0,l0,l0,l0>", zone="(0<=start__light_match_match0_ && 0<=start__mend_fuse_fuse0_match0_ && 0<=start__mend_fuse_fuse1_match0_ && 0<=end__light_match_match0_ && 0<=end__mend_fuse_fuse0_match0_ && 0<=end__mend_fuse_fuse1_match0_)"]'
    print(node_parser.match(test))

    print(read_line(test))

    test2 = "n11 -> n107 [color=blue]"
    print(read_line(test2))

    test_file = "tck_examples/MatchCellar-impossible/instance_1.dot"
    with open(test_file, 'r') as f:
        r = read_string(f.read())
        print(len(r))

    # print(convert_constraint("RING_x=0"))
    # print(convert_constraint("ST2_y=ST2_z+100"))
    # state = "<l2,l3,l0>  (ST2_y=ST2_z+100)"
    # print(StateParser().match(state))
    # state = "<l2,l3,l0>  (RING_x=0 & ST1_x=20 & ST1_y=20 & ST1_z=120 & ST2_x=40 & ST2_y=140 & ST2_z=40 & RING_x=ST1_x-20 & RING_x=ST1_y-20 & RING_x=ST1_z-120 & RING_x=ST2_x-40 & RING_x=ST2_y-140 & RING_x=ST2_z-40 & ST1_x=ST1_y & ST1_x=ST1_z-100 & ST1_x=ST2_x-20 & ST1_x=ST2_y-120 & ST1_x=ST2_z-20 & ST1_y=ST1_z-100 & ST1_y=ST2_x-20 & ST1_y=ST2_y-120 & ST1_y=ST2_z-20 & ST1_z=ST2_x+80 & ST1_z=ST2_y-20 & ST1_z=ST2_z+80 & ST2_x=ST2_y-100 & ST2_x=ST2_z & ST2_y=ST2_z+100)"
    # print(StateParser().match(state))
