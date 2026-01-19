import json
import sys
import re
from .read_dot import read_string, Node, Edge
from itertools import chain
from .scc import strongly_connected_components_path
import argparse


def invert(mapping):
    inverted = dict()
    for k, v in mapping.items():
        if v in inverted:
            raise ValueError("Mapping is not injective!")
        inverted[v] = k
    return inverted


class VerboseKeyError(KeyError):
    def __init__(self, name, args):
        self.args = args
        self.name = name

    def __str__(self):
        return "KeyError: key {} in {}".format(self.args, self.name)

    def __repr__(self):
        return "VerboseKeyError({},{})".format(self.name, self.args)


def make_verbose_map(name, d):
    def do(key):
        if key in d:
            return d[key]
        else:
            raise VerboseKeyError(name, key)
    return do


def convert(certificate, renaming, is_buechi=False, compute_nums=False, reverse_nums=False, ignore_vars=False, loc_to_id=None):
    def loc_to_id_default(i, loc):
        return loc[1:]
    loc_to_id = loc_to_id_default if loc_to_id == None else loc_to_id

    process_id_to_name = invert(renaming['processes'])
    process_location_id = renaming['locations']
    var_id = renaming['vars']
    # The zero clock is expected to be included in the renaming
    clocks_id = renaming['clocks']
    num_clocks = len(clocks_id)
    num_vars = len(var_id)
    num_processes = len(process_id_to_name)

    process_id_to_name = make_verbose_map(
        "Process id to name", process_id_to_name)
    process_location_id = make_verbose_map(
        "Process & location id to id", process_location_id)

    def strip_l(loc):
        return loc.lstrip("l")

    def convert_locs(locs): # Should work
        return tuple(int(strip_l(l)) for i, l in enumerate(locs))

    def convert_dbm(constraints):
        d = {}
        for i in range(num_clocks):
            for j in range(num_clocks):
                d[(i, j)] = None
        for is_le, x, y, c in constraints:
            i = clocks_id[x] if x != 0 else 0
            j = clocks_id[y] if y != 0 else 0
            d[(i, j)] = (is_le, c)
        for j in range(num_clocks):
            if d[(0, j)] is None:
                d[(0, j)] = (True, 0)
            if d[(j, j)] is None:
                d[(j, j)] = (True, 0)
        return [d[(i, j)] for i in range(num_clocks) for j in range(num_clocks)]

    def convert_vars(vars):
        if ignore_vars:
            vars = ((x, v) for x, v in vars if not x.startswith("cmtd_"))
        vars = sorted(vars, key=lambda x: var_id[x[0]])
        return tuple(int(x[1]) for x in vars)

    def convert_node(node):
        locs, vars, constraints, num_opt = node.loc_asmt, node.vars_asmt, node.zones, node.num_opt
        vars = convert_vars(vars)
        return convert_locs(locs), vars, convert_dbm(constraints), num_opt

    result = {}
    vertices = []
    edges = {}
    scc_nums = {}
    for element in certificate:
        if isinstance(element, Node):
            locs, vars, dbm, num_opt = convert_node(element)
            
            if is_buechi:
                vertices.append(element.id)
                edges[element.id] = []
                # Remember the node id to assign the SCC number later.
                dbm = (dbm, element.id)
                scc_nums[element.id] = num_opt
                if num_opt == None and not compute_nums:
                    raise ValueError(
                        "Missing SCC number for: <{}, {}, {}>".format(locs, vars, dbm))

            if not (locs, vars) in result:
                result[(locs, vars)] = []
            result[(locs, vars)].append(dbm)
        elif is_buechi and isinstance(element, Edge):
            node_id = element.source
            edges[node_id].append(element.sink)

    if compute_nums and is_buechi:
        # Increase maximum call stack depth for SCC computation
        sys.setrecursionlimit(10000)
        components = list(strongly_connected_components_path(vertices, edges))
        # Reset maximum call stack depth to default
        sys.setrecursionlimit(1000)

        n = len(components)
        scc_nums = {}
        for i, component in enumerate(components):
            scc_num = n - i
            for node in component:
                scc_nums[node] = scc_num
    elif reverse_nums and is_buechi:
        max_num = max(scc_nums.values())
        for k, v in scc_nums.items():
            scc_nums[k] = max_num - v

    if is_buechi:
        for k, dbms in result.items():
            result[k] = [(dbm, scc_nums[node]) for dbm, node in dbms]

    num_discrete_states = len(result.keys())
    num_dbms = sum((len(xs) for xs in result.values()))
    num_edges = sum((len(xs) for xs in edges.values()))

    return (num_discrete_states, num_dbms, num_edges), (num_processes, num_vars, num_clocks, result)


def int_to_bytes(x):
    return x.to_bytes(8, 'big', signed=True)


def int_list_to_bytes(x):
    return b''.join(map(int_to_bytes, x))


def constraint_to_bytes(x):
    is_le, c = x
    b = c
    b <<= 1
    if is_le:
        b |= 1
    return int_to_bytes(b)


inf_bytes = b'\x7f\xff\xff\xff\xff\xff\xff\xff'


def dbm_to_bytes(dbm):
    return b''.join(map(lambda x: inf_bytes if x is None else constraint_to_bytes(x), dbm))


def dbm_int_to_bytes(x):
    dbm, i = x
    return b''.join([dbm_to_bytes(dbm), int_to_bytes(i)])


def state_union_to_bytes(x, is_buechi=False):
    (locs, vars), dbms = x
    zone_to_bytes = dbm_int_to_bytes if is_buechi else dbm_to_bytes
    return b''.join(chain(
        [int_list_to_bytes(locs),
         int_list_to_bytes(vars),
         int_to_bytes(len(dbms))],
        map(zone_to_bytes, dbms)))


def certificate_to_bytes(x, is_buechi=False):
    header = [int_to_bytes(43 if is_buechi else 42)]
    num_processes, num_vars, num_clocks, result = x
    lengths = map(int_to_bytes,
                  [num_processes,
                   num_clocks,
                   num_vars,
                   len(result)])
    states = map(lambda x: state_union_to_bytes(x, is_buechi), result.items())
    return b''.join(chain(header, lengths, states))


def model_to_loc_renaming(model):
    def process_to_renaming(process):
        result = {}
        for node in process['nodes']:
            name = node['name']
            if name in result:
                raise ValueError("Model has duplicate location names!")
            result[name] = str(node['id'])
        return result

    result = list(map(process_to_renaming, model['automata']))

    def loc_to_id(i, l):
        return result[i][l]

    return loc_to_id


def convert_from_renaming_file(certificate, renaming_file, is_buechi, compute_nums, is_imitator, ignore_vars, model_file=None):
    with open(renaming_file) as renaming_file:
        certificate = read_string(certificate, is_imitator)
        renaming = json.load(renaming_file)
        loc_to_id = None
        if model_file:
            with open(model_file) as model_file:
                model = json.load(model_file)
                loc_to_id = model_to_loc_renaming(model)

        nums, result = convert(certificate, renaming, is_buechi, compute_nums, is_imitator,
                               ignore_vars, loc_to_id)
        
        binary = certificate_to_bytes(result, is_buechi)
        return nums, binary


def convert_from_files(certificate_file, renaming_file, is_buechi=False, compute_nums=False, is_imitator=False, ignore_vars=False, model_file=None):
    with open(certificate_file) as certificate_file:
        certificate = certificate_file.read()
        return convert_from_renaming_file(certificate, renaming_file, is_buechi, compute_nums, is_imitator, ignore_vars, model_file)


parser = argparse.ArgumentParser(
    description="Convert a certificate given in TChecker's .dot format to Munta's binary format.")
parser.add_argument("cert", type=str, help="The input certificate")
parser.add_argument("renaming", type=str,
                    help="A renaming file for the original model")
parser.add_argument("out", type=str, help="The output file")
parser.add_argument("-m", "--model", type=str,
                    help="The original model file to be used for renaming")
parser.add_argument(
    "-b", "--buechi", action='store_true', help="Specifies that a Büchi certificate should be output")
parser.add_argument(
    "-imi", "--imitator", action='store_true', help="Specifies that the certificate was produced by imitator")
parser.add_argument("--ignore-vars", action='store_true',
                    help="Ignore all variables")
parser.add_argument("--compute-nums", action='store_true',
                    help="Re-calculate SCC numbers from edges")

if __name__ == "__main__":
    args = parser.parse_args()
    model_file = args.model
    certificate_file = args.cert
    renaming_file = args.renaming
    output_file = args.out
    is_buechi = args.buechi
    is_imitator = args.imitator
    ignore_vars = args.ignore_vars
    compute_nums = args.compute_nums
    _, binary = convert_from_files(
        certificate_file, renaming_file, is_buechi, compute_nums, is_imitator, ignore_vars, model_file)
    with open(output_file, 'wb') as output_file:
        output_file.write(binary)
