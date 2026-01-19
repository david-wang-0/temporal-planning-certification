import json
import sys
import pydot


def dot_from_model(model):
    dot = pydot.Dot(graph_type='digraph')
    nodes = {}
    graphs = []
    default_shape = "circle"
    init_shape = "doublecircle"
    for process_num, automaton in enumerate(model['automata']):
        initial = int(automaton['initial'])
        graph = pydot.Cluster(
            graph_name=automaton['name'], label=automaton['name'])
        for node in automaton['nodes']:
            node_id = node['id']
            shape = init_shape if node_id == initial else default_shape
            name = node['name']
            label = name + "\n" + node['invariant']
            name = name + '_' + str(process_num)
            nodes[node_id] = pydot.Node(
                name=name, label=label, shape=shape)
            graph.add_node(nodes[node_id])
        for edge in automaton['edges']:
            source = nodes[edge['source']]
            target = nodes[edge['target']]
            label = "{}\n {}\n {}".format(
                *(edge[attr] for attr in ('label', 'guard', 'update')))
            graph.add_edge(pydot.Edge(src=source, dst=target, label=label))
        dot.add_subgraph(graph)
    return str(dot)


def convert_from_file(input_file):
    with open(input_file) as f:
        d = json.load(f)
        return dot_from_model(d)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: convert.py file_in file_out")
        sys.exit(0)

    s = convert_from_file(sys.argv[1])
    f = sys.argv[2]
    with open(f, 'w') as f:
        f.write(s)
