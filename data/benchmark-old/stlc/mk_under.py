import re
import sys
import json

def to_lib(source):
    mid = 3
    str_let = source[0:mid]
    rest = source[mid:]
    return str_let + "[@library]" + rest

def load_lib(name):
    with open("{}/rty.ml".format(name), 'r') as f:
        return f.read()

def write_under(name):
    j_fname = "{}/gen.json".format(name)
    under_fname = "{}/_under.ml".format(name)
    with open (j_fname, "r") as f:
        j = json.load(f)
    header = "external method_predicates : t = {}\n".format(' '.join([ "\"{}\"".format(mp) for mp in j['mps']]))
    libs = "\n".join([ to_lib(load_lib(lib)) for lib in j['libs']])
    with open(under_fname, 'w') as f:
        f.write("{}\n{}\n{}".format(header, libs, load_lib(name)))
    return

meta_config_file = "../../../meta-config.json"
benchmark_table_file = "../../../config/benchmark.json"

def init ():
    with open (benchmark_table_file) as f:
        benchmark_table = json.load(f)
    return benchmark_table

sys.path.insert(1, '../../../scripts')
import iter_benchs

if __name__ == '__main__':
    tab = init ()
    for name in iter_benchs.stlc_names:
        for info in tab['benchmarks_info']:
            for entry in info['benchmarks']:
                if entry["name"] == name:
                    path = entry["path"]
                    break
        write_under(path)
