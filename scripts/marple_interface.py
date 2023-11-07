import sys
import argparse
import os
import os.path
import subprocess
import colored

cmd_prefix = ["dune", "exec", "--", "bin/main.exe"]

workdir = ""

meta_config_file = "meta-config.json"

def invoc_cmd(verbose, cmd, output_file, cwd=None):
    if output_file is not None:
        # print("{}:{}".format(output_file, type(output_file)))
        if (verbose):
            print(" ".join(cmd + [">>", output_file]))
        with open(output_file, "a+") as ofile:
            try:
                subprocess.run(cmd, cwd=cwd, stdout=ofile)
            except subprocess.CalledProcessError as e:
                print(e.output)
    else:
        if (verbose):
            print(" ".join(cmd))
        try:
            subprocess.run(cmd, cwd=cwd)
        except subprocess.CalledProcessError as e:
            print(e.output)

def ri_type_check(filename, verbose):
    path = filename.split('/')
    method_str = path[-1]
    dir_str = "/".join(path[0::-1])
    if (verbose):
        print (colored.purple_text("Running Marple on " + filename))
    cmd = cmd_prefix + ["ri-type-check", meta_config_file, dir_str, method_str]
    invoc_cmd(verbose, cmd, None)

def ri_ntype_check(filename, verbose):
    path = filename.split('/')
    method_str = path[-1]
    dir_str = "/".join(path[0:-1])
    if (verbose):
        print (colored.purple_text("Running Basic Type Check on " + filename))
    cmd = cmd_prefix + ["ri-ntype-check", meta_config_file, dir_str, method_str]
    invoc_cmd(verbose, cmd, None)

def print_raw(filename, verbose):
    print (colored.purple_text("Print (without desugar) " + filename))
    cmd = cmd_prefix + ["print-raw", meta_config_file, filename]
    invoc_cmd(verbose, cmd, None)

def print_raw_rty_to_srl(filename, verbose):
    print (colored.purple_text("Print (without desugar) " + filename))
    cmd = cmd_prefix + ["print-raw-rty-to-srl", meta_config_file, filename]
    invoc_cmd(verbose, cmd, None)

def print_raw_rty_without_pred(filename, verbose):
    print (colored.purple_text("Print (without desugar) " + filename))
    cmd = cmd_prefix + ["print-raw-rty-without-pred", meta_config_file, filename]
    invoc_cmd(verbose, cmd, None)

if __name__ == '__main__':
    try:
        if sys.argv[2] == "verbose":
            verbose = True
    except:
        verbose = False
    print_raw(sys.argv[1], verbose)
