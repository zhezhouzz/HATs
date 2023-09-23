import sys
import argparse
import os
import os.path
import subprocess

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

def run(dir_str, verbose):
    filename = "{}/{}".format(dir_str, "prog.ml")
    if (verbose):
        print (colored.bold_text("Running Poirot on "+filename))
    cmd = cmd_prefix + ["coverage-type-check", meta_config_file,
                        # "{}/{}".format(dir_str, "config.json"),
                        filename,
                        "{}/{}".format(dir_str, "_under.ml")]
    invoc_cmd(verbose, cmd, None)

def show_refine(dir_str, verbose):
    cmd = cmd_prefix + ["print-coverage-types", meta_config_file,
                        "{}/{}".format(dir_str, "_under.ml")]
    invoc_cmd(verbose, cmd, None)

def show_source(dir_str, fm, verbose):
    cmd = cmd_prefix + ["print-source-code", fm, meta_config_file,
                        "{}/{}".format(dir_str, "prog.ml"),
                        "{}/{}".format(dir_str, "_under.ml")]
    invoc_cmd(verbose, cmd, None)

def split_source(dir_str, verbose):
    cmd = cmd_prefix + ["split-source-code",
                        "{}/{}".format(dir_str, "prog.ml")]
    invoc_cmd(verbose, cmd, None)

def reset_source(dir_str, verbose):
    cmd = ["cp", "{}/_under.ml".format(dir_str), ".tmp._under.ml"]
    invoc_cmd(verbose, cmd, None)
    cmd = ["rm", "-rf", dir_str]
    invoc_cmd(verbose, cmd, None)
    cmd = ["mkdir", dir_str]
    invoc_cmd(verbose, cmd, None)
    cmd = ["cp", ".tmp._under.ml", "{}/_under.ml".format(dir_str)]
    invoc_cmd(verbose, cmd, None)

def cp_source(from_file, dir_str, verbose):
    cmd = ["cp", from_file, "{}/{}".format(dir_str, "prog.ml")]
    invoc_cmd(verbose, cmd, None)

def run_cobalt(cobalt_dir, cmd, cobalt_input, verbose):
    cmd = ["./effsynth.native"] + cmd + [cobalt_input]
    invoc_cmd(verbose, cmd, ".log", cwd=cobalt_dir)

def test_parsing(dir_str, verbose):
    cmd = cmd_prefix + ["print-source-code", meta_config_file,
                        "{}/{}".format(dir_str, "prog.ml")]
    invoc_cmd(verbose, cmd, None)
    # rtyfile = "{}/{}".format(dir_str, "_under.ml")
    # if os.path.isfile(rtyfile):
    #     cmd = cmd_prefix + ["print-source-code", meta_config_file, rtyfile]
    #     invoc_cmd(verbose, cmd, None)

def test_ntypecheck(dir_str, verbose):
    cmd = cmd_prefix + ["print-source-code", meta_config_file,
                        "{}/{}".format(dir_str, "prog.ml")]
    invoc_cmd(verbose, cmd, None)

def typecheck(dir_str, verbose):
    cmd = cmd_prefix + ["type-check", meta_config_file,
                        "{}/{}".format(dir_str, "prog.ml")]
    invoc_cmd(verbose, cmd, None)

if __name__ == '__main__':
    try:
        if sys.argv[2] == "verbose":
            verbose = True
    except:
        verbose = False
    run(sys.argv[1], verbose)
