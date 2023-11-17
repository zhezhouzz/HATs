# Supplementary Material: Hoare Automata Type

This is the supplementary material for the PLDI 2024 submission *A HAT Trick: Automatically Verifying Representation Invariants Using Symbolic Finite Automata*. This supplementary material consists of both the OCaml implementation (**Marple**) and the Coq formalization of the type system of our core language **λ<sup>E</sup>** introduced in the paper.

A docker image of this repo with all required dependecies is available on: `https://hub.docker.com/r/marple24/marple`.

### Supplementary Material Structure

This section gives a brief overview of the files in this supplementary material.

* `bin/main.ml`: the main entry point of **Marple**.
* `coersion` and `normalization/`: the normalization procedure that normalizes the code into the Monadic Normal Form (a variant of the A-Normal form).
* `data/`: the predefined types and the benchmark input files.
  + `data/predefined/`: the predefined types.
  + `data/ri/ADT_LIBRARY/METHOD.ml`: the benchmark input files. For each `ADT` that is implemented by different underline library `LIBRARY`, There is a folder under path `data/ri/`. Besides `METHOD.ml` that are methods of given `ADT` implementation, these folder also provide the basic and refinement types for underline library (`lib_nty.ml` and `lib_rty.ml`), automata predicates (`automata_preds.ml`) and represention invaraint `ri.ml`.
* `desymbolic/`: minterm transfermation that convert SFA into FA.
* `dtree/`: the decision tree data structure used in instantiation and minterm generation.
* `env/`: the universal environment of **Marple** which is loaded from the configuration files.
* `formalization/`: the Coq proofs of our core language **λ<sup>E</sup>**.
* `frontend/`: the **Marple** parser, a modified OCaml parser.
* `syntax/` and `language/`: the AST of the languages used in **Marple**.
* `meta-config.json`: the main configuration file, the details can be found in [Configuration of Marple](#configuration-of-marple).
* `ntypecheck/`: basic type inference and check.
* `scripts/`: various Python scripts for collecting and displaying experimental results.
* `smtquery/`: the Z3 (SMT solver) wrapper.
* `subtyping/`: refinement subtype check.
* `typecheck/`: refinement type check.

### Representation Invaraints in Benchmarks

We provides the meaning of representation invaraints of each ADT in our benchmarks, they are encoded as different SFA acorroding to the underline libraries.

* `ConnectedGraph`: all nodes are connect by at least one node (allowing self-loop).
* `DFA`: for a node and a character, there is at most one transition.
* `FileSystem`: Any path that is stored as a key in the key-value
  store (other than the root path) must also have its parent stored as a
  non-deleted directory in the store.
* `Heap`: the top element of a heap is the minimal one.
* `LazySet`: there is no duplicate element insertion.
* `MinSet`: the recorded minimal element is the minimal element in the set.
* `Queue`: the queue data structure that supports first-in-first-out (FIFO) order.
* `Set`: the set data structure that contains non-duplicate elements.
* `Stack`: the stack data structure that supports first-in-last-out (FILO) order.

### Running the Docker Image

You may fetch the pre-built Docker image from Docker Hub:

    $ docker pull marple24/marple:pldi-2024

To launch a shell in the Docker image:

    $ docker run -it -m="8g" marple24/marple:pldi-2024

### Running Benchmarks of Marple

In this section, we discuss the scripts that displays the tables in the evaluation section of the paper. The executable of Marple is `_build/default/bin/main.exe`, which can be built the following command:

    $ dune build --profile release

##### Pretty Printing

The following command pretty prints the content of given files, which may contains source code, autoamata predicates, and HATs:

    $ ./_build/default/bin/main.exe print-raw meta-config.json data/ri/FileSystem_KVStore/ri.ml

The script will print the following autoamata predicates:

```
val[@pred] rI: (p : Path.t) = ☐⟨is_root p⟩ ∨ (¬aliveP(p) ∨ dirP(parent p))
```

Another example:

    $ ./_build/default/bin/main.exe print-raw meta-config.json data/ri/FileSystem_KVStore/add.ml

The script will print the following source code and refinement types:

```
let add = fun (path : Path.t) ->
  fun (content : Bytes.t) ->
    (if exists path
     then (false : bool)
     else
       (let (parent_path : Path.t) = getParent path in
        if not (exists parent_path)
        then (false : bool)
        else
          (let (bytes' : Bytes.t) = get parent_path in
           if isDir bytes'
           then
             let (unused!0 : unit) = put path content in
             let (unused!1 : unit) = put parent_path (addChild bytes' path) in
             (true : bool)
           else (false : bool))) : bool)
val[@assertRty] add: (p:Path.t)⇢(path:{v:Path.t | true})→(content:{v:Bytes.t | true})→[rI(p)]{v:bool | true}[rI(p)]
```

##### Basic Type Check

The following command performs the basic type check for a given ADT implementation.

    $ python3 scripts/comprehensive.py silent ntyping-one data/ri/FileSystem_Tree

By enable the `preprocess` option in the config file `meta-config.json`, **Marple** will print the result of preprocess: desguaring, basic type check, and normalization. The details can be found in [Configuration of Marple](#configuration-of-marple).

##### Type check

The following command performs the type check for a given ADT implementation. It will take about `3` min:

    $ python3 scripts/comprehensive.py silent typing-one data/ri/FileSystem_Tree

By enable the `typing` option in the config file `meta-config.json`, **Marple** will print the typing rules used during type check.

##### Comprehensive Scripts

The following scripts run the benchmark suite displayed in Table 1 of the paper.

###### Step 1: Preprocess

The following scripts run the preprocess on all benchmark suite displayed in Table 1 of the paper, and store the result into statfile file (defined in config file `meta-config.json`, the default location is `.stat`).

    $ python3 scripts/comprehensive.py silent ntyping data/ri

Then, the following prints the first part of table 1 (as latex code).

    $ python3 scripts/comprehensive.py n show-table1 data/ri

###### Step 2: Type Check

The following scripts run typecheck on all benchmark suite displayed in Table 1 of the paper, and store the result into statfile file (defined in config file `meta-config.json`, the default location is `.stat`). It will take about `15` mins:

    $ python3 scripts/comprehensive.py silent typing data/ri

Then, the following prints the two parts of table 1 (please first performs preporcess to get the statistics result for the first part of the table).

    $ python3 scripts/comprehensive.py n show-table1 data/ri


##### Detailed Steps

By add commanding the line argument `verbose`, all of the scripts above will show the actual command sent to **Marple** on each benchmark. For example, by running:

    $ python3 scripts/comprehensive.py verbose ntyping-one data/ri/FileSystem_Tree

The script will print the following commands:

```
dune build --profile release
Running Basic Type Check on data/ri/FileSystem_Tree/add.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/add.ml
Running Basic Type Check on data/ri/FileSystem_Tree/add_path_in_dir.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/add_path_in_dir.ml
Running Basic Type Check on data/ri/FileSystem_Tree/del_path_in_dir.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/del_path_in_dir.ml
Running Basic Type Check on data/ri/FileSystem_Tree/delete.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/delete.ml
Running Basic Type Check on data/ri/FileSystem_Tree/deleteChildren.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/deleteChildren.ml
Running Basic Type Check on data/ri/FileSystem_Tree/init.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/init.ml
...
```

Readers can try these commands to execute each step individually.

#### Configuration of Marple

All commands of **Marple** will take a universal configuration file (`meta-config.json`) in JSON format as its first argument. Precisely, the JSON file outputs results in JSON format to some output directory.
- the `debug_tags` field controls the debug information output. Precisely, we have the following options:
  + if the `preprocess` field is true, **Marple** will print the preprocess result. It will print the given source code, type code, and the code in Monadic Normal Form.
  + if the `typing` field is set as true, **Marple** will print the type judgement of each step in the type check.
  + if the `result` field is set as true, **Marple** will print the type check result.
- the `resfile` field indicates the path of the output file of type check.
- the `logfile` field indicates the path of the log file of type check.
- the `statfile` field indicates the path of the statistics file of type check.
- the `uninterops` field indicates the built-in operators and method predicates used in the current benchmarks.
- the `prim_path` field indicates the predefined refinement types for a number of
OCaml primitives, including various arithmetic operators, and data constructors, and axioms of unintepreted functions.

### Coq Formalization

See `formalization/README.md`.
