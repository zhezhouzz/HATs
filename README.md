# Artifact Guide: A HAT Trick: Automatically Verifying Representation Invariants Using Symbolic Finite Automata

This is the accompanying artifact for the PLDI 2024 submission _A HAT Trick: Automatically Verifying Representation Invariants Using Symbolic Finite Automata_. This artifact consists of both the OCaml implementation (**Marple**) and the Coq formalization of the type system of our core language **λ<sup>E</sup>** introduced in the paper.

A docker image of this repo with all required dependecies is available on: `https://hub.docker.com/r/marple24/marple`.

## Getting Started Guide

We recommend machines have at least 8 GB of memory and 8 GB of hard
disk space available when building and running Docker images. All
benchmarks were tested on a Linux machine having Intel i7-8700 CPU @ 3.20GHz with `64GB` of RAM. The estimated execution time in the rest of the document also fits this setting.

### Requirements

This artifact is built as a Docker image. Before proceeding, ensure
Docker is installed. (On *nix, `sudo docker run hello-world` will test
your installation.) If Docker is not installed, install it via the
[official installation guide](https://docs.docker.com/get-docker/). This guide was tested using Docker version `20.10.23`, but any contemporary Docker version is expected to work.

### Using the Pre-Built Docker Image

You may fetch the pre-built Docker image from Docker Hub:

    $ docker pull marple24/marple:pldi-2024

You may also load the docker image from the file `marple:pldi-2024.tar.gz`.

    $ docker load < marple:pldi-2024.tar.gz

### Building the Docker Image (Optional)

Alternately, to build the Docker image yourself, navigate to the
directory containing the Dockerfile and tell Docker to build:

    $ docker build . --tag marple24/marple:pldi-2024

**Resource Requirements:** Although our tool **Marple** and the Coq formalization doesn't have large memory usage, building the docker image needs more than `32GB` RAM available. This memory usage requirement comes from the installation of the SMT solver `z3` (https://github.com/Z3Prover/z3). When the RAM limit of Docker (by default, it is `8GB` on Mac, no limit on Linux machine) is lower than `32GB`, the installation of `z3` will be killed and the `docker build` will fail.
The memory error can be fixed by increasing the RAM limit in Docker; you can find instructions for doing so on Mac here: (https://docs.docker.com/desktop/settings/mac/#resources), for Windows here: (https://docs.docker.com/desktop/settings/windows/#resources), and for Linux here: (https://docs.docker.com/desktop/settings/linux/#resources). The pre-built docker image is built on a Linux machine having Intel i7-8700 CPU @ 3.20GHz with `64GB` of RAM, it took `30` min to build.

### Running the Docker Image

To launch a shell in the Docker image:

    $ docker run -it -m="8g" marple24/marple:pldi-2024

To compile **Marple**:

    $ dune build --profile release && cp _build/default/bin/main.exe main.exe
The compilation result of **Marple** is an executable `_build/default/bin/main.exe`. For the sake of convenience, we copy it under the current directory. You can run **Marple** by executing `main.exe <args>` directly or executing it via `dune`, that is `dune exec -- bin/main.exe <args>`.

You can print **Marple**'s help message to verify the tool operating
successfully:

    $ ./main.exe --help

##### Pretty Printing

As another way to verify the tool operating successfull, the following command pretty prints the content of given files, which may contains source code, automata predicates, and HATs:

    $ ./main.exe print-raw meta-config.json data/ri/FileSystem_KVStore/ri.ml

The script will print the following automata predicates:

```
val[@pred] rI: (p : Path.t) = ☐⟨is_root p⟩ ∨ (¬aliveP(p) ∨ dirP(parent p))
```

Another example:

    $ ./main.exe print-raw meta-config.json data/ri/FileSystem_KVStore/add.ml

The script will print the following source code and refinement types:

```ocaml
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

### Coq proofs in the Docker Image

The Coq proofs of our core language **λ<sup>E</sup>** are located in the `formalization/` directory. To build and check the Coq formalization, simply run `make` in the formalization directory. See `formalization/README.md`.

## Step-by-Step Instructions

In this section, we provide the instructions to evaluate our artifact.

### Artifact Structure

This section gives a brief overview of the files in this artifact.

* `bin/main.ml`: the main entry point of **Marple**.
* `coersion/` and `normalization/`: the normalization procedure that normalizes the code into the Monadic Normal Form (a variant of the A-Normal form).
* `data/`: the predefined types and the benchmark input files.
  + `data/predefined/`: the predefined types.
  + `data/ri/ADT_LIBRARY/INTERFACE.ml`: the benchmark input files. For each `ADT` that is implemented by different underline library `LIBRARY`, There is a folder under path `data/ri/`. Besides `INTERFACE.ml` that are methods of given `ADT` implementation, these folders also provide the basic and refinement types for underline library (`lib_nty.ml` and `lib_rty.ml`), automata predicates (`automata_preds.ml`) and representation invariant `ri.ml`.
* `desymbolic/`: minterm transformation that convert SFA into FA.
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

### Running Benchmarks of Marple

In this section, we discuss the scripts that display the tables in the evaluation section of the paper.

#### Comprehensive Scripts

The following scripts run the benchmark suite displayed in Table 1 of the paper.

##### Step 1: Preprocess

The following scripts run the preprocess step on all benchmark suite displayed
in Table 1 of the paper, and store the result into a statfile file (defined in
config file `meta-config.json`, the default location is `.stat`).

    $ ../.venv/bin/python scripts/comprehensive.py silent ntyping data/ri

Then, the following prints the first part of table 1 (as Markdown table). The printed table is in _GitHub_ Markdown format, the reader can visualize the table via `https://gist.github.com/` or any other Markdown visualizer.

    $ ../.venv/bin/python scripts/comprehensive.py silent show-md-table1 data/ri

##### Step 2: Type Check

The following scripts run type check on all benchmark suite displayed in Table 1 of the paper, and store the result into statfile file (defined in config file `meta-config.json`, the default location is `.stat`). It will take about `15` mins:

    $ ../.venv/bin/python scripts/comprehensive.py silent typing data/ri

Then, the following prints the two parts of table 1 (please first perform preprocessing to get the statistics result for the first part of the table). The printed table is in _GitHub_ Markdown format, the reader can visualize the table via `https://gist.github.com/` or any other Markdown visualizer.

    $ ../.venv/bin/python scripts/comprehensive.py silent show-md-table1 data/ri


#### Detailed Steps

By add commanding the line argument `verbose`, all of the above scripts will show the actual command sent to **Marple** on each benchmark. For example, by running:

    $ ../.venv/bin/python scripts/comprehensive.py verbose ntyping data/ri

The script will print the following commands:

```
dune build --profile release
Running Basic Type Check on data/ri/Stack_LinkedList/concat.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/Stack_LinkedList/concat.ml
Running Basic Type Check on data/ri/Stack_LinkedList/concat_aux.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/Stack_LinkedList/concat_aux.ml
Running Basic Type Check on data/ri/Stack_LinkedList/cons.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/Stack_LinkedList/cons.ml
Running Basic Type Check on data/ri/Stack_LinkedList/empty.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/Stack_LinkedList/empty.ml
Running Basic Type Check on data/ri/Stack_LinkedList/head.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/Stack_LinkedList/head.ml
Running Basic Type Check on data/ri/Stack_LinkedList/is_empty.ml
./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/Stack_LinkedList/is_empty.ml
Running Basic Type Check on data/ri/Stack_LinkedList/tail.ml
...
```

Readers can try these commands to execute each step individually.

### Detail Usage of Marple

For reusability, we introduce the detail usage of Marple. Using **Marple**, you
can do the following.

#### Pretty Printing

See [Pretty Printing](#pretty-printing).

#### Basic Type Check and Normalization

The following command performs the basic (OCaml) type check (and normalization which converts code into A-normal form, converts LTLf formulae into symbolic regular language) for a given ADT implementation.

    $ ../.venv/bin/python scripts/comprehensive.py silent ntyping-one data/ri/FileSystem_Tree

The following command performs the basic type check (and normalization which convert code into A-normal form, converts LTLf formulae into symbolic regular language) for one interface of a given ADT implementation.

    $ ./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/init.ml

By enabling the `preprocess` option in the config file `meta-config.json`, **Marple** will print the result of preprocess: desugaring, basic type check, and normalization. The details can be found in [Configuration of Marple](#configuration-of-marple).

**Requirements:** We use bold and colored printing in the command line, make sure your terminal supports escape sequences.

For example,

    $ ./_build/default/bin/main.exe ri-ntype-check meta-config.json data/ri/FileSystem_Tree/init.ml

will print

```
Top Operation Normal Type Context:
&&:bool -> bool -> bool
==:int -> int -> bool
...

Top Function Normal Type Context:
getParent:Path.t -> Path.t
isRoot:Path.t -> bool
...

Automata Predicates:
val[@pred] storedP: (k : Path.t) (value : Bytes.t) = ♢(⟨put x_0 x_1 = vret | x_1 == value ∧ x_0 == k⟩ ∧ ◯☐¬⟨put x_0 x_1 = vret | x_0 == k⟩)
...

Top Operation Rty Context:
&&:(a:{v:bool | true}) → (b:{v:bool | true}) → {v:bool | v <=> (a ∧ b)}
||:(a:{v:bool | true}) → (b:{v:bool | true}) → {v:bool | v <=> (a ∨ b)}
...

Top Function Rty Context:
getParent:(a:{v:Path.t | true}) → {v:Path.t | v == (parent a)}
isRoot:(a:{v:Path.t | true}) → {v:bool | v == (is_root a)}
...

Source Code:

let init = fun (u : unit) ->
  (let (unused!0 : unit) = init (getRoot (() : unit)) in
   let (unused!1 : unit) = put (getRoot (() : unit)) (fileInit (() : unit)) in
   (() : unit) : unit)
val[@assertSRLRty] init: (p:Path.t) ⇢ (u:{v:unit | true}) → [(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))]{v:unit | true}[(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))]


Basic Typed:
let init = (fun (u : unit) ->
   (let (unused!0 : unit) =
      ((init : Path.t -> unit)
         ((getRoot : unit -> Path.t) (() : unit) : Path.t) : unit) in
    (let (unused!1 : unit) =
       ((put : Path.t -> Bytes.t -> unit)
          ((getRoot : unit -> Path.t) (() : unit) : Path.t)
          ((fileInit : unit -> Bytes.t) (() : unit) : Bytes.t) : unit) in
     (() : unit) : unit) : unit) : unit -> unit)
val[@assertSRLRty] init: (p:Path.t) ⇢ (u:{v:unit | true}) → [(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))]{v:unit | true}[(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))]


Normalized:
init:
fun (u : unit) ->
  let (x!36 : Path.t) = getRoot () in
  let (unused!0 : unit) = (init : Path.t -> unit) x!36 in
  let (x!37 : Bytes.t) = fileInit () in
  let (x!38 : Path.t) = getRoot () in
  let (unused!1 : unit) = (put : Path.t -> Bytes.t -> unit) x!38 x!37 in ()
```

#### HAT Type check

The following command performs the HAT type check for a given ADT implementation. It will take about `3` min:

    $ ../.venv/bin/python scripts/comprehensive.py silent typing-one data/ri/FileSystem_Tree

The following command performs the HAT type check for an interface of a given ADT implementation.

    $ ./_build/default/bin/main.exe ri-type-check meta-config.json data/ri/FileSystem_Tree/add.ml

By enable the `typing` option in the config file `meta-config.json`, **Marple** will print the typing rules and subtyping rules used during type check.

**Requirements:** We use bold and coloring printing in command line, make sure your terminal supports escape sequences.

For example,

    $ ./_build/default/bin/main.exe ri-type-check meta-config.json data/ri/FileSystem_Tree/add.ml

will print

```
...
Subtyping:
R: getParent:(a:{v:Path.t | true}) → {v:Path.t | v == (parent a)}, isRoot:(a:{v:Path.t | true}) → {v:bool | v == (is_root a)}, getRoot:(a:{v:unit | true}) → {v:Path.t | is_root v}, fileInit:(a:{v:unit | true}) → {v:Bytes.t | is_dir v}, addChild:(a:{v:Bytes.t | true}) → (b:{v:Path.t | true}) → {v:Bytes.t | is_dir v}, delChild:(a:{v:Bytes.t | true}) → (b:{v:Path.t | true}) → {v:Bytes.t | is_dir v ∧ is_del v}, getChild:(a:{v:Bytes.t | true}) → {v:Path.t | true}, hasChild:(a:{v:Bytes.t | true}) → {v:bool | true}, setDeleted:(a:{v:Bytes.t | true}) → {v:Bytes.t | is_del v}, isDir:(a:{v:Bytes.t | true}) → {v:bool | v == (is_dir a)}, add_path_in_dir:(p:Path.t) ⇢ (path:{v:Path.t | true}) → (path':{v:Path.t | true}) → [(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))]{v:unit | true}[(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))], p!0:{v:Path.t | true}, path:{v:Path.t | true}, content:{v:Bytes.t | true}, x!36:{v:bool | ¬v}, a!168:{v:unit | ¬x!36}, parent_path:{v:Path.t | v == (parent path)}, a!549:{v:Bytes.t | true}, bytes':{v:Bytes.t | v == a!549}, x!37:{v:bool | v == (is_dir bytes')}, a!1627:{v:unit | ¬x!37}
⊢ {v:bool | ¬v}
<:{v:bool | true}
Subtyping:
R: getParent:(a:{v:Path.t | true}) → {v:Path.t | v == (parent a)}, isRoot:(a:{v:Path.t | true}) → {v:bool | v == (is_root a)}, getRoot:(a:{v:unit | true}) → {v:Path.t | is_root v}, fileInit:(a:{v:unit | true}) → {v:Bytes.t | is_dir v}, addChild:(a:{v:Bytes.t | true}) → (b:{v:Path.t | true}) → {v:Bytes.t | is_dir v}, delChild:(a:{v:Bytes.t | true}) → (b:{v:Path.t | true}) → {v:Bytes.t | is_dir v ∧ is_del v}, getChild:(a:{v:Bytes.t | true}) → {v:Path.t | true}, hasChild:(a:{v:Bytes.t | true}) → {v:bool | true}, setDeleted:(a:{v:Bytes.t | true}) → {v:Bytes.t | is_del v}, isDir:(a:{v:Bytes.t | true}) → {v:bool | v == (is_dir a)}, add_path_in_dir:(p:Path.t) ⇢ (path:{v:Path.t | true}) → (path':{v:Path.t | true}) → [(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))]{v:unit | true}[(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p⟩)*))))], p!0:{v:Path.t | true}, path:{v:Path.t | true}, content:{v:Bytes.t | true}, x!36:{v:bool | ¬v}, a!168:{v:unit | ¬x!36}, parent_path:{v:Path.t | v == (parent path)}, a!549:{v:Bytes.t | true}, bytes':{v:Bytes.t | v == a!549}, x!37:{v:bool | v == (is_dir bytes')}, a!1627:{v:unit | ¬x!37}
⊢ (((((.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p!0⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p!0⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p!0 ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p!0⟩)*))))) ∧ ((.*;(⟨connectChild x_0 x_1 = vret | x_1 == path⟩;.*)) ∨ (.*;(⟨init x_0 = vret | x_0 == path⟩;.*)))ᶜ);⟨mem x_0 = vret | x_0 == path ∧ ¬vret⟩) ∧ (.*;(⟨put x_0 x_1 = vret | x_1 == a!549 ∧ x_0 == parent_path⟩;(.\⟨put x_0 x_1 = vret | x_0 == parent_path⟩)*)));⟨get x_0 = vret | x_0 == parent_path ∧ vret == a!549⟩
<:(.\⟨connectChild x_0 x_1 = vret | ¬x_0 == (parent x_1)⟩)* ∧ (⟨is_root p!0⟩* ∨ ((.*;(⟨connectChild x_0 x_1 = vret | x_0 == p!0⟩;.*))ᶜ ∨ (.*;(⟨put x_0 x_1 = vret | x_0 == p!0 ∧ is_dir x_1⟩;(.\⟨put x_0 x_1 = vret | x_0 == p!0⟩)*))))
matched case (False): true
Check::Match [✓](Typecheck__Bidirectional.comp_htriple_check.end_info:425)
Check::LetApp [✓](Typecheck__Bidirectional.comp_htriple_check.end_info:317)
Check::TEOpApp [✓](Typecheck__Bidirectional.comp_htriple_check.end_info:266)
Check::LetApp [✓](Typecheck__Bidirectional.comp_htriple_check.end_info:317)
matched case (False): true
Check::Match [✓](Typecheck__Bidirectional.comp_htriple_check.end_info:425)
Check::TEOpApp [✓](Typecheck__Bidirectional.comp_htriple_check.end_info:266)
Check::Lam [✓](Typecheck__Bidirectional.value_type_check.end_info:130)
Check::Lam [✓](Typecheck__Bidirectional.value_type_check.end_info:130)
Task 1(add): exec time 19.768031(s), type check succeeded
DT(FileSystem)  Task 1(add): exec time 19.768031(s), type check succeeded
```

#### Configuration of Marple

All commands of **Marple** will take a universal configuration file (`meta-config.json`) in JSON format as its first argument. Precisely, the JSON file outputs results in JSON format to some output directory.
- the `debug_tags` field controls the debug information output. Precisely, we have the following options:
  + if the `preprocess` field is true, **Marple** will print the preprocessed result. It will print the given source code, typed code, and the code in A-Normal Form.
  + if the `typing` field is set as true, **Marple** will print the typing judgement of each step in the type check.
  + if the `result` field is set as true, **Marple** will print the type check result.
- the `resfile` field indicates the path of the output file of type check.
- the `logfile` field indicates the path of the log file of type check.
- the `statfile` field indicates the path of the statistics file of type check.
- the `uninterops` field indicates the built-in operators and method predicates used in the current benchmarks.
- the `prim_path` field indicates the predefined refinement types for a number of
OCaml primitives, including various arithmetic operators, and data constructors, and axioms of uninterpreted functions.

#### Input File Formats

As a verification tool for representation invariant of datatypes that is
implemented by an underline stateful library, **Marple** expects input that contains
the specification of underline stateful library and a representation invariant
shared by all interfaces. For example, when **Marple** can type check an
interface `INTERFACE` via the following command (introduced in [HAT Type
check](#hat-type-check)):

    $ ./_build/default/bin/main.exe ri-type-check meta-config.json ADT_DIR/INTERFACE.ml

a folder (`ADT_DIR`) should contain the following files:

- `ADT_DIR`
  + `lib_nty.ml` (the basic (OCaml) typing for the underline stateful library)
  + `lib_rty.ml` (the HAT typing for the underline stateful library)
  + `automata_preds.ml` (automata predicates, e.g., 𝑃stored in Example 4.1, it is optional)
  + `ri.ml` (representation invariant shared by all interfaces)
  + `INTERFACE.ml` (source code and HAT of this interface)

#### Format of `lib_nty.ml`

It is the same as the value declaration in OCaml signature:

```c
val NAME : OCAML_TYPE
```

#### Format of `lib_rty.ml`

It has the following format where `HAT` is defined in [Syntax of HAT](#syntax-of-hat).

```c
let[@libRty] NAME = HAT
```

where `NAME` is simply a string.

#### Format of `ri.ml` and `automata_preds.ml`

It has the following format where `SFA` is defined in [Syntax of HAT](#syntax-of-hat).

```c
let[@pred] NAME (ARG : OCAML_TYPE) ... = SFA
```

#### Format of `INTERFACE.ml`

It has the following format where `HAT` is defined in [Syntax of HAT](#syntax-of-hat).

```c
let INTERFACE = OCAML_EXPR

let[@assertRty] INTERFACE = HTY
```

The source code `OCAML_EXPR` expected by **Marple** is simply an OCaml function listing. Currently, **Marple** handles only a subset of OCaml, it does not handle features involving references and effects, parametric polymorphism, or concurrency. Additionally, all functions should be annotated with precise input and output type; all left-hand-side variables in a let binding should be annotated with its precise type.

#### Syntax of HAT

The syntax of the `HAT` and `SFA` is similar to the OCaml let expression but with [attributes](https://v2.ocaml.org/manual/attributes.html):

```c
VAR := string
OCAML_TYPE:= the OCmal type

OP := "==" | "!=" | "+" | "-" | "<" | ">" | ...
EFFOP := string

LIT :=
| "true"
| "false"
| INT
| VAR
| OP VAR ...

PROP :=
| LIT
| "implies" PROP PROP
| "iff" PROP PROP
| PROP "&&" PROP
| PROP "||" PROP
| "not" PROP
| "fun ((" NAME " [@forall]) : " OCAML_TYPE ") ->" PROP // ∀NAME:OCAML_TYPE. PROP

RTY :=
| "(" PROP ":[%" VAR ":" OCAML_TYPE "])" // base type
| "fun ?l(" NAME "=" RTY ") -> " HAT // arrow type
| "fun ((" NAME ":" OCAML_TYPE ")) [@ghost]) -> " HAT // ghost arrow type

EVENT_ARG :=
| VAR
| "(" OCAML_EXPR "[@d])" // ∼𝑣𝑥 in type aliases in Figure 4

SFA_PRED := NAME // automata predicate, e.g., 𝑃stored in Example 4.1

SFA :=
| EFFOP "(" EVENT_ARG "," ... "," VAR "," PROP ")" // symbolic event <EFFOP ... EVENT_ARG ... = VAR | PROP >
| "_X" SFA // next modality
| "_G" SFA // global modality
| "_F" SFA // final modality
| "lastL" // last modality
| SFA ";" SFA // concat
| SFA "&&" SFA // intersection
| SFA "||" SFA // union
| "not" SFA // complement
| SFA_PRED LIT ... // automata predicate application, e.g., 𝑃exists (k) in Example 4.2

HAT :=
| RTY
| "[|" HAT ";" HAT ";" ... "|]" // intersection type
| "{ pre = " SFA "; res =" RTY "; post = " SFA "}" // HAT [pre] rty [post]
| "{ pre = " SFA "; res =" RTY "; newadding = " SFA "}" // HAT [pre] rty [pre; newadding]

```

The definition of the coverage type is consistent with Figure 4. Precisely,
+ the value literal is defined as `LIT`.
+ the qualifier is defined as `PROP`.
+ the refinement type is defined as `RTY`.
+ the Symbolic Finite Automata is defined as `SFA`. Notice that, the type alias `∼𝑣𝑥` is notated by `[@d]`. We also accept the automata predicates application, e.g., `𝑃exists (k)` in Example 4.2.
+ the Hoare Automata Types is defined as `HAT`, we use an abbreviation with the
  `newadding` field when the postcondition automata is just appending new events
  to the precondition automata.
+ Our syntax share the same syntax sugar with OCaml programs, thus, for example

```
let[@assertRty] add ((p : Path.t) [@ghost]) ?l:(path = (true : [%v: Path.t]))
    ?l:(content = (true : [%v: Bytes.t])) =
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
```

can be desugared as

```ocaml
let[@assertRty] add =
    fun ((p : Path.t) [@ghost]) ->
    fun ?l:(path = (true : [%v: Path.t])) ->
    fun ?l:(content = (true : [%v: Bytes.t])) ->
  { pre = rI p; res = (true : [%v: bool]); post = rI p }
```

### Coq Formalization

See `formalization/README.md`.
