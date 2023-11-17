FROM ocaml/opam:debian-ocaml-4.14-flambda
RUN sudo apt-get update
RUN sudo apt install -y software-properties-common
RUN sudo apt-get install -y python3 python3-pip python3-venv
RUN python3 -m venv .venv
RUN . .venv/bin/activate
RUN sudo apt-get install -y libgmp-dev
RUN opam init --auto-setup
RUN opam update
RUN opam switch create HAT --package=ocaml-variants.4.14.1+options,ocaml-option-flambda
RUN eval $(opam env)
RUN opam repo add coq-released https://coq.inria.fr/opam/released
RUN opam update
RUN opam install coq.8.18.0
RUN eval $(opam env)
RUN opam install coq-stdpp.1.9.0 coq-hammer-tactics.1.3.2+8.18
RUN opam install dune.3.11.1 core.v0.15.0 core_unix.v0.15.0 yojson.1.7.0 conf-c++.1.0 conf-python-3.1.0.0 qcheck.0.18.1 ocolor.1.3.0 dolog.6.0.0 ocamlbuild.0.14.1
RUN opam install z3.4.8.14
RUN sudo apt-get install -y vim
SHELL ["/bin/bash", "-lc"]
ARG CACHEBUST=1
ADD ocaml5_parser_a ocaml5_parser
RUN cd ocaml5_parser && opam install . && cd ..
ADD zzdatatype zzdatatype
RUN cd zzdatatype && opam install . && cd ..
ADD utils utils
RUN cd utils && opam install . && cd ..
ADD normal5ty normal5ty 
RUN cd normal5ty && opam install . && cd ..
RUN eval $(opam env)
ADD HATs HATs
WORKDIR HATs
USER root
