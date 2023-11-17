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
RUN opam install coq-stdpp.1.9.0
RUN opam install coq-hammer-tactics.1.3.2+8.18
RUN opam install dune.3.11.1
RUN opam install core.v0.15.0
RUN opam install core_unix.v0.15.0
RUN opam install yojson.1.7.0
RUN opam install conf-c++.1.0
RUN opam install conf-python-3.1.0.0
RUN opam install qcheck.0.18.1
RUN opam install ocolor.1.3.0
RUN opam install dolog.6.0.0
RUN opam install ocamlbuild.0.14.1
RUN opam install z3.4.8.14
RUN sudo apt-get install -y vim
SHELL ["/bin/bash", "-lc"]
ARG CACHEBUST=1
RUN git clone https://github.com/mitchell-lang/ocaml5_parser.git && cd ocaml5_parser && git pull origin ef47e625b5fa33497a3134f40db42ce8ffdbc134 && git checkout -b ef47e625b5fa33497a3134f40db42ce8ffdbc134 && opam install . && cd ..
RUN git clone https://github.com/zhezhouzz/zzdatatype.git && cd zzdatatype && git pull origin 8f224463f94021c35649c347850d2f57dde3f7b0 && git checkout -b 8f224463f94021c35649c347850d2f57dde3f7b0 && opam install . && cd ..
RUN git clone https://github.com/zhezhouzz/utils.git && cd utils && git pull origin 4e3066bb09cc2dad4babd5f55e330ada8ecb1e91 && git checkout -b 4e3066bb09cc2dad4babd5f55e330ada8ecb1e91 && opam install . && cd ..
RUN eval $(opam env)
RUN git clone https://github.com/mitchell-lang/normal5ty.git && cd normal5ty && git pull origin 2fef196bb91468b090b269b3bdef3e4946ac8fe4 && git checkout -b origin 2fef196bb91468b090b269b3bdef3e4946ac8fe4 && opam install . && cd ..
RUN eval $(opam env)
RUN git clone https://github.com/zhezhouzz/HATs.git
WORKDIR HATs
RUN git config pull.ff only
RUN git checkout pldi24-sm
RUN git pull origin 5c607bb10188114d1f28ce872fcbbe77a90ecbe2
RUN git checkout -b 5c607bb10188114d1f28ce872fcbbe77a90ecbe2
