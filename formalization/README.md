# Proof Readme #

## Proof File Structures

The files containing the definitions and proofs of our core language
**λ<sup>E</sup>** are structured as follows:
- `Atom.v`: Definitions and notations of atoms (variables) in **λ<sup>E</sup>**.
- `Tactics.v`: Some auxiliary tactics.
- `NamelessTactics.v`: Auxiliary tactics for the locally nameless representation.
- `CoreLang.v`: Definitions and notations of terms in **λ<sup>E</sup>**.
- `CoreLangProp.v`: Lemmas for the syntax of **λ<sup>E</sup>**.
- `Trace.v`: Definitions and notations of traces.
- `OperationalSemantics.v`: Definitions and notations of the small-step
  operational semantics of **λ<sup>E</sup>**.
- `BasicTyping.v`: Definitions and notations for the basic typing.
- `BasicTypingProp.v`: Lemmas for the basic typing rules.
- `Qualifier.v`: Definitions and notations for qualifiers.
- `ListCtx.v`: Definitions and notations for reasoning about type context.
- `RefinementType.v`: Definitions and notations of Hoare Automata Types.
- `Denotation.v`: Definitions and notations of the automaton and type denotation.
- `Instantiation.v`: Definition and notations of substitution and
  multi-substitution operation.
- `InstantiationProp.v`: Lemmas for multi-substitution.
- `Typing.v`: Definitions and notations for the typing rules; as well as the
  statements and proofs of the fundamental and soundness theorems.

## Compilation and Dependencies

Our formalization is tested against `Coq 8.18.0`, and requires the libraries
`coq-stdpp 1.9.0` and `coq-hammer-tactics 1.3.2+8.18`. The easiest way to
install the dependencies is via [OPAM](https://opam.ocaml.org/doc/Install.html).
For example:

```sh
# If you have not already used opam
opam init
opam update
# Create a new opam environment to test this project
opam switch create HAT --package=ocaml-variants.4.14.1+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin coq 8.18.0
opam pin coq-stdpp 1.9.0
opam pin coq-hammer-tactics 1.3.2+8.18
```

> Notice: We have installed all dependencies listed above in our docker image.

To build and check the Coq formalization, simply run `make` in the
`formalization` directory. The command `Print Assumptions soundness` at the end
of file `Typing.v` should print out `Axioms: builtin_typing_relation : ...`. It
means our proofs do not rely on any axioms except for the definition
`builtin_typing_relation` (i.e. `Δ` in the paper), which we deliberately leave
undefined, as the type system is parameterized over this relation.

Our formalization takes inspiration and ideas from the following work, though does not directly depend on them:
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/): a lot of our formalization is inspired by the style used in Software Foundations.
- [The Locally Nameless Representation](https://chargueraud.org/research/2009/ln/main.pdf): we use locally nameless representation for variable bindings.

## Paper-to-artifact Correspondence

| Definition/Theorems          | Paper                                                                       | Definition                                                                                                                | Notation                        |
|------------------------------|-----------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------|---------------------------------|
| Term Syntax                  | Fig. 2                                                                    | mutually recursively defined as values (`value`) and expressions (`tm`) in file `CoreLang.v` (line `53`)                      |                                 |
| Trace Syntax                 | Fig. 3                                                                    | `trace` in file `Trace.v` (line `23`)                                                                                     | `[ev{ op ~ v1 := v2 }]`         |
| Operational semantics        | Fig. 3 (and Fig. 9 in appendix) | `step` in file `OperationalSemantics.v` (line `18`)                                                                       | `α ⊧ e ↪{ α } e`        |
| Type Syntax                  | Fig. 4                                                                    | basic types (`ty`) in file `CoreLang` (line `22`), Refinement Types (`pty`) and Hoare Automata Types (`hty`) in file `RefinementType.v` (line `43` and `49`) | `{:b \| ϕ }`, `t ⇨ τ`, `b ⇢ t`, `<[A]t[A]>` and `τ ⊓ τ`                               |
| Basic typing rules           | Fig. 10 in appendix                                         | mutually recursive definition of `tm_has_type` and `value_has_type` in file `BasicTyping.v` (line `39`)                     | `Γ ⊢t e ⋮t T` and `Γ ⊢t v ⋮v T` |
| Type Erasure                 | Fig. 5                                                                    | `pty_erase` (line `74`), `hty_erase` (line `81`) and `ctx_erase` (line `95`) in file `RefinementTypes.v`                                          | `⌊ t ⌋`, `⌊ τ ⌋` and `⌊ Γ ⌋*`            |
| Well-formedness | Fig. 5 (and Fig. 12 in appendix)                                                                  | `wf_pty` (line `34`), `wf_am` (line `27`) and `wf_hty` (line `45`) in file `Typing.v`                                                               | `Γ ⊢WFp t`, `Γ ⊢WFa A` and `Γ ⊢WF τ`                       |
| Subtyping | Fig. 5 (and Fig. 12 in appendix) | `pty_subtyping` and `subtyping` in file `Typing.v` (line `69` and `76`)                                                                                | `Γ ⊢ t1 <⋮p t2` and `Γ ⊢ τ1 <⋮ τ2` |
| Typing rules                 | Fig. 6 (and Fig. 13 in appendix) | `effop_type_check` (line `95`), and mutually inductive propositions `value_type_check` (line `152`) and `term_type_check` (line `109`) in file `Typing.v`            | `Γ ⊢ op ⋮o t`,  `Γ ⊢ v ⋮v t` and `Γ ⊢ e ⋮t τ` |
| Trace language                 | Fig. 7                                                                   | `langA` in file `Denotation.v` (line `33`)                                                                                | `a⟦ A ⟧`                        |
| Type denotation              | Fig. 7                                                                   | `ptyR` (line `69`) and `htyR` (line `90`) in file `Denotation.v`                                                                                 | `p⟦ t ⟧` and `⟦ τ ⟧`                         |
| Type context denotation      | Fig. 7                                                                   | `ctxRst` in file `Denotation.v` (line `113`)                                                                              |                                 |
| Fundamental Theorem          | Theorem 4.8                                                                | `fundamental` in file `Typing.v` (line `916`)                                                                               |                                 |
| Soundness theorem            | Corollary 4.9                                                                | `soundness` in file `Typing.v` (line `944`)                                                                                 |                                 |

## Differences Between Paper and Artifact

- Basic types: our formalization only has two base types: nat and bool.
- Effectful operators: to simplify the syntax, all operators in our
  formalization only take one argument
- Pure operators (e.g., arithmetic operators): they are treated as effectful
 operators, whose return value is independent of the context trace, and will not
 interfere the result of other operators.
- For simplicity, pattern-matching only matches on Boolean discriminees.
  Pattern matching on natural numbers such as

```
match n with
| 0 -> e1
| S m -> e2
```

is implemented as follows:

```
let cond = op_eq_zero n in
match cond with
| true -> e1
| else ->
  let m = op_minus_one n in
  e2
```
- The formalization treats the distinction between values and expressions
  (computations) more explicitly, connecting them using a standard `return`
  syntax.
- Instead of syntactic subtyping presented in the paper, we use semantic
  subtyping in the formalization.
- The formalization only considers a minimal set of symbolic finite automata
  relevant to the metatheory. The complete set of SFAs can be
  straightforwardly added, but is orthogonal to the formal development.
- We encode the propositions in refinement types as shallowly embedded Coq
  propositions.
- We assume all input programs are alpha-converted, such that all variables have
  unique names.
- We use the [locally nameless
  representation](https://chargueraud.org/research/2009/ln/main.pdf) to
  represent binders in all of our definitions, thus they look slightly different
  from the ones shown in the paper.
