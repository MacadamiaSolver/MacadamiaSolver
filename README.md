# MacadamiaSolver

__MacadamiaSolver__ (or simple __MandmS__ as an acronym for MacANDaMia solver) is a theorem prover (SMT-solver) in Presburger Arithmetic based on the finite-automata approach for deciding.

## Dependencies
To build the project you'll need these dependencies to be installed:
- OPam - OCaml package manager.
- OCaml >5.0.

You may install the dependencies using the following bash commands:
```bash
#
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
opam switch create 5.2.0+flambda --packages=ocaml-variants.5.2.0+options,ocaml-option-flambda --yes
```

## Building
The MacadamiaSolver project can be built like this:
```bash
# Installing project dependencies.
opam install . --deps-only --with-test
# Building the project and its tests.
opam exec -- dune build @check @all
```

The executable binary is available in the `_build` dir.

## Usage

By default opam build an executable in `./_build/default/bin/main.exe`. Starting it up brings you to REPL for evaluating theorem proving. We strongly encourage you to run it the following way
```bash
ledit ./_build/default/bin/main.exe
```
Using common unix `ledit` allows navigating through the input and switching the history of executed commands.

Commands supported by the REPL and their semantics:
- `let <name> <params...> = <FOL formula>` - define a new predicate.
- `list` - list existing predicates.
- `eval <formula>` - prove a theorem.
- `dump <FOL formula>` - display the automaton for the desired FOL formula using GraphViz.
- `parse <FOL formula>` - display the AST tree for the FOL formula.
- `help` - display help information.

MacadamiaSolver uses the syntax defined by the following grammar rules for expression first-order logic statements:
```
formula ::= ( formula )
          | ~formula
          | formula & formula
          | formula '|' formula
          | formula -> formula
          | formula <- formula
          | formula <-> formula
          | E var formula
          | A var formula
          | atomic_formula

atomic_formula ::= term = term
                 | term != term
                 | term < term
                 | term > term
                 | term <= term
                 | term >= term
                 | pred term*

pred ::= [a-zA-Z_][a-zA-Z_0-9]*

term ::= (term)
       | const (term) | const var
       | var
       | const
var ::= [a-zA-Z_][a-zA-Z_0-9]*
const ::= [0-9]+
```

Example usage:
```
eval Ax Ey x = y + 1
```

Output:
```
Result: true
```

## Future development

Our future plans include:
- Supporting predicates.
- Implementing the prover for the existential Semёnov arithmetic (`<N, 2**x, +, <, ...>`).
- Supporting SMT-Lib for evaluating benchmarks
