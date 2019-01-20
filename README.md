# someSAT - a SAT-solver

This was a coding exercise for a course I took in NCTU in 2016. Was second
fastest in the class or something like that. I cleaned up the code a little
since then. The program solves
[SAT problems](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem).
2-literal-watching, VSIDS and 1UIP resolution are implemented. There is also a
branch `add_preprocessor`, where a couple of preprocessing techniques are
implemented. However, those don't bring much, and the code is overall uglier
and less tested.

## Usage

```
make
./somesat path_to_cnf [path_to_solution]
```

As input the solver expects a file in
[CNF Format](https://people.sc.fsu.edu/~jburkardt/data/cnf/cnf.html).

If `path_to_solution` not given will try to create a file with the same name as
the input, but with extension `.sat` instead of `.cnf`.

`make install` will install into `~/.usr/bin` by default (duh).
If for whatever reason you want to install it, specify desired prefix with
`make install PREFIX=/path`.
