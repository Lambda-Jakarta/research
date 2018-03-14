Abdullah wants to make a monad-aware programming language and banish `fmap`.

- [David Turner's paper "Total functional programming"](http://www.jucs.org/jucs_10_7/total_functional_programming/jucs_10_07_0751_0768_turner.pdf)
    - [citeseerx backup link](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.106.364&rep=rep1&type=pdf)
    - Advantages:
        - Total functional programming simplifies denotational semantics. No need to consider bottoms.
    - Disadvantages:
        - A total functional programming language is not Turing-complete.
    - "How do we write operating systems?"
        - Codata and corecursion.
    - "Codata definitions are equations over types that produce final algebras, instead of the initial algebras we get for data definitions."
        - This statement sounds important but it is meaningless to those who are not fluent in category theory.
        We should write some examples to help the reader understand this statement.
    - Walther recursion can be thought as structural recursion enhanced for convenience?
    - See also [Danielsson et al.'s "Fast and loose reasoning is morally correct"](http://www.cse.chalmers.se/~nad/publications/danielsson-et-al-popl2006.html).
- [Stephen Dolan's Ph.D. thesis "Algebraic subtyping"](https://www.cl.cam.ac.uk/~sd601/thesis.pdf)

The folder [abdullah-conjecture](abdullah-conjecture/)
contains a proposed partial proof of the Abdullah conjecture for all Haskell 98 type endofunctions.
The proof can be checked by the Lean theorem prover version 3.
See also the [Lean prover home page](https://leanprover.github.io/).
To edit Lean source files, use Visual Studio Code and its Lean plugin.
