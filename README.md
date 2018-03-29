# Reading triage

["The lambda calculus is algebraic", Peter Selinger](https://www.mscs.dal.ca/~selinger/papers/combinatory.pdf):
"We argue that free variables should not be interpreted as elements in a model, as is usually done, but as indeterminates."

["On the algebraic models of lambda calculus", Antonino Salibra](https://pdfs.semanticscholar.org/055d/69ee4dc95fbf6457419c90338493667478b1.pdf):
"The variety (equational class) of lambda abstraction algebras was introduced
to algebraize the untyped lambda calculus in the same way Boolean algebras algebraize the classical propositional calculus."
Propositional logic is modeled by Boolean algebra.
First-order logic is modeled by cylindric algebra?
Lambda calculus is modeled by lambda abstraction algebra.
Why algebra? Because it is equational?
[Wikipedia "algebraic logic"](https://en.wikipedia.org/wiki/Algebraic_logic)

["The algebraic lambda-calculus", Lionel Vaux](https://pdfs.semanticscholar.org/7596/19f05a42ff3045bcf87fcaa3edbff01e1130.pdf)

["Lambda abstraction algebras: representation theorems", Don Pigozzi, Antonino Salibra](https://pdfs.semanticscholar.org/44c9/2ad00b8ceba78319005db048b24d61a80748.pdf):

["Applying Universal Algebra to Lambda Calculus", Giulio Manzonetto, Antonino Salibra](http://www.dsi.unive.it/~salibra/mainfinale.pdf)

Dana Scott's PCF; also search the Internet for "the language pcf"
["Introduction to Real PCF (Notes)", Mart\'in H\"otzel Escard\'o](http://www.cs.bham.ac.uk/~mhe/papers/RNC3.pdf)

# Need tidying-up

Abdullah wants to make a monad-aware programming language and banish `fmap`.

The plan is to research two related things in parallel:

- the relationship among laziness, strictness, totality, and monads
- using algebraic subtyping to mix parametric subtyping and inheritance subtyping

Abdullah hints that "lazy is monadic over strict".
What does it mean?
(Erik: I forgot the exact words. I need to ask him for a formal statement.)

The terms "lazy" and "strict" imply operational semantics.
They are two strategies for beta-reduction.
"Lazy" is normal-order.
"Strict" is applicative-order.

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
    - Due to the Church-Rosser property, "the difference between strict and lazy goes away in a strong functional language".
        - [Church-Rosser theorem](https://en.wikipedia.org/wiki/Church%E2%80%93Rosser_theorem)
        - [Church-Rosser property](http://mathworld.wolfram.com/Church-RosserProperty.html)

A semantic function maps a well-formed expression to a meaning (a denotation, a mathematical value).
(Erik: Is this standard programming language theory terminology?)

["Corecursion and coinduction: what they are and how they relate to recursion and induction", Mike Gordon](http://www.cl.cam.ac.uk/archive/mjcg/plans/Coinduction.html):
"My goal here is to try to understand these things through the activity of creating a simple explanation."

["Data and Codata", Dan Piponi](http://blog.sigfpe.com/2007/07/data-and-codata.html):
"The program might not terminate, but from a mathematical perspective this is a completely well defined function."
"Note the duality: in structural recursion we 'deconstruct' the argument and then we're allowed to recurse. In guarded recursion we recurse first, and then we're allowed to use the constructor."

["Data vs Codata", Michael Maloney](https://www.tac-tics.net/blog/data-vs-codata)

In structural recursion, we require that the function deconstructs the input into smaller parts;
we require that the function breaks down (takes apart) the input.
In structural corecursion, we require that the function constructs the output into bigger parts;
we require that the function builds up the output.

- Wikipedia
    - [Semantics](https://en.wikipedia.org/wiki/Semantics_(computer_science))
        - [Denotational semantics](https://en.wikipedia.org/wiki/Denotational_semantics)
            - "An important tenet of denotational semantics is that semantics should be compositional:
            the denotation of a program phrase should be built out of the denotations of its subphrases."
                - This needs an example.

- [Stephen Dolan's Ph.D. thesis "Algebraic subtyping"](https://www.cl.cam.ac.uk/~sd601/thesis.pdf)
    - [Subtyping on Wikipedia](https://en.wikipedia.org/wiki/Subtyping)

Scala already tries to join parametric subtyping and inheritance subtyping.
What is the problem with Scala?

The folder [abdullah-conjecture](abdullah-conjecture/)
contains a proposed partial proof of the Abdullah conjecture for all Haskell 98 type endofunctions.
The proof can be checked by the Lean theorem prover version 3.
See also the [Lean prover home page](https://leanprover.github.io/).
To edit Lean source files, use Visual Studio Code and its Lean plugin.

Other past researches:

- Brzozowski quotients.
    - [Yacc is dead](https://arxiv.org/abs/1010.5023)
    - "Parsing with derivatives"

- Laziness, complete laziness, full laziness, minimal reduction, what?
    - [Olin Shivers and Mitchell Wand: Bottom-up beta substitution: uplinks and lambda-DAGs](http://www.brics.dk/RS/04/38/BRICS-RS-04-38.pdf)
