

## Mathematics

Lean is not only a powerful functional programming language, but is also known for being a flexible proof assistant. It has helped thousands of mathematicians worldwide to formalize starter up-to research-level mathematics.

The best learning resource for mathematics with Lean is the book [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean). It is quite long, but has a lot of step-wise exercises to learn the language and the Mathlib library.




### Searching mathematical patterns

The collection of definitions and theorems in Mathlib is large. Sometimes the naming of the modules, namespaces and proofs is not entirely consistent. Use these resources to find the definitions and theorems you need:

You can use [Loogle](https://loogle.lean-lang.org/) to search for definitions that help to solve a particular open goal. To open `loogle` in VS Code, you can use the command palette (`Ctrl + Shift + P`) and type `Loogle: Search for a definition`.

Examples of Loogle searches:

- To find theorems about addition and less than:

  ```lean
  ?a + ?b < ?c
  ```

- To find theorems about multiplication being associative:

  ```lean
  ?a * (?b * ?c) = (?a * ?b) * ?c
  ```

- To find definitions involving lists and membership:

  ```lean
  ?a ∈ List ?b
  ```

- To find theorems about natural number induction:

  ```lean
  (?P 0) → (∀ n, ?P n → ?P (n + 1)) → ∀ n, ?P n
  ```

- Lemma's defined for the type `ENNReal` (extended non-negative real numbers):
  
  ```lean
  ENNReal _ / _ = _ ↔ _
  ````
  
### Searching mathematical concepts


You can also search using English / natural language on [Moogle](https://moogle.ai/) or [Lean Explore](https://www.leanexplore.com). For natural language search, simply describe what you're looking for in plain English:

- "addition is associative"
- "if a function is continuous then it is measurable"
- "natural number induction principle"
- "Cauchy-Schwarz inequality"
- "derivative of composition of functions"

If you prefer reading documentation in your browser, you can search on the [HTML pages](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html) with cross-references and syntax highlighting.


There is a new place where you can copy-paste the current proof state and search for theorems that can help you solve it: https://premise-search.com/.

## Practice

Mathlib4 is the most popular Lean library.

- Contains all of undergraduate mathematics.
- Contains all of graduate mathematics.
- Contains most of research-level mathematics.
- But, **no riddles**!

You can play with some solved riddles (or computational problems) by navigating the [`RiddleProofs`](./RiddleProofs) directory.


_**Note**: Difficult proofs where sometimes solved with the help of Claude Opus 4 (not covered in this workshop). For beginners in Lean, it is recommended not to configure any LLM agents while learning the basics as this can slow down your learning._

### Simple riddles

Monty Hall problem:

![image:w:30%](img/monty_hall.png)

Jealous husbands problem:

- Can you generalize to N couples?
- What about more than 2 people in a boat?

![image:w:30%](img/jealous_husbands.jpg)


### Lights out

Look at examples in `BoardExamples.lean` and visualisation in `Widget.Lean`.

Mathematical interpretation is in `LinearAlgebra.lean`.

- Can you write a brute-force function (in Lean) to search solutions?
- Which start configurations are solvable?
- Which start configurations are insolvable?


Frontend:

- Define a way to visualize steps, one at a time, while manually testing the puzzle.
- Make cells in the widget clickable.

Group theory:

- Try to read and understand the lemmas used in `GroupTheory.lean`.
- Try to compute a product of two matrices.



### Birthday problem

- What if there were more days in a year?
- Understand what kind of probability distributions are available for Lean in Mathlib4 (or other projects?).
- Model another similar probabilistic problem / paradox, using another distribution.


### Advanced Lean problems

If you are ready for it, continue with more challenging problems. Use the techniques in the proofs to improve your skills.

- Solutions to recent International Mathematical Olympiad problems: <https://dwrensha.github.io/compfiles/imo.html>
- Have a look at the [100 problems](https://leanprover-community.github.io/100.html). The list is inspired by <https://www.cs.ru.nl/~freek/100/>.

### Unformalised problems

When you have had enough of formalised (in Lean) problems, you can find new problems to formalize and solve in [Project Euler](https://projecteuler.net/) if you want to solve new riddles or problems and compete with others.
