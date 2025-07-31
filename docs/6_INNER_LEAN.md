
## How Lean works

Lean code lives in two "worlds": the world of **syntax** (what you write) and the world of **expressions** (what it means).

### User's world: `Syntax`

When you write code in a `.lean` file, Lean first sees it as just text. Its first job is to parse this text into a structure called `Syntax`. Think of `Syntax` as a blueprint that describes your code's structure—its notations, commands, and layout.

  * **Macros:** Lean is highly customizable. You can define your own notation (like `a ∣ b` for "a divides b") using **macros**. Macros are rules that transform `Syntax` into other `Syntax` before anything else happens. This lets you shape the language to your needs.

### Logic's world: `Expr`

For Lean to understand the *mathematical meaning* of your code, it must leave the world of `Syntax`. It converts your code's blueprint into a core logical object called an `Expr` (short for "Expression").

An `Expr` is the fundamental data structure for everything in Lean's logic:

  * A **term** like `$5$` is an `Expr`.
  * A **type** like `ℕ` (the natural numbers) is an `Expr`.
  * A **theorem statement** like `$2 + 2 = 4$` is an `Expr`.
  * A **proof** of that theorem is also an `Expr`.

So types, proofs and terms are just a special kind of `Expr`.  `Expr` is where Lean performs its magic: type checking, proof verification, and logical computation.


### The bridge: elaboration and the environment

How does `Syntax` become an `Expr`? Through a crucial process called **elaboration**. The elaborator is Lean's "brain." It takes your user-friendly syntax and:

1.  Infers types.
2.  Resolves notation.
3.  Checks for logical correctness.
4.  Translates it all into a well-typed `Expr`.

Once a definition or theorem is successfully elaborated into an `Expr`, it's stored in a global library called the **environment**. When you import `mathlib4`, you are loading its tens of thousands of `Expr`s into this environment, ready for you to use.


### Talking back to you: delaboration

When Lean needs to show you something—like a proof goal or an error message—it does the reverse process. It takes an internal, computer-readable `Expr` and **delaborates** it back into human-readable `Syntax` to display on your screen.

