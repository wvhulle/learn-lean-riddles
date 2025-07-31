# Lean for dummies

**Lean is a functional programming language and theorem prover. It is used to write formal proofs in mathematics, computer science, and other fields.**

A simple example of the syntax of Lean is:

```lean4
theorem Nat.exists_infinite_primes (n : ℕ) :
∃ (p : ℕ), n ≤ p ∧ Prime p
```

## Why Lean?

Lean is flexible:

- Advanced **programming language**
  - Monads: containers for stuff that needs context
  - Dependent types: e.g. vectors of list N
  - In-place modification compiler optimizations
- Mathematical **theorem prover**
  - Largest database of mathematical theorems: Mathlib
  - Both constructive and classical logic
  - Tactic / meta-programming
  - Supports **concurrent separation logic**: prove correctness of concurrent imperative programs.


Solving internation mathematical olympiad problems is also possible. 

See AlphaProof by Google: https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/

Lean can be used  **verification**:

- Check functioning custom processors.
- Detecting bugs in the Rust standard library.
- Detecting bugs in other systems languages.

## Sysghent


Community for systems programmers around Ghent, Belgium.

- Website: sysghent.be
- Signal group: ask me to get added +32479080252
- MeetUp events: https://www.meetup.com/sysghent/
- Mobilizon


![image:w:20%](img/logo_sysghent.png)


## First steps



Go to https://live.lean-lang.org/.

Click examples and load "Logic".

TODO: prepare some simple logic proofs.

Follow a pre-made tutorial step-by-step: https://adam.math.hhu.de/

## Important intuition

> **Mathematics = Programming**


What does this mean?

- Proving things in mathematics is like writing programs.
- Writing programs is like proving things in mathematics.

How exactly?

- **Propositions are types**.
- **Proofs are programs**.


## Product types

Lean has normal record-like / struct-like data-types:

```lean
structure RGB where
  red : Nat
  green : Nat
  blue : Nat
```

Inheritance / extension is possible with `extends`.

A constructor is written separately:

```lean
def pureGreen : RGB :=
  { red := 0x00
    green := 0xff
    blue := 0x00 }
```

Sometimes, inline, you would write:

```lean
{ red := 0x00, green := 0xff, blue := 0x00 : RGB}
```

## Inductive data-types

The prototype of a recursive data-type is the natural numbers:

```lean
inductive Nat : Type where
| zero : Nat
| succ : Nat → Nat
```

Recursive types in Lean are called inductive data-types. They are a generalization of the natural numbers:

```lean
inductive List (α : Type) : Type where
| nil : List α
| cons : α → List α → List α
```

Notice, this is a generic type.


## Functions

A simple function:

```lean
def shuffle (c : RGB) : RGB :=
  { red := RGB.green c
    green := RGB.blue c
    blue := RGB.red c }
```

Evaluation is not the core purpose of Lean, but it is easy and explicit:

```lean
#eval append N [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]
```


### Termination

By default, functions that start **without `partial` have to be terminating**.

```lean
def append (α : Type) : List α → List α → List α
| List.nil, ys => ys
| List.cons x xs, ys => List.cons x (append α xs ys)
```

Termination checks can be:

- automatically inferred by the compiler
- proven by manually specifying a measure in the definition
- proven by manually proving well-foundedness of recursion

Usually, when you do brute-force search, you do not care about termination (because you know that the computation is unbounded):

```lean
partial def bruteForceSearch (xs : List Nat) : List Nat :=
  match xs with
  | List.nil => List.nil
  | List.cons x xs' => sorry
```


## Definitions vs theorems


Definitions and theorems have almost the same syntax:

A definition (program):

```lean
def add_comm_zero_left (n : Nat) :
  add 0 n = add n 0 :=
  add_comm 0 n
```


As a theorem (proof):

```lean
theorem add_comm_zero_left (n : Nat) :
  add 0 n = add n 0 :=
  add_comm 0 n
```

However, the body of the theorem is not considered relevant (also called proof irrelevance), just the statement is kept.

A `lemma` is identical to a `theorem`, but `lemma` more common for less-important theorems.

## Functional proofs vs tactic proofs

You can prove theorems in Lean using functional style:

```lean
theorem double_add (n : Nat) : n + n = 2 * n :=
  (Nat.two_mul n).symm
```

You can also prove theorems in Lean using tactics (like `intro`, `exact`):

```lean
theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  intro hp
  intro hpq
  apply hpq
  exact hp
``` 

Tactics proofs start with the goal and work backwards. More common in formal mathematics, less common in functional programming.


## Relational proofs

You can use relational reasoning with the `rw` (rewrite), `simp` (simplify) tactics:

```lean
theorem add_assoc_example (a b c : Nat) : 
  (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]
```

The `rw` tactic replaces the left-hand side of the equation from the lemma `Nat.add_assoc` with the right-hand side when the left-hand-side matches.

Relational `calc` style proofs reflect the traditional style of writing proofs:

```lean
theorem calc_example (a b : Nat) : 
  (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  calc (a + b) * (a + b) 
    = a * (a + b) + b * (a + b) := by rw [Nat.add_mul]
    _ = a * a + a * b + b * (a + b) := by sorry
    _ = a * a + 2 * a * b + b * b := by ring
```

You can also use other relations like `<->` or `<`. 



## Finding the right documentation

How to choose?

- You are a **mathematician**? 
  - Start with the interactive tutorial "Mathematics in Lean".
  - Look at "100 theorems in Lean".
  - Look at the Mathlib4 index page.
  - Join the "math" channel on [Lean Zulip chat](https://leanprover.zulipchat.com/).
- You are a **developer**? 
  - Start with "Functional programming Lean"
  - Read the [Lean reference manual](https://lean-lang.org/doc/reference/latest/)
- You are a **language nerd**?
  - [Hitchhiker's Guide to Logical Verification (2023 Edition)](https://lean-forward.github.io/hitchhikers-guide/2023/)
  - Read "Tactic programming guide"
  - Read "Metaprogramming in Lean"
- You are **something else**? Try the interactive "Natural number game" at [Lean games (University Düsseldorf)](https://adam.math.hhu.de/).

Don't forget to set your location on the [Lean community map](https://leanprover-community.github.io/meet.html#community-guidelines). You can find in-person Lean courses and workshops on the [event page](https://leanprover-community.github.io/events.html).



