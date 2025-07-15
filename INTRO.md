---
title: "Introduction to Lean"
sub_title: (language and proof assistant)
date: 2025-07-17
author: Willem Vanhulle
options:
  end_slide_shorthand: true
  incremental_lists: true
theme:
  name: light
---

# Sysghent

Community for systems programmers.

![image:w:20%](img/logo_sysghent.png)

Today: **Learn lean with riddles**.

Past events:

- Social and embedded Rust workshop in June.
- Functional programming presentations in April.
- ...

---

# Photos

Built your own smart plant pot with Rust and a Pico.

- Workshop last month on 4th of June 2025
- First workshop with Raspberry Pico and Rust
- Popular, 30 participants, even couples on date

![image:w:90%](img/plant.jpg)

---

# Lean

![image:w:30%](img/logo_lean.png)

What is it?

- An advanced programming language
- Mathematical theorem prover

Try it out without installing online:

> https://live.lean-lang.org/

What does it have to do with systems programming?

- It's parent language Coq has been used to verify systems hardware and software.
- Lean can also be used to write highly correct, safe software.
- Otherwise, it is **mostly just fun!**

---

# Today

Learn Lean using computational problems / riddles.

For example: the Monty Hall problem

![image:w:30%](img/monty_hall.png)

Jealous husbands problem:

![image:w:30%](img/jealous_husbands.jpg)

But first, you need a basic introduction to Lean.

---

# Learning resources Lean

Where should you start?

- Official list: https://leanprover-community.github.io/learn.html
- My notes for this workshop: https://github.com/wvhulle/learn-lean-riddles
  - contains instructions for installation
  - computation problems (riddles), partially or fully solved
  - tips for creating Lean modules

How to choose?

- You are a **mathematician**? Start with "Mathematics in Lean"
- You are a **developer**? Start with "Functional programming Lean"
- You are a **language nerd**? Read "Tactic programming guide"
- You are **something else**? Try the interactive "Natural number game"

---

# Mathematics = Programming

Starting point of this workshop:

- Mathematics = programming
- Programming = mathematics

What does this mean?

- Proving things in mathematics is like writing programs.
- Writing programs is like proving things in mathematics.

Also known as the;

- **Propositions as types**.
- **Proofs as programs**.

Discovered by Brouwer, Heyting, Kolmogorov, Curry, Howard, and many others.


---

# Formally in Lean

Example: **polar coordinates**

- A program that computes polar coordinates from cartesian coordinates = theorem that shows polar coordinates exist, given cartesian coordinates exist.
- A theorem that shows polar coordinates exist for each cartesian coordinate = a program that computes polar coorindates from cartesian coordinates.

A Lean definition of this function:

```lean4
def polar_to_cartesian: Cart -> Pol :=
  sorry
```

This is **exactly the same** as a Lean theorem:

```lean
theorem polar_to_cartesian: Cart -> Pol :=
  sorry
```

(`sorry` is a placeholder for "I don't know how to prove this yet".)

---

# Basic data types

## Inductive data-types

Generalization of natural numbers with induction principle:

```lean
inductive Nat : Type where
| zero : Nat
| succ : Nat → Nat
```

## Structures

Similar to records or objects.

```lean
structure RGB where
  red : N
  green : N
  blue : N
```

Usage with:

```lean
def pureGreen : RGB :=
  { red := 0x00
    green := 0xff
    blue := 0x00 }
```

---

# Functions

- Simple function

```lean
def shuffle (c : RGB) : RGB :=
  { red := RGB.green c
    green := RGB.blue c
    blue := RGB.red c }
```

- Safe recursion with termination

```lean
def append (α : Type) : List α → List α → List α
| List.nil, ys => ys
| List.cons x xs, ys => List.cons x (append α xs ys)
```

- Evaluation (running / execution)

```lean
#eval append N [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]
```

# Theorems

- Forward proofs (functional programming):

```lean
theorem add_comm_zero_left (n : N) :
  add 0 n = add n 0 :=
  add_comm 0 n
```

- Backwards proofs (with tactics):

```lean
theorem And_swap (a b : Prop) :
a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha
```

---

# What's next?

Mathlib4 is the most popular Lean library.

- Contains all of undergraduate mathematics.
- Contains all of graduate mathematics.
- Contains most of research-level mathematics.
- But, **no riddles**!

What about the riddles?

- Mathlib4's section on conditional probability:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ConditionalProbability.html
  Few to no examples.
- 100 examples of famous problems / proofs
  https://leanprover-community.github.io/100.html
  One is the **birthday paradox** and uses a uniform discrete density.

---

# Let's exercise

## Beginner

I recommend to start with one of these:

- In the web browser: play the online "Natural number game" to understand fundamentals.
- Local: follow the "Mathematics in lean" tutorial and practice proving things.

## Advanced



If you are new to proof assistants, but you have written code, you can have a look at the `Statement.lean` files in the repository of this workshop. (Of course, you are free to use other resources, available online.)

For playing with the Lean content in this repository:

- You will need to clone: `git@github.com:wvhulle/learn-lean-riddles.git`.
- Then run `lake build` to build everything. First time can take a while.
- Open the Lean files in VS code with the Lean4 extension.
- Open the infoview and step through proofs interactively.

In the following slides, there is a brief sketch of each riddle / problem.

---

# Jealous husbands

First read `Statement.lean`.

![image:w:30%](img/jealous_husbands.jpg)

- Can you generalize to N couples?
- What about more than 2 people in a boat?
- Can you optimize my BFS in `Search.lean`?
- Like `JealousMathematician.lean`, can you write a version for "cannibals and missionaries"?

---

# Lights out

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

---

# Monty Hall

First look at `Statement.lean`.

![image:w:30%](img/monty_hall.png)

- Derive a statement for the "total probability" law
- Proof the total probability law as a theorem / lemma.
- Replace boilerplate proof code in `Dilemma.lean` by the total probability law.

---

# Birthday problem

- What if there were more days in a year?
- Understand what kind of probability distributions are available for Lean in Mathlib4 (or other projects?).
- Model another similar probabilistic problem / paradox, using another distribution.


---

# Learning resources Lean

Where should you start?

- Official list: https://leanprover-community.github.io/learn.html
- My notes for this workshop: https://github.com/wvhulle/learn-lean-riddles
  - contains instructions for installation
  - computation problems (riddles), partially or fully solved
  - tips for creating Lean modules

How to choose?

- You are a **mathematician**? Start with "Mathematics in Lean"
- You are a **developer**? Start with "Functional programming Lean"
- You are a **language nerd**? Read "Tactic programming guide"
- You are **something else**? Try the interactive "Natural number game"