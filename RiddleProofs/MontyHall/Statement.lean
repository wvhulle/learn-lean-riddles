import Mathlib.Probability.Notation

/-!
# The Monty Hall Problem

This file formalizes the Monty Hall problem, a classic probability puzzle.

**The Problem**

You are a contestant on a game show. You are presented with three closed doors. Behind one door is a car (the prize), and behind the other two are goats.

   ┌───────┐   ┌───────┐   ┌───────┐
   │ Door 1│   │ Door 2│   │ Door 3│
   │  ???  │   │  ???  │   │  ???  │
   └───────┘   └───────┘   └───────┘
      ^           ^           ^
   [Goat/Car]  [Goat/Car]  [Goat/Car]

You complete the following steps:
1. You choose one door.
2. The host, who knows where the car is, opens one of the other two doors to reveal a goat.
3. The host asks if you want to switch your choice to the remaining closed door.

**The Question**

Is it to your advantage to switch doors?

**The Answer (Spoiler)**

Yes! Switching gives you a 2/3 probability of winning, while staying gives you only 1/3.

**Mathematical Intuition**

When you first pick a door, there's a 1/3 chance the car is behind it, and a 2/3 chance 
the car is behind one of the other two doors. When the host opens one of the other doors 
to reveal a goat, all of that 2/3 probability gets concentrated on the remaining door.

**Learning goals for this formalization**

- Learn how to define custom data types in Lean using `inductive`
- Understand how to work with finite types (`Fintype`)
- See how to model discrete probability problems
- Practice working with structures to represent game states
-/

inductive Door : Type
| left    -- Door 1
| middle  -- Door 2  
| right   -- Door 3
deriving DecidableEq, Repr, Fintype

open Door

structure Game where
  car   : Door  -- which door has the car behind it
  pick  : Door  -- which door the contestant initially picks
  host  : Door  -- which door the host opens (must have a goat)
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Door := ⟨Door.left⟩

-- Get the third door (the one that's neither door1 nor door2)
def other_door (door1 door2 : Door) : Door :=
  if door1 = left ∧ door2 = middle then right
  else if door1 = left ∧ door2 = right then middle
  else if door1 = middle ∧ door2 = left then right
  else if door1 = middle ∧ door2 = right then left
  else if door1 = right ∧ door2 = left then middle
  else if door1 = right ∧ door2 = middle then left
  else left  -- fallback case (shouldn't happen in valid games)

example : other_door left middle = right := by rfl
example : other_door left right = middle := by rfl
