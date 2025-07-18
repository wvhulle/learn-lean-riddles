import Mathlib.Probability.Notation

/-!
# The Monty Hall Problem

This file formalizes the Monty Hall problem, a classic probability puzzle.

## Statement**

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

## Question

Is it to your advantage to switch doors?

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
