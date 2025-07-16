/-
# Lights Out Puzzle

The Lights Out puzzle is a finite state automaton on an m×n grid where each cell
has binary state (on/off). Pressing a button toggles itself and its von Neumann
neighborhood (orthogonally adjacent cells).

   ┌───┬───┬───┬───┬───┐
   │ ● │ ○ │ ● │ ○ │ ● │
   ├───┼───┼───┼───┼───┤
   │ ○ │ ● │ ○ │ ● │ ○ │
   ├───┼───┼───┼───┼───┤
   │ ● │ ○ │ ● │ ○ │ ● │
   ├───┼───┼───┼───┼───┤
   │ ○ │ ● │ ○ │ ● │ ○ │
   ├───┼───┼───┼───┼───┤
   │ ● │ ○ │ ● │ ○ │ ● │
   └───┴───┴───┴───┴───┘

  Example: 5×5 Lights Out grid. ● = on, ○ = off

## Goal

Turn all lights off by pressing buttons according to the rules.


## Challenges

- Can you write a brute-force function (in Lean) to search solutions?
- Which start configurations are solvable?
- Which start configurations are insolvable?


Frontend:

- Define a way to visualize steps, one at a time, while manually testing the puzzle.
- Make cells in the widget clickable.

Group theory:

- Try to read and understand the lemmas used in `GroupTheory.lean`.
- Try to compute a product of two matrices.

-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs



variable {m n : ℕ} [NeZero m] [NeZero n]

-- 𝔽₂ is mathematical notation for "the field with 2 elements" = {0, 1}
-- In Lean, this is represented as ZMod 2 (integers modulo 2)
notation "𝔽₂" => ZMod 2

def Button (m n : ℕ) := Fin m × Fin n

instance [Fintype (Fin m)] [Fintype (Fin n)] : Fintype (Button m n) :=
  inferInstanceAs (Fintype (Fin m × Fin n))

instance : DecidableEq (Button m n) :=
  inferInstanceAs (DecidableEq (Fin m × Fin n))

def LightState (m n : ℕ) := Matrix (Fin m) (Fin n) 𝔽₂

instance : Add (LightState m n) := inferInstanceAs (Add (Matrix (Fin m) (Fin n) 𝔽₂))
instance : AddCommMonoid (LightState m n) :=
  inferInstanceAs (AddCommMonoid (Matrix (Fin m) (Fin n) 𝔽₂))
instance : DecidableEq (LightState m n) := inferInstanceAs (DecidableEq (Matrix (Fin m) (Fin n) 𝔽₂))

def allOff : LightState m n := fun _ _ => 0

def isWin (state : LightState m n) : Prop := state = allOff

-- Check if two positions are adjacent (Manhattan distance = 1)
def areAdjacent (pos1 pos2 : Button m n) : Bool :=
  let (i1, j1) := pos1
  let (i2, j2) := pos2
  (i1 = i2 ∧ Int.natAbs (j1.val - j2.val) = 1) ∨
  (j1 = j2 ∧ Int.natAbs (i1.val - i2.val) = 1)

-- Von Neumann neighborhood: button affects itself and orthogonally adjacent cells
def isAffected (button : Button m n) (pos : Button m n) : Bool :=
  decide (button = pos) || areAdjacent button pos

def effect (button : Button m n) : LightState m n :=
  Matrix.of fun i j => if isAffected button (i, j) then 1 else 0

-- In 𝔽₂, addition is the same as XOR (exclusive or)
def press (state : LightState m n) (button : Button m n) : LightState m n :=
  state + effect button

def pressAt (state : LightState m n) (i : Fin m) (j : Fin n) : LightState m n :=
  press state (i, j)




/-!
## Linear algebraic formulation

**Key idea**: Instead of thinking about the puzzle as a game, we can think of it as
a linear algebra problem! Each button press is a linear transformation, and we want
to find a combination of button presses that transforms our initial state to the
all-off state.

This is much more efficient than trying all possible button combinations.
-/


-- Convert a matrix state to a vector (flattens the 2D grid into a 1D vector)
def toVector (state : LightState m n) : Button m n → ZMod 2 :=
  Function.uncurry state

def fromVector (v : Button m n → ZMod 2) : LightState m n :=
  Function.curry v

-- Button effect matrix A where Ae_i = effect of pressing button i
def buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (effect btn) pos

def ButtonSelection (m n : ℕ) := Button m n → ZMod 2

def applySelection (initial : LightState m n) (selection : ButtonSelection m n) : LightState m n :=
  initial + fromVector (buttonMatrix.mulVec selection)

-- A puzzle is solvable if there exists some selection of buttons that
-- transforms the initial state to the all-off state
def isSolvable (initial : LightState m n) : Prop :=
  ∃ selection : ButtonSelection m n, applySelection initial selection = allOff



/-!
## Computational verification
-/

/-- Apply button set (exploiting idempotence) -/
def applyButtons (initial : LightState m n) (buttons : Finset (Button m n)) : LightState m n :=
  initial + buttons.sum (fun btn => effect btn)

/-- Brute-force solvability check -/
def isSolvableCompute (initial : LightState m n) [DecidableEq (LightState m n)] : Bool :=
  (Finset.univ.powerset.filter fun buttons =>
    applyButtons initial buttons = allOff).card > 0
