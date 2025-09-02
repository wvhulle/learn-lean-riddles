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



-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs

section Statement

variable {m n : ℕ} [NeZero m] [NeZero n]

notation "𝔽₂" => ZMod 2

abbrev Button (m n : ℕ) : Type := Fin m × Fin n

abbrev LightState (m n : ℕ) : Type := Matrix (Fin m) (Fin n) 𝔽₂

def allOff : LightState m n := 0



def areAdjacent (pos1 pos2 : Button m n) : Bool :=
  let (i1, j1) := pos1
  let (i2, j2) := pos2
  (i1 = i2 ∧ Int.natAbs (j1.val - j2.val) = 1) ∨
  (j1 = j2 ∧ Int.natAbs (i1.val - i2.val) = 1)


def isAffected (button pos : Button m n) : Bool :=
  button = pos ∨ areAdjacent button pos

def effect (button : Button m n) : LightState m n :=
  Matrix.of fun i j => if isAffected button (i, j) then 1 else 0

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


def toVector (state : LightState m n) : Button m n → ZMod 2 :=
  Function.uncurry state

def fromVector (v : Button m n → ZMod 2) : LightState m n :=
  Function.curry v

def buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (effect btn) pos

def ButtonSelection (m n : ℕ) := Button m n → ZMod 2


def applySelection (initial : LightState m n) (selection : ButtonSelection m n) : LightState m n :=
  initial + fromVector (buttonMatrix.mulVec selection)

def isSolvable (initial : LightState m n) : Prop :=
  ∃ selection : ButtonSelection m n, applySelection initial selection = allOff

end Statement



/-!
## Computational verification
-/



instance [Fintype (Fin m)] [Fintype (Fin n)] :
    DecidablePred (isSolvable : LightState m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype



section ButtonProperties

theorem press_involution (button : Button m n) (state : LightState m n) :
  press (press state button) button = state := by
  funext i j
  have h : effect button i j + effect button i j = 0 := by
    rw [← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]
  calc press (press state button) button i j
    = state i j + effect button i j + effect button i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]
    _ = state i j + (effect button i j + effect button i j) := by rw [add_assoc]
    _ = state i j + 0 := by rw [h]
    _ = state i j := add_zero _

theorem press_commute (button₁ button₂ : Button m n) (state : LightState m n) :
  press (press state button₁) button₂ = press (press state button₂) button₁ := by
  funext i j
  simp only [press, Matrix.add_apply]
  ring

end ButtonProperties
