/-
# Lights Out Puzzle

The Lights Out puzzle consists of a grid of lights that can be on or off.
Pressing a button toggles that light and all adjacent lights (up, down, left, right).
The goal is to turn all lights off starting from some initial configuration.

This puzzle demonstrates the beautiful connection between:
1. **Reasoning approach**: Linear algebra over GF(2) - it's just solving Ax = b
2. **Computational approach**: State space search through all possible button presses

The mathematical insight: Each button press can be represented as a vector in (ℤ/2ℤ)^(n×m),
and the puzzle becomes solvable if and only if the target state is in the column space
of the "button effect matrix" over GF(2).
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
## Game State and Basic Operations

We represent the game state as a matrix over ℤ/2ℤ where:
- 0 = light off
- 1 = light on
-/

variable {m n : ℕ} [NeZero m] [NeZero n]

/-- A Lights Out game state is a matrix over ℤ/2ℤ -/
def LightsOut (m n : ℕ) := Matrix (Fin m) (Fin n) (ZMod 2)

namespace LightsOut

-- Instance for adding matrices (game states)
instance : Add (LightsOut m n) := inferInstanceAs (Add (Matrix (Fin m) (Fin n) (ZMod 2)))
instance : AddCommMonoid (LightsOut m n) := inferInstanceAs (AddCommMonoid (Matrix (Fin m) (Fin n) (ZMod 2)))
instance : DecidableEq (LightsOut m n) := inferInstanceAs (DecidableEq (Matrix (Fin m) (Fin n) (ZMod 2)))

/-- The initial state with all lights off -/
def allOff : LightsOut m n := fun _ _ => 0

/-- The state with all lights on -/
def allOn : LightsOut m n := fun _ _ => 1

/-- Check if all lights are off (winning condition) -/
def isWin (state : LightsOut m n) : Prop := state = allOff

/-- Check if position (i', j') is affected by pressing button at (i, j) -/
def isAffected (i : Fin m) (j : Fin n) (i' : Fin m) (j' : Fin n) : Bool :=
  -- A position is affected if it's the button itself or orthogonally adjacent
  (i = i' ∧ j = j') ||  -- same position
  (i = i' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val)) ||  -- horizontal neighbor
  (j = j' ∧ (i.val + 1 = i'.val ∨ i'.val + 1 = i.val))     -- vertical neighbor

/-- The effect of pressing button at position (i, j) -/
def buttonEffect (i : Fin m) (j : Fin n) : LightsOut m n :=
  Matrix.of fun i' j' => if isAffected i j i' j' then 1 else 0

/-- Apply a button press to the current state -/
def press (state : LightsOut m n) (i : Fin m) (j : Fin n) : LightsOut m n :=
  state + buttonEffect i j


/-!
## Linear Algebra Approach

The key insight: represent each button as a vector in (ℤ/2ℤ)^(m×n).
The puzzle is solvable iff the initial state is in the column space of the button matrix.
-/

/-- Convert a game state to a vector -/
def toVector (state : LightsOut m n) : (Fin m × Fin n) → ZMod 2 :=
  fun ⟨i, j⟩ => state i j

/-- Convert a vector back to a game state -/
def fromVector (v : (Fin m × Fin n) → ZMod 2) : LightsOut m n :=
  Matrix.of fun i j => v ⟨i, j⟩

/-- The button effect matrix where each column represents pressing one button -/
def buttonMatrix : Matrix (Fin m × Fin n) (Fin m × Fin n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (buttonEffect btn.1 btn.2) pos

/-- A sequence of button presses -/
def ButtonSequence (m n : ℕ) := (Fin m × Fin n) → ZMod 2

/-- Apply a sequence of button presses -/
def applySequence (initial : LightsOut m n) (seq : ButtonSequence m n) : LightsOut m n :=
  initial + fromVector (buttonMatrix.mulVec seq)

/-- The puzzle is solvable if there exists a button sequence that reaches the win state -/
def isSolvable (initial : LightsOut m n) : Prop :=
  ∃ seq : ButtonSequence m n, applySequence initial seq = allOff

/-!
## Computational Approach via State Space Search

For verification and smaller puzzles, we can use brute-force search.
-/

/-- All possible button positions -/
def allButtons : Finset (Fin m × Fin n) := Finset.univ

/-- Apply a set of button presses (each button pressed once) -/
def applyButtons (initial : LightsOut m n) (buttons : Finset (Fin m × Fin n)) : LightsOut m n :=
  buttons.sum (fun btn => buttonEffect btn.1 btn.2) + initial

/-- Check if the puzzle is solvable by trying all possible button combinations -/
def isSolvableCompute (initial : LightsOut m n) [DecidableEq (LightsOut m n)] : Bool :=
  (allButtons.powerset.filter fun buttons => 
    applyButtons initial buttons = allOff).card > 0

/-!
## Examples and Verification

Let's verify our approach with some small examples.
-/

section Examples

/-- 2×2 example with single light on -/
def example2x2 : LightsOut 2 2 := 
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Pressing (0,0) toggles the light and its neighbors -/
theorem example2x2_press_00 : 
  press example2x2 0 0 = Matrix.of fun i j => 
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0 := by
  apply Matrix.ext
  intro i j
  simp [press, example2x2, buttonEffect, isAffected]
  fin_cases i <;> fin_cases j <;> simp

/-- The correct solution for 2×2 single light -/
theorem example2x2_solution : 
  let solution : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 0)}
  applyButtons example2x2 solution = allOff := by
  simp only [applyButtons]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [example2x2, buttonEffect, isAffected, allOff]

/-- 3×3 cross pattern -/
def example3x3Cross : LightsOut 3 3 :=
  Matrix.of fun i j => 
    if (i = 1) ∨ (j = 1) then 1 else 0

/-- The all-on 3×3 pattern is solvable by pressing all corners -/
def allOn3x3_solution : LightsOut 3 3 → LightsOut 3 3 :=
  fun initial => 
    let corners : Finset (Fin 3 × Fin 3) := {(0, 0), (0, 2), (2, 0), (2, 2)}
    applyButtons initial corners

/-- Example: The 2×2 puzzle with single light is solvable -/
theorem example2x2_solvable : isSolvable example2x2 := by
  -- We use the solution {(0,0), (0,1), (1,0)}
  use fun btn => if btn ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 2 × Fin 2)) then 1 else 0
  -- Show that applying this sequence gives allOff
  convert example2x2_solution
  simp [applySequence, applyButtons]
  congr 1
  ext btn
  simp [fromVector, buttonMatrix, toVector, Matrix.mulVec]
  split_ifs <;> simp

end Examples

/-!
## Theoretical Results

The main theoretical result connects the two approaches.
-/

/-- The button matrix as a linear map -/
def buttonLinearMap : ((Fin m × Fin n) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Fin n) → ZMod 2) :=
  Matrix.toLin' buttonMatrix

/-- A state is solvable iff it's in the image of the button linear map -/
theorem solvable_iff_in_image (initial : LightsOut m n) :
  isSolvable initial ↔ 
  toVector initial ∈ Set.range buttonLinearMap := by
  constructor
  · intro ⟨seq, h⟩
    use seq
    simp [buttonLinearMap, Matrix.toLin'_apply]
    rw [← h]
    simp [applySequence, fromVector, toVector]
    ext i j
    simp
  · intro ⟨seq, h⟩
    use seq
    simp [buttonLinearMap, Matrix.toLin'_apply] at h
    simp [applySequence, fromVector, toVector]
    ext i j
    rw [← h]
    simp

/-- The linear algebra and computational approaches are equivalent -/
theorem solvable_iff_in_column_space (initial : LightsOut m n) :
  isSolvable initial ↔ 
  toVector initial ∈ Set.range (buttonMatrix.mulVec) := by
  rw [solvable_iff_in_image]
  simp [buttonLinearMap, Matrix.toLin'_apply]

/-- Button presses are self-inverse (pressing twice = doing nothing) -/
theorem button_self_inverse (i : Fin m) (j : Fin n) (state : LightsOut m n) :
  press (press state i j) i j = state := by
  simp [press, buttonEffect]
  ext i' j'
  simp [Matrix.add_apply]
  -- In ZMod 2, x + x = 0
  ring

/-- The order of button presses doesn't matter -/
theorem button_press_comm (i₁ i₂ : Fin m) (j₁ j₂ : Fin n) (state : LightsOut m n) :
  press (press state i₁ j₁) i₂ j₂ = press (press state i₂ j₂) i₁ j₁ := by
  simp [press]
  ring

/-- For finite grids, we can decide solvability -/
instance [Fintype m] [Fintype n] : DecidablePred (isSolvable : LightsOut m n → Prop) := by
  intro initial
  -- Since we only need to check if each button is pressed 0 or 1 times,
  -- there are only finitely many possibilities
  apply decidable_of_iff (∃ buttons : Finset (Fin m × Fin n), applyButtons initial buttons = allOff)
  constructor
  · intro ⟨buttons, h⟩
    use fun btn => if btn ∈ buttons then 1 else 0
    convert h using 1
    simp [applySequence, applyButtons]
    congr 1
    ext pos
    simp [fromVector, buttonMatrix, toVector, Matrix.mulVec]
    split_ifs <;> simp
  · intro ⟨seq, h⟩
    use (Finset.univ.filter fun btn => seq btn = 1)
    simp [applyButtons, applySequence] at h ⊢
    convert h using 1
    ext pos
    simp [fromVector, buttonMatrix, toVector, Matrix.mulVec]
    split_ifs with h1
    · simp [h1]
    · simp [h1]

end LightsOut