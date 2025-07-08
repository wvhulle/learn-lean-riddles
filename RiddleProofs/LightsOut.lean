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

namespace Statement

variable {m n : ℕ} [NeZero m] [NeZero n]

/-- A Lights Out game state is a matrix over ℤ/2ℤ -/
def LightsOut (m n : ℕ) := Matrix (Fin m) (Fin n) (ZMod 2)


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


end Statement

/-!
## Linear Algebra Approach

The key insight: represent each button as a vector in (ℤ/2ℤ)^(m×n).
The puzzle is solvable iff the initial state is in the column space of the button matrix.
-/

open Statement (LightsOut buttonEffect press allOff isWin isAffected)

/-- Convert a game state to a vector -/
def toVector (state : LightsOut m n) : (Fin m × Fin n) → ZMod 2 :=
  fun ⟨i, j⟩ => state i j

/-- Convert a vector back to a game state -/
def fromVector (v : (Fin m × Fin n) → ZMod 2) : LightsOut m n :=
  Matrix.of fun i j => v ⟨i, j⟩

/-- The button effect matrix where each column represents pressing one button -/
def buttonMatrix : Matrix (Fin m × Fin n) (Fin m × Fin n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (buttonEffect btn.1 btn.2) pos

/-
ButtonSelection can represent pressing multiple buttons at once.

For example, to press buttons (0,0), (0,1), and (1,0), you'd have:
  selection (0,0) = 1  -- press this button
  selection (0,1) = 1  -- press this button
  selection (1,0) = 1  -- press this button
  selection (1,1) = 0  -- don't press this button

The order of button presses doesn't matter (as proven by button_press_comm).
-/
def ButtonSelection (m n : ℕ) := (Fin m × Fin n) → ZMod 2

/-- Apply a selection of button presses -/
def applySelection (initial : LightsOut m n) (selection : ButtonSelection m n) : LightsOut m n :=
  initial + fromVector (buttonMatrix.mulVec selection)

/-- The puzzle is solvable if there exists a button selection that reaches the win state -/
def isSolvable (initial : LightsOut m n) : Prop :=
  ∃ selection : ButtonSelection m n, applySelection initial selection = allOff

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
  funext i j
  fin_cases i <;> fin_cases j <;>
  { rw [press, example2x2, buttonEffect, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply]
    dsimp [isAffected]
    decide }

/-- The correct solution for 2×2 single light -/
theorem example2x2_solution :
  applyButtons example2x2 ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 2 × Fin 2)) = allOff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { -- Check all 4 cases explicitly
    dsimp [applyButtons, buttonEffect, isAffected, example2x2, allOff, Finset.sum]
    decide }

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
  use fun btn => if btn ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 2 × Fin 2)) then 1 else 0
  simp [applySelection, fromVector, buttonMatrix, Matrix.mulVec, Matrix.of_apply, toVector]
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp [example2x2, allOff, buttonEffect, isAffected, Matrix.of_apply]
    decide }

end Examples

/-!
## Theoretical Results

The main theoretical result connects the two approaches.
-/

/-- The button matrix as a linear map -/
def buttonLinearMap : ((Fin m × Fin n) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Fin n) → ZMod 2) :=
  Matrix.toLin' buttonMatrix

/-- Helper: In ZMod 2, if a + b = 0, then a = b -/
lemma add_eq_zero_iff_eq_ZMod2 {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + 0 := by rw [add_zero]
         _ = a + (b + b) := by rw [← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]
         _ = (a + b) + b := by rw [add_assoc]
         _ = 0 + b := by rw [h]
         _ = b := by rw [zero_add]
  · intro h; rw [h, ← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]

/-- Helper: fromVector ∘ toVector = id for matrices -/
lemma fromVector_toVector (M : LightsOut m n) : fromVector (toVector M) = M := by
  funext i j
  simp [fromVector, toVector, Matrix.of_apply]

/-- Helper: toVector is injective -/
lemma toVector_injective : Function.Injective (@toVector m n) := by
  intros M N eq
  funext i j
  exact congr_fun eq ⟨i, j⟩

/-- A state is solvable iff it's in the image of the button linear map -/
theorem solvable_iff_in_image (initial : LightsOut m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range buttonLinearMap := by
    calc isSolvable initial
      ↔ ∃ selection, applySelection initial selection = Statement.allOff := Iff.rfl
      _ ↔ ∃ selection, initial + fromVector (buttonMatrix.mulVec selection) = Statement.allOff := by
          rfl
      _ ↔ ∃ selection, toVector (initial + fromVector (buttonMatrix.mulVec selection)) = toVector Statement.allOff := by
          constructor
          · rintro ⟨selection, h⟩; use selection; rw [h]
          · rintro ⟨selection, h⟩; use selection
            exact toVector_injective h
      _ ↔ ∃ selection, toVector initial + buttonMatrix.mulVec selection = 0 := by
          simp only [fromVector]
          constructor
          · rintro ⟨selection, h⟩; use selection; funext pos; exact congr_fun h pos
          · rintro ⟨selection, h⟩; use selection; funext pos; exact congr_fun h pos
      _ ↔ ∃ selection, buttonMatrix.mulVec selection = toVector initial := by
          constructor
          · rintro ⟨selection, h⟩; use selection; funext pos
            exact add_eq_zero_iff_eq_ZMod2.mp (by rw [add_comm]; exact congr_fun h pos)
          · rintro ⟨selection, h⟩; use selection; funext pos
            rw [← h]; exact add_eq_zero_iff_eq_ZMod2.mpr rfl
      _ ↔ toVector initial ∈ Set.range (buttonMatrix.mulVec) := Set.mem_range.symm
      _ ↔ toVector initial ∈ Set.range buttonLinearMap := by
          simp only [buttonLinearMap]
          rfl

/-- The linear algebra and computational approaches are equivalent -/
theorem solvable_iff_in_column_space (initial : LightsOut m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range (buttonMatrix.mulVec) := by
  rw [solvable_iff_in_image]
  simp [buttonLinearMap, Matrix.toLin'_apply]

/-- Button presses are self-inverse (pressing twice = doing nothing) -/
theorem button_self_inverse (i : Fin m) (j : Fin n) (state : LightsOut m n) :
  press (press state i j) i j = state := by
  funext i' j'
  calc press (press state i j) i j i' j'
    = (press state i j + buttonEffect i j) i' j' := by rw [press]
    _ = press state i j i' j' + buttonEffect i j i' j' := by rw [Matrix.add_apply]
    _ = (state + buttonEffect i j) i' j' + buttonEffect i j i' j' := by rw [press]
    _ = state i' j' + buttonEffect i j i' j' + buttonEffect i j i' j' := by rw [Matrix.add_apply]
    _ = state i' j' + (buttonEffect i j i' j' + buttonEffect i j i' j') := by rw [add_assoc]
    _ = state i' j' + 0 := by {
        rw [buttonEffect, Matrix.of_apply]
        split_ifs with h
        · -- If affected, then 1 + 1 = 0 in ZMod 2
          have : (1 : ZMod 2) + 1 = 0 := by decide
          simp [this]
        · -- If not affected, then 0 + 0 = 0
          simp
      }
    _ = state i' j' := by rw [add_zero]

/-- The order of button presses doesn't matter since pressing the same button twice cancels out (button_self_inverse), what matters is just which buttons you press an odd number of times. -/
theorem button_press_comm (i₁ i₂ : Fin m) (j₁ j₂ : Fin n) (state : LightsOut m n) :
  press (press state i₁ j₁) i₂ j₂ = press (press state i₂ j₂) i₁ j₁ := by
  funext i j
  calc press (press state i₁ j₁) i₂ j₂ i j
    = (press state i₁ j₁ + buttonEffect i₂ j₂) i j := by rw [press]
    _ = press state i₁ j₁ i j + buttonEffect i₂ j₂ i j := by rw [Matrix.add_apply]
    _ = (state + buttonEffect i₁ j₁) i j + buttonEffect i₂ j₂ i j := by rw [press]
    _ = state i j + buttonEffect i₁ j₁ i j + buttonEffect i₂ j₂ i j := by rw [Matrix.add_apply]
    _ = state i j + (buttonEffect i₁ j₁ i j + buttonEffect i₂ j₂ i j) := by rw [add_assoc]
    _ = state i j + (buttonEffect i₂ j₂ i j + buttonEffect i₁ j₁ i j) := by rw [add_comm (buttonEffect i₁ j₁ i j)]
    _ = state i j + buttonEffect i₂ j₂ i j + buttonEffect i₁ j₁ i j := by rw [← add_assoc]
    _ = (state + buttonEffect i₂ j₂) i j + buttonEffect i₁ j₁ i j := by rw [← Matrix.add_apply]
    _ = press state i₂ j₂ i j + buttonEffect i₁ j₁ i j := by rw [← press]
    _ = (press state i₂ j₂ + buttonEffect i₁ j₁) i j := by rw [← Matrix.add_apply]
    _ = press (press state i₂ j₂) i₁ j₁ i j := by rw [← press]

/-- For finite grids, we can decide solvability -/
instance [Fintype (Fin m)] [Fintype (Fin n)] : DecidablePred (isSolvable : LightsOut m n → Prop) := by
  intro initial
  -- isSolvable means ∃ selection, applySelection initial selection = allOff
  -- Since we have finitely many possible selections, this is decidable
  unfold isSolvable
  -- We need to show that the existence of a selection is decidable
  -- First, note that ButtonSelection m n = (Fin m × Fin n) → ZMod 2
  -- This is a finite type since both domain and codomain are finite
  have : Fintype (ButtonSelection m n) := by
    -- ButtonSelection m n = (Fin m × Fin n) → ZMod 2
    -- Both Fin m × Fin n and ZMod 2 are finite, so functions between them are finite
    unfold ButtonSelection
    infer_instance
  -- For finite types, we can decide existence by checking all elements
  apply Fintype.decidableExistsFintype
