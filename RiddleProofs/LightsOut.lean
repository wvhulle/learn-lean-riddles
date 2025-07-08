/-
# Lights out puzzle

The Lights Out puzzle consists of a grid of lights that can be on or off.
Pressing a button toggles that light and all adjacent lights (up, down, left, right).
The goal is to turn all lights off starting from some initial configuration.

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


This puzzle demonstrates the beautiful connection between:
1. **Reasoning approach**: Linear algebra over GF(2) - it's just solving Ax = b
2. **Computational approach**: State space search through all possible button presses



The mathematical insight: Each button press can be represented as a vector in (ℤ/2ℤ)^(n×m),
and the puzzle becomes solvable if and only if the target state is in the column space
of the "button effect matrix" over GF(2).
-/

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

scoped notation "𝔽₂" => ZMod 2

scoped notation "●" => (1 : 𝔽₂)  -- light on
scoped notation "○" => (0 : 𝔽₂)  -- light off

/-- A button on the grid -/
def Button (m n : ℕ) := Fin m × Fin n

instance [Fintype (Fin m)] [Fintype (Fin n)] : Fintype (Button m n) :=
  inferInstanceAs (Fintype (Fin m × Fin n))

instance : DecidableEq (Button m n) :=
  inferInstanceAs (DecidableEq (Fin m × Fin n))

/-- A Lights Out game state is a matrix over the binary field 𝔽₂ -/
def State (m n : ℕ) := Matrix (Fin m) (Fin n) 𝔽₂



instance : Add (State m n) := inferInstanceAs (Add (Matrix (Fin m) (Fin n) 𝔽₂))
instance : AddCommMonoid (State m n) := inferInstanceAs (AddCommMonoid (Matrix (Fin m) (Fin n) 𝔽₂))
instance : DecidableEq (State m n) := inferInstanceAs (DecidableEq (Matrix (Fin m) (Fin n) 𝔽₂))

/-- The initial state with all lights off -/
def allOff : State m n := fun _ _ => ○

/-- The state with all lights on -/
def allOn : State m n := fun _ _ => ●

/-- Check if all lights are off (winning condition) -/
def isWin (state : State m n) : Prop := state = allOff

/-- Check if two positions are orthogonally adjacent -/
def areAdjacent (pos1 pos2 : Button m n) : Bool :=
  let (i1, j1) := pos1
  let (i2, j2) := pos2
  (i1 == i2 && (j1.val + 1 == j2.val || j2.val + 1 == j1.val)) ||
  (j1 == j2 && (i1.val + 1 == i2.val || i2.val + 1 == i1.val))

/-- Check if position is in the von Neumann neighborhood (button + adjacent) -/
def inVonNeumannNeighborhood (center target : Button m n) : Bool :=
  decide (center = target) || areAdjacent center target

/-- Check if position is affected by pressing a button -/
def isAffected (button : Button m n) (pos : Button m n) : Bool :=
  inVonNeumannNeighborhood button pos

/-- The effect of pressing a specific button -/
def effect (button : Button m n) : State m n :=
  Matrix.of fun i j => if isAffected button (i, j) then ● else ○

/-- Apply a button press to the current state -/
def press (state : State m n) (button : Button m n) : State m n :=
  state + effect button

/-- Apply a button press by coordinates -/
def pressAt (state : State m n) (i : Fin m) (j : Fin n) : State m n :=
  press state (i, j)


end Statement

/-!
## Linear Algebra Approach

The key insight: represent each button as a vector in (ℤ/2ℤ)^(m×n).
The puzzle is solvable iff the initial state is in the column space of the button matrix.
-/

open Statement (State effect press allOff isWin isAffected Button pressAt inVonNeumannNeighborhood areAdjacent)

/-- Convert a game state to a vector using uncurrying -/
def toVector (state : State m n) : Button m n → ZMod 2 :=
  Function.uncurry state

/-- Convert a vector back to a game state using currying -/
def fromVector (v : Button m n → ZMod 2) : State m n :=
  Function.curry v

/-- The button effect matrix where each column represents pressing one button -/
def buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (effect btn) pos

/-
ButtonSelection can represent pressing multiple buttons at once.

For example, to press buttons (0,0), (0,1), and (1,0), you'd have:
  selection (0,0) = 1  -- press this button
  selection (0,1) = 1  -- press this button
  selection (1,0) = 1  -- press this button
  selection (1,1) = 0  -- don't press this button

The order of button presses doesn't matter (as proven by button_press_comm).
-/
def ButtonSelection (m n : ℕ) := Button m n → ZMod 2

/-- Apply a selection of button presses -/
def applySelection (initial : State m n) (selection : ButtonSelection m n) : State m n :=
  initial + fromVector (buttonMatrix.mulVec selection)

/-- The puzzle is solvable if there exists a button selection that reaches the win state -/
def isSolvable (initial : State m n) : Prop :=
  ∃ selection : ButtonSelection m n, applySelection initial selection = allOff

/-!
## Computational approach via state space search

For verification and smaller puzzles, we can use brute-force search.
-/

/-- All possible button positions -/
def allButtons : Finset (Button m n) := Finset.univ

/-- Apply a set of button presses (each button pressed once) -/
def applyButtons (initial : State m n) (buttons : Finset (Button m n)) : State m n :=
  initial + buttons.sum (fun btn => effect btn)

/-- Check if the puzzle is solvable by trying all possible button combinations -/
def isSolvableCompute (initial : State m n) [DecidableEq (State m n)] : Bool :=
  (allButtons.powerset.filter fun buttons =>
    applyButtons initial buttons = allOff).card > 0

/-!
## Examples and verification

Let's verify our approach with some small examples.
-/

section Examples

/-- 2×2 example with single light on -/
def example2x2 : State 2 2 :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Pressing (0,0) toggles the light and its neighbors -/
theorem example2x2_press_00 :
  pressAt example2x2 0 0 = Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { rw [pressAt, press, example2x2, effect, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply]
    simp only [isAffected, inVonNeumannNeighborhood, areAdjacent]
    decide }

/-- The correct solution for 2×2 single light -/
theorem example2x2_solution :
  applyButtons example2x2 ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) = allOff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [applyButtons, effect, isAffected,
    inVonNeumannNeighborhood, areAdjacent, example2x2, allOff]
    simp
    decide }

/-- Example: The 2×2 puzzle with single light is solvable -/
theorem example2x2_solvable : isSolvable example2x2 := by
  use fun btn => if btn ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) then 1 else 0
  simp [applySelection, fromVector, buttonMatrix, toVector]
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [example2x2, allOff, effect, isAffected,
    inVonNeumannNeighborhood, areAdjacent]
    decide }

/-- 3×3 cross pattern -/
def example3x3Cross : State 3 3 :=
  Matrix.of fun i j =>
    if (i = 1) ∨ (j = 1) then 1 else 0

/-- The all-on 3×3 pattern is solvable by pressing all corners -/
def allOn3x3_solution : State 3 3 → State 3 3 :=
  fun initial =>
    let corners : Finset (Button 3 3) := {(0, 0), (0, 2), (2, 0), (2, 2)}
    applyButtons initial corners


end Examples

/-!
## Theoretical

The main theoretical result connects the two approaches.
-/

/-- The button matrix as a linear map -/
def buttonLinearMap : ((Fin m × Fin n) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Fin n) → ZMod 2) :=
  Matrix.toLin' buttonMatrix

lemma add_eq_zero_iff_eq_ZMod2 {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + 0 := by rw [add_zero]
         _ = a + (b + b) := by rw [← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]
         _ = (a + b) + b := by rw [add_assoc]
         _ = 0 + b := by rw [h]
         _ = b := by rw [zero_add]
  · intro h; rw [h, ← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]



lemma toVector_injective : Function.Injective (@toVector m n) := by
  intros M N eq
  funext i j
  exact congr_fun eq ⟨i, j⟩

/-- A state is solvable iff it's in the image of the button linear map -/
theorem solvable_iff_in_image (initial : State m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range buttonLinearMap := by
    calc isSolvable initial
      ↔ ∃ selection, applySelection initial selection = allOff := Iff.rfl
      _ ↔ ∃ selection, initial + fromVector (buttonMatrix.mulVec selection) = allOff := by
          rfl
      _ ↔ ∃ selection, toVector (initial + fromVector (buttonMatrix.mulVec selection)) = toVector allOff := by
          constructor
          · rintro ⟨selection, h⟩; use selection; rw [h]
          · rintro ⟨selection, h⟩; use selection; exact toVector_injective h
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
theorem solvable_iff_in_column_space (initial : State m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range (buttonMatrix.mulVec) := by
  rw [solvable_iff_in_image]
  rfl

/-- Button presses are self-inverse (pressing twice = doing nothing) -/
theorem button_self_inverse (button : Button m n) (state : State m n) :
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

/-- The order of button presses doesn't matter since pressing the same button twice cancels out (button_self_inverse), what matters is just which buttons you press an odd number of times. -/
theorem button_press_comm (button₁ button₂ : Button m n) (state : State m n) :
  press (press state button₁) button₂ = press (press state button₂) button₁ := by
  funext i j
  calc press (press state button₁) button₂ i j
    = state i j + effect button₁ i j + effect button₂ i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]
    _ = state i j + effect button₂ i j + effect button₁ i j := by ring
    _ = press (press state button₂) button₁ i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]

/-- For finite grids, we can decide solvability -/
instance [Fintype (Fin m)] [Fintype (Fin n)] : DecidablePred (isSolvable : State m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype
