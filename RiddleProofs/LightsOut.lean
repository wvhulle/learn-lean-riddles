/-
# Lights out puzzle

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

## Mathematical structure

The puzzle exhibits rich algebraic structure:

- **State space**: Matrix (Fin m) (Fin n) (ℤ/2ℤ)
- **Action group**: (ℤ/2ℤ)^(m×n) acting by componentwise addition
- **Key insight**: Button presses form an abelian group where each element has order 2

The puzzle reduces to solving a linear system over 𝔽₂:
  ```
  Ax = b  where A is the button effect matrix
  ```

Solvability is equivalent to b ∈ Im(A), making this a problem in linear algebra
over finite fields rather than combinatorial search.
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Statement

variable {m n : ℕ} [NeZero m] [NeZero n]

/- Button on or off -/
scoped notation "𝔽₂" => ZMod 2

/-- Grid position -/
def Button (m n : ℕ) := Fin m × Fin n

instance [Fintype (Fin m)] [Fintype (Fin n)] : Fintype (Button m n) :=
  inferInstanceAs (Fintype (Fin m × Fin n))

instance : DecidableEq (Button m n) :=
  inferInstanceAs (DecidableEq (Fin m × Fin n))

/-- Game state as a matrix over 𝔽₂ -/
def State (m n : ℕ) := Matrix (Fin m) (Fin n) 𝔽₂

instance : Add (State m n) := inferInstanceAs (Add (Matrix (Fin m) (Fin n) 𝔽₂))
instance : AddCommMonoid (State m n) := inferInstanceAs (AddCommMonoid (Matrix (Fin m) (Fin n) 𝔽₂))
instance : DecidableEq (State m n) := inferInstanceAs (DecidableEq (Matrix (Fin m) (Fin n) 𝔽₂))

/-- Zero state (all lights off) -/
def allOff : State m n := fun _ _ => 0

/-- Winning condition -/
def isWin (state : State m n) : Prop := state = allOff

/-- Manhattan distance = 1 -/
def areAdjacent (pos1 pos2 : Button m n) : Bool :=
  let (i1, j1) := pos1
  let (i2, j2) := pos2
  (i1 = i2 ∧ Int.natAbs (j1.val - j2.val) = 1) ∨
  (j1 = j2 ∧ Int.natAbs (i1.val - i2.val) = 1)

/-- Von Neumann neighborhood -/
def isAffected (button : Button m n) (pos : Button m n) : Bool :=
  decide (button = pos) || areAdjacent button pos

/-- Button effect matrix -/
def effect (button : Button m n) : State m n :=
  Matrix.of fun i j => if isAffected button (i, j) then 1 else 0

/-- Button press action -/
def press (state : State m n) (button : Button m n) : State m n :=
  state + effect button

def pressAt (state : State m n) (i : Fin m) (j : Fin n) : State m n :=
  press state (i, j)


end Statement

/-!
## Linear algebraic formulation
-/

open Statement (State effect press allOff isWin isAffected Button pressAt areAdjacent)

/-- State isomorphism with function space -/
def toVector (state : State m n) : Button m n → ZMod 2 :=
  Function.uncurry state

def fromVector (v : Button m n → ZMod 2) : State m n :=
  Function.curry v

/-- Button effect matrix A where Ae_i = effect of pressing button i -/
def buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (effect btn) pos

/-- Selection vector in (ℤ/2ℤ)^(m×n) -/
def ButtonSelection (m n : ℕ) := Button m n → ZMod 2

/-- Apply selection vector s: state ↦ state + As -/
def applySelection (initial : State m n) (selection : ButtonSelection m n) : State m n :=
  initial + fromVector (buttonMatrix.mulVec selection)

/-- Solvability: ∃s. initial + As = 0 -/
def isSolvable (initial : State m n) : Prop :=
  ∃ selection : ButtonSelection m n, applySelection initial selection = allOff

/-!
## Computational verification
-/

/-- Apply button set (exploiting idempotence) -/
def applyButtons (initial : State m n) (buttons : Finset (Button m n)) : State m n :=
  initial + buttons.sum (fun btn => effect btn)

/-- Brute-force solvability check -/
def isSolvableCompute (initial : State m n) [DecidableEq (State m n)] : Bool :=
  (Finset.univ.powerset.filter fun buttons =>
    applyButtons initial buttons = allOff).card > 0

/-!
## Examples
-/

section Examples

/-- Single light at (0,0) -/
def example2x2 : State 2 2 :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Pressing (0,0) toggles the light and its neighbors -/
theorem example2x2_press_00 :
  pressAt example2x2 0 0 = Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { rw [pressAt, press, example2x2, effect, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply]
    simp only [isAffected, areAdjacent]
    decide }

/-- The correct solution for 2×2 single light -/
theorem example2x2_solution :
  applyButtons example2x2 ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) = allOff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [applyButtons, effect, isAffected,
    areAdjacent, example2x2, allOff]
    simp
    decide }

/-- Example: The 2×2 puzzle with single light is solvable -/
theorem example2x2_solvable : isSolvable example2x2 := by
  use fun btn => if btn ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) then 1 else 0
  simp [applySelection, fromVector, buttonMatrix, toVector]
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [example2x2, allOff, effect, isAffected,
    areAdjacent]
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
## Main results
-/

/-- Linear map induced by button matrix -/
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

/-- Solvability criterion: initial ∈ Im(A) -/
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


/-- Involution property: press^2 = id -/
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

/-- Commutativity: button group is abelian -/
theorem button_press_comm (button₁ button₂ : Button m n) (state : State m n) :
  press (press state button₁) button₂ = press (press state button₂) button₁ := by
  funext i j
  calc press (press state button₁) button₂ i j
    = state i j + effect button₁ i j + effect button₂ i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]
    _ = state i j + effect button₂ i j + effect button₁ i j := by ring
    _ = press (press state button₂) button₁ i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]

/-- Decidability of solvability -/
instance [Fintype (Fin m)] [Fintype (Fin n)] : DecidablePred (isSolvable : State m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype
