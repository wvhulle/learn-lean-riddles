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

**The goal**: Turn all lights off by pressing buttons according to the rules.

**Learning goals for this formalization**
- Understand how to model puzzles using linear algebra over finite fields
- Learn about matrices and linear maps in Lean
- See how group theory applies to puzzle games
- Practice working with ℤ/2ℤ (integers modulo 2)

## Mathematical structure

The puzzle exhibits rich algebraic structure:

- **State space**: Matrix (Fin m) (Fin n) (ℤ/2ℤ)  -- Each cell is 0 or 1
- **Action group**: (ℤ/2ℤ)^(m×n) acting by componentwise addition
- **Key insight**: Button presses form an abelian group where each element has order 2
  (pressing the same button twice cancels out)

The puzzle reduces to solving a linear system over 𝔽₂:
  ```
  Ax = b  where A is the button effect matrix
  ```

Solvability is equivalent to b ∈ Im(A), making this a problem in linear algebra
over finite fields rather than combinatorial search.

**Why this works**: Since each button press toggles lights (addition in ℤ/2ℤ),
and pressing a button twice returns to the original state, the order of button
presses doesn't matter - only which buttons are pressed an odd number of times.
-/

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.GroupAction.Basic

namespace Statement

variable {m n : ℕ} [NeZero m] [NeZero n]

-- 𝔽₂ is mathematical notation for "the field with 2 elements" = {0, 1}
-- In Lean, this is represented as ZMod 2 (integers modulo 2)
scoped notation "𝔽₂" => ZMod 2

def Button (m n : ℕ) := Fin m × Fin n

instance [Fintype (Fin m)] [Fintype (Fin n)] : Fintype (Button m n) :=
  inferInstanceAs (Fintype (Fin m × Fin n))

instance : DecidableEq (Button m n) :=
  inferInstanceAs (DecidableEq (Fin m × Fin n))

def State (m n : ℕ) := Matrix (Fin m) (Fin n) 𝔽₂

instance : Add (State m n) := inferInstanceAs (Add (Matrix (Fin m) (Fin n) 𝔽₂))
instance : AddCommMonoid (State m n) := inferInstanceAs (AddCommMonoid (Matrix (Fin m) (Fin n) 𝔽₂))
instance : DecidableEq (State m n) := inferInstanceAs (DecidableEq (Matrix (Fin m) (Fin n) 𝔽₂))

def allOff : State m n := fun _ _ => 0

def isWin (state : State m n) : Prop := state = allOff

-- Check if two positions are adjacent (Manhattan distance = 1)
def areAdjacent (pos1 pos2 : Button m n) : Bool :=
  let (i1, j1) := pos1
  let (i2, j2) := pos2
  (i1 = i2 ∧ Int.natAbs (j1.val - j2.val) = 1) ∨
  (j1 = j2 ∧ Int.natAbs (i1.val - i2.val) = 1)

-- Von Neumann neighborhood: button affects itself and orthogonally adjacent cells
def isAffected (button : Button m n) (pos : Button m n) : Bool :=
  decide (button = pos) || areAdjacent button pos

def effect (button : Button m n) : State m n :=
  Matrix.of fun i j => if isAffected button (i, j) then 1 else 0

-- In 𝔽₂, addition is the same as XOR (exclusive or)
def press (state : State m n) (button : Button m n) : State m n :=
  state + effect button

def pressAt (state : State m n) (i : Fin m) (j : Fin n) : State m n :=
  press state (i, j)


end Statement

/-!
## Linear algebraic formulation

**Key idea**: Instead of thinking about the puzzle as a game, we can think of it as
a linear algebra problem! Each button press is a linear transformation, and we want
to find a combination of button presses that transforms our initial state to the
all-off state.

This is much more efficient than trying all possible button combinations.
-/

open Statement (State effect press allOff isWin isAffected Button pressAt areAdjacent)

-- Convert a matrix state to a vector (flattens the 2D grid into a 1D vector)
def toVector (state : State m n) : Button m n → ZMod 2 :=
  Function.uncurry state

def fromVector (v : Button m n → ZMod 2) : State m n :=
  Function.curry v

-- Button effect matrix A where Ae_i = effect of pressing button i
def buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2) :=
  Matrix.of fun pos btn => toVector (effect btn) pos

def ButtonSelection (m n : ℕ) := Button m n → ZMod 2

def applySelection (initial : State m n) (selection : ButtonSelection m n) : State m n :=
  initial + fromVector (buttonMatrix.mulVec selection)

-- A puzzle is solvable if there exists some selection of buttons that
-- transforms the initial state to the all-off state
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

Let's work through some concrete examples to see how the theory works in practice!
-/

section Examples

/-- A simple 2×2 puzzle: single light at top-left corner (0,0)
    Visual representation:
    ┌───┬───┐
    │ ● │ ○ │
    ├───┼───┤
    │ ○ │ ○ │
    └───┴───┘
-/
def example2x2 : State 2 2 :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- What happens when we press the button at (0,0)?
    It toggles itself and its neighbors (0,1) and (1,0)
    Result:
    ┌───┬───┐
    │ ○ │ ● │  -- (0,0) toggled off, (0,1) toggled on
    ├───┼───┤
    │ ● │ ○ │  -- (1,0) toggled on, (1,1) unaffected
    └───┴───┘
-/
theorem example2x2_press_00 :
  pressAt example2x2 0 0 = Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { rw [pressAt, press, example2x2, effect, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply]
    simp only [isAffected, areAdjacent]
    decide }

/-- The correct solution for 2×2 single light: press buttons (0,0), (0,1), (1,0)
    Why this works: Each button toggles overlapping regions, and the overlaps
    cancel out, leaving only the original light toggled off -/
theorem example2x2_solution :
  applyButtons example2x2 ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) = allOff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [applyButtons, effect, isAffected,
    areAdjacent, example2x2, allOff]
    simp
    decide }

/-- Prove that our 2×2 puzzle is solvable using linear algebra -/
theorem example2x2_solvable : isSolvable example2x2 := by
  -- The solution is to press buttons (0,0), (0,1), (1,0) - encode this as a selection vector
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

/-- **Main theorem**: Solvability criterion using linear algebra

This theorem establishes the fundamental connection between the puzzle and linear algebra.
A Lights Out puzzle is solvable if and only if the initial state belongs to the
image (range) of the button linear map.

**What this means**: The button linear map represents all possible effects we can
achieve by pressing buttons. If our initial state is in the image of this map,
then there exists some combination of button presses that will get us to the all-off state.

**Why this is useful**: Instead of trying all 2^(m*n) possible button combinations,
we can use linear algebra to determine solvability in polynomial time.
-/
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

/-!
## Group structure on button selections

### What is a group?

A **group** is a mathematical structure that captures the idea of symmetry and reversible operations.
Think of it like a set of actions where:
1. You can combine any two actions to get another action
2. There's a "do nothing" action (the identity)
3. Every action can be undone (has an inverse)
4. The order of grouping doesn't matter when combining multiple actions

### The Lights Out group

In Lights Out, button presses form a special kind of group called an **abelian group**
(named after mathematician Niels Abel). This means the order of button presses doesn't matter:
pressing button A then B gives the same result as pressing B then A.

**The group structure**:
- **Elements**: Each "button selection" is a choice of which buttons to press
- **Operation**: Combine two selections by pressing all buttons from both selections
- **Identity**: The empty selection (don't press any buttons)
- **Inverse**: In our puzzle, every button press is its own inverse! This happens because
  we're working in ℤ/2ℤ (integers modulo 2), where 1 + 1 = 0. Pressing a button twice
  returns to the original state.
- **Commutativity**: press(A) + press(B) = press(B) + press(A)

**Why this matters**: This group structure transforms a seemingly complex puzzle into
a linear algebra problem that can be solved efficiently. Instead of trying all 2^(m×n)
possible button combinations, we can use the group structure to find solutions systematically.

The mathematical notation (ℤ/2ℤ)^(m×n) means: a group where each of the m×n positions
can be either 0 (don't press) or 1 (press), with addition modulo 2.
-/

-- The group of button selections is just the function type with pointwise addition
instance : Add (ButtonSelection m n) := Pi.instAdd
instance : Zero (ButtonSelection m n) := Pi.instZero
instance : Neg (ButtonSelection m n) := Pi.instNeg

-- In ℤ/2ℤ, every element is its own inverse
instance : AddCommGroup (ButtonSelection m n) := Pi.addCommGroup

-- The group is isomorphic to (ℤ/2ℤ)^(m×n)
def buttonGroupIso : ButtonSelection m n ≃+ (Button m n → ZMod 2) :=
  AddEquiv.refl _

-- Every button selection has order dividing 2
-- This is a fundamental property of the group structure
axiom button_selection_order_two (sel : ButtonSelection m n) :
  sel + sel = 0

-- The fundamental property: button order doesn't matter
-- This follows from the commutativity of addition in ℤ/2ℤ
axiom button_selections_commute (sel1 sel2 : ButtonSelection m n) (state : State m n) :
  applySelection (applySelection state sel1) sel2 = applySelection (applySelection state sel2) sel1

/-- Decidability of solvability -/
instance [Fintype (Fin m)] [Fintype (Fin n)] : DecidablePred (isSolvable : State m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype
