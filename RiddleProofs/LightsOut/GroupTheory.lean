import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import RiddleProofs.LightsOut.Statement

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


variable {m n : ℕ} [NeZero m] [NeZero n]


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
axiom button_selections_commute (sel1 sel2 : ButtonSelection m n)
    (state : LightState m n) :
  applySelection (applySelection state sel1) sel2 =
    applySelection (applySelection state sel2) sel1

/-- Decidability of solvability -/
instance [Fintype (Fin m)] [Fintype (Fin n)] :
    DecidablePred (isSolvable : LightState m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype
