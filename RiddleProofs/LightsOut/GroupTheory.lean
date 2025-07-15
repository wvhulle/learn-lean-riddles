import RiddleProofs.LightsOut.LinearAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic

/-!
## Vector space structure on button selections

The crucial observation is that button selections don't just form a group - they form a
**vector space** over the field 𝔽₂ = ℤ/2ℤ. This vector space structure is what makes
the Lights Out puzzle solvable via linear algebra.

**Vector space structure**:
- **Scalars**: 𝔽₂ = {0, 1} with addition and multiplication mod 2
- **Vectors**: ButtonSelection m n = (Button m n → 𝔽₂)
- **Addition**: Pointwise addition of selections
- **Scalar multiplication**: 0 · sel = ∅, 1 · sel = sel

**Why this matters**: The puzzle becomes solving Ax = b where:
- A is the button effect matrix (linear transformation)
- x is the button selection we want to find
- b is the target configuration (usually all-off)

-/

variable {m n : ℕ}

-- The group of button selections is just the function type with pointwise addition
instance : Add (ButtonSelection m n) := Pi.instAdd
instance : Zero (ButtonSelection m n) := Pi.instZero
instance : Neg (ButtonSelection m n) := Pi.instNeg

-- In ℤ/2ℤ, every element is its own inverse
instance : AddCommGroup (ButtonSelection m n) := Pi.addCommGroup

-- Button selections form a vector space over 𝔽₂
instance : Module (ZMod 2) (ButtonSelection m n) := Pi.module _ _ _

-- The vector space is isomorphic to 𝔽₂^(m×n)
def buttonVectorIso : ButtonSelection m n ≃ₗ[ZMod 2] (Button m n → ZMod 2) :=
  LinearEquiv.refl _ _

-- Solvability characterization: a configuration is solvable iff it's in the image of the button matrix
theorem solvability_characterization [NeZero m] [NeZero n] (initial : LightState m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range (buttonLinearMap : (Button m n → ZMod 2) →ₗ[ZMod 2] (Button m n → ZMod 2)) := by
  exact solvable_iff_in_image initial

-- Extensionality for button selections
@[ext]
theorem ButtonSelection.ext {sel1 sel2 : ButtonSelection m n}
    (h : ∀ button, sel1 button = sel2 button) : sel1 = sel2 :=
  funext h

-- Every button selection has order dividing 2 (involution property)
theorem button_selection_involution (sel : ButtonSelection m n) :
  sel + sel = 0 := by
  ext button
  calc sel button + sel button
    = 2 * sel button := by rw [two_mul]
    _ = 0 := by exact mul_eq_zero_of_left rfl (sel button)

-- The fundamental property: button order doesn't matter (commutativity)
theorem button_selections_commute (sel1 sel2 : ButtonSelection m n)
    (state : LightState m n) :
  applySelection (applySelection state sel1) sel2 =
    applySelection (applySelection state sel2) sel1 := by
  unfold applySelection
  calc state + fromVector (buttonMatrix.mulVec sel1) + fromVector (buttonMatrix.mulVec sel2)
    = state + (fromVector (buttonMatrix.mulVec sel1) + fromVector (buttonMatrix.mulVec sel2)) := by rw [add_assoc]
    _ = state + (fromVector (buttonMatrix.mulVec sel2) + fromVector (buttonMatrix.mulVec sel1)) := by rw [add_comm (fromVector _)]
    _ = state + fromVector (buttonMatrix.mulVec sel2) + fromVector (buttonMatrix.mulVec sel1) := by rw [← add_assoc]

-- The dimension of the button selection space equals the number of buttons
theorem buttonSelection_dimension [NeZero m] [NeZero n] [Fintype (Button m n)] :
  Module.finrank (ZMod 2) (ButtonSelection m n) = Fintype.card (Button m n) := by
  -- ButtonSelection m n = Button m n → ZMod 2 is a finite product of copies of ZMod 2
  -- Since ZMod 2 is a field (with the prime fact), we can use Module.finrank_pi
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold ButtonSelection
  apply Module.finrank_pi

-- Explicit dimension calculation for m×n grid
theorem buttonSelection_dimension_grid [NeZero m] [NeZero n] [Fintype (Fin m)] [Fintype (Fin n)] :
  Module.finrank (ZMod 2) (ButtonSelection m n) = m * n := by
  have card_fin_m : Fintype.card (Fin m) = m := by convert Fintype.card_fin m
  have card_fin_n : Fintype.card (Fin n) = n := by convert Fintype.card_fin n
  rw [buttonSelection_dimension]
  simp only [Button, Fintype.card_prod]
  rw [card_fin_m, card_fin_n]




-- Button effect as matrix-vector multiplication
theorem button_effect_as_matrix_vector (btn : Button m n) :
  toVector (effect btn) = buttonMatrix.mulVec (Pi.single btn 1) := by
  funext pos
  simp only [buttonMatrix, toVector, Matrix.mulVec, Pi.single]
  -- The goal is: Function.uncurry (effect btn) pos = (fun j => Function.uncurry (effect j) pos) ⬝ᵥ Function.update 0 btn 1
  -- This is a dot product, so let's unfold it
  simp only [dotProduct]
  -- Now we have a sum that equals the function value when only btn contributes
  rw [Finset.sum_eq_single btn]
  · simp only [Function.update_apply]
    -- The goal is: Function.uncurry (effect btn) pos = Matrix.of (...) pos btn * (if btn = btn then 1 else 0)
    simp only [ite_true, mul_one]
    -- This reduces to showing Matrix.of (fun pos btn => Function.uncurry (effect btn) pos) pos btn = Function.uncurry (effect btn) pos
    rw [Matrix.of_apply]
  · intro b hb_mem hb_ne
    simp only [Function.update_apply]
    -- The goal is: Matrix.of (...) pos b * (if b = btn then 1 else 0) = 0
    simp only [hb_ne, if_false]
    exact rfl
  · intro hbtn_not_mem
    exfalso
    exact hbtn_not_mem (Finset.mem_univ btn)

-- The kernel characterizes "null" button combinations
theorem kernel_characterization_incomplete (sel : ButtonSelection m n) :
  sel ∈ LinearMap.ker buttonLinearMap ↔
  applySelection allOff sel = allOff := by
  simp only [LinearMap.mem_ker, buttonLinearMap]
  simp only [applySelection]
  show (Matrix.toLin' buttonMatrix) sel = 0 ↔ allOff + fromVector (buttonMatrix.mulVec sel) = allOff
  constructor
  · intro h
    -- If buttonMatrix.mulVec sel = 0, then fromVector (buttonMatrix.mulVec sel) = fromVector 0 = allOff
    -- So allOff + fromVector (buttonMatrix.mulVec sel) = allOff + allOff = allOff
    rw [Matrix.toLin'_apply] at h
    rw [h]
    simp only [fromVector]
    exact rfl
  · intro h
    -- If allOff + fromVector (buttonMatrix.mulVec sel) = allOff, then fromVector (buttonMatrix.mulVec sel) = 0
    -- Since toVector and fromVector are inverses, this means buttonMatrix.mulVec sel = 0
    rw [Matrix.toLin'_apply]
    have h1 : fromVector (buttonMatrix.mulVec sel) = 0 := by
      exact (eq_zero_iff_eq_zero_of_add_eq_zero h).mp rfl
    -- Now we need to show buttonMatrix.mulVec sel = 0
    -- Since fromVector and toVector are inverses, this follows from h1
    have h2 : toVector (fromVector (buttonMatrix.mulVec sel)) = toVector 0 := by
      rw [h1]
    simp only [toVector] at h2
    exact h2

-- A concrete 2×2 example
section TwoByTwo
variable [Fintype (Fin 2)]

-- In a 2×2 grid, we have exactly 4 buttons and dimension 4
example : Module.finrank (ZMod 2) (ButtonSelection 2 2) = 4 := by
  exact buttonSelection_dimension_grid

-- Single button press: represents pressing exactly one button
def singleButtonPress (btn : Button 2 2) : ButtonSelection 2 2 :=
  Pi.single btn 1

-- Single button presses form a basis for the vector space
theorem singleButton_basis_incomplete :
  LinearIndependent (ZMod 2) (singleButtonPress : Button 2 2 → ButtonSelection 2 2) := by
  unfold singleButtonPress
  sorry -- Requires proving Pi.single functions are linearly independent

end TwoByTwo
