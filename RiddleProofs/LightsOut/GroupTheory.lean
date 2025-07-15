import RiddleProofs.LightsOut.Statement
import RiddleProofs.LightsOut.LinearAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.PrincipalIdealDomain
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

**Key properties**:
1. **Dimension**: The vector space has dimension m×n
2. **Involution**: Every selection is its own inverse (sel + sel = 0)
3. **Commutativity**: Order of button presses doesn't matter
4. **Solvability**: A configuration is solvable iff it's in the image of the button matrix
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

-- Connection to linear algebra: solvability characterization
theorem solvability_via_vector_space [NeZero m] [NeZero n] (initial : LightState m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range (buttonLinearMap : (Button m n → ZMod 2) →ₗ[ZMod 2] (Button m n → ZMod 2)) := by
  exact solvable_iff_in_image initial

-- Extensionality for button selections
@[ext]
theorem ButtonSelection.ext {sel1 sel2 : ButtonSelection m n}
    (h : ∀ button, sel1 button = sel2 button) : sel1 = sel2 :=
  funext h

-- Every button selection has order dividing 2 (involution property)
theorem button_selection_order_two (sel : ButtonSelection m n) :
  sel + sel = 0 := by
  ext button
  rw [Pi.add_apply]
  change sel button + sel button = 0
  rw [← two_mul]
  exact mul_eq_zero_of_left rfl (sel button)

-- The fundamental property: button order doesn't matter (commutativity)
theorem button_selections_commute (sel1 sel2 : ButtonSelection m n)
    (state : LightState m n) :
  applySelection (applySelection state sel1) sel2 =
    applySelection (applySelection state sel2) sel1 := by
  unfold applySelection
  simp only [add_assoc]
  congr 1
  rw [add_comm]

-- The dimension of the button selection space
theorem buttonSelection_dimension [NeZero m] [NeZero n] [Fintype (Button m n)] :
  Module.finrank (ZMod 2) (ButtonSelection m n) = Fintype.card (Button m n) := by
  -- ButtonSelection m n = Button m n → ZMod 2
  -- This is a finite product of copies of ZMod 2
  -- ZMod 2 is a field, giving us the StrongRankCondition needed for Module.finrank_pi
  
  -- Try to establish that 2 is prime and get field instance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  
  -- With the Fact instance, ZMod 2 should automatically be a field
  -- Let's try to use Module.finrank_pi directly
  unfold ButtonSelection
  
  -- Apply Module.finrank_pi which should work now that we have the Fact instance
  apply Module.finrank_pi

-- Concrete dimension calculation
theorem buttonSelection_dimension_explicit [NeZero m] [NeZero n] [Fintype (Fin m)] [Fintype (Fin n)] :
  Module.finrank (ZMod 2) (ButtonSelection m n) = m * n := by
  rw [buttonSelection_dimension]
  simp only [Button, Fintype.card_prod]
  -- We need to prove Fintype.card (Fin m) * Fintype.card (Fin n) = m * n
  -- This should be true by Fintype.card_fin, but we need to handle instance unification
  have h1 : Fintype.card (Fin m) = m := by
    -- Convert the instance to the standard one
    convert Fintype.card_fin m
  have h2 : Fintype.card (Fin n) = n := by
    -- Convert the instance to the standard one
    convert Fintype.card_fin n
  rw [h1, h2]




-- Button effect is a linear combination of basis vectors
theorem button_effect_linear (btn : Button m n) :
  toVector (effect btn) = buttonMatrix.mulVec (Pi.single btn 1) := by
  funext pos
  simp only [buttonMatrix, toVector, Matrix.mulVec, Pi.single]
  -- The goal is: Function.uncurry (effect btn) pos = (fun j => Function.uncurry (effect j) pos) ⬝ᵥ Function.update 0 btn 1
  -- This is a dot product, so let's unfold it
  simp only [Matrix.dotProduct]
  -- Now we have a sum that equals the function value when only btn contributes
  rw [Finset.sum_eq_single btn]
  · simp only [Function.update_apply, if_pos rfl, mul_one]
    -- This reduces to showing Matrix.of (fun pos btn => Function.uncurry (effect btn) pos) pos btn = Function.uncurry (effect btn) pos
    rw [Matrix.of_apply]
  · intro b hb_mem hb_ne
    simp only [Function.update_apply, if_neg hb_ne, mul_zero]
  · intro hbtn_not_mem
    exfalso
    exact hbtn_not_mem (Finset.mem_univ btn)

-- The kernel characterizes "null" button combinations
theorem kernel_characterization (sel : ButtonSelection m n) :
  sel ∈ LinearMap.ker buttonLinearMap ↔
  applySelection allOff sel = allOff := by
  simp only [LinearMap.mem_ker, buttonLinearMap]
  simp only [applySelection]
  sorry -- This would require careful kernel computation

-- A concrete 2×2 example
section TwoByTwo
variable [Fintype (Fin 2)]

-- In a 2×2 grid, we have 4 buttons and 4 light positions
example : Module.finrank (ZMod 2) (ButtonSelection 2 2) = 4 := by
  exact buttonSelection_dimension_explicit

-- Example: single button press
def singleButtonPress (btn : Button 2 2) : ButtonSelection 2 2 :=
  Pi.single btn 1

-- Single button presses form a basis for the vector space
theorem singleButton_linearly_independent :
  LinearIndependent (ZMod 2) (singleButtonPress : Button 2 2 → ButtonSelection 2 2) := by
  unfold singleButtonPress
  sorry -- This would require proving Pi.single functions are linearly independent

end TwoByTwo
