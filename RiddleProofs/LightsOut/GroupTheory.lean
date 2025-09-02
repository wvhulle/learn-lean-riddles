import RiddleProofs.LightsOut.LinearAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
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

instance : AddCommGroup (ButtonSelection m n) := Pi.addCommGroup

instance : Module (ZMod 2) (ButtonSelection m n) := Pi.module _ _ _

def buttonVectorIso : ButtonSelection m n ≃ₗ[ZMod 2] (Button m n → ZMod 2) :=
  LinearEquiv.refl _ _

theorem solvability_characterization [NeZero m] [NeZero n] (initial : LightState m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range (buttonLinearMap : (Button m n → ZMod 2) →ₗ[ZMod 2] (Button m n → ZMod 2)) :=
  solvable_iff_in_image initial

@[ext]
theorem ButtonSelection.ext {sel1 sel2 : ButtonSelection m n}
    (h : ∀ button, sel1 button = sel2 button) : sel1 = sel2 :=
  funext h

theorem button_selection_involution (sel : ButtonSelection m n) :
  sel + sel = 0 := by
  ext button
  calc sel button + sel button
    = 2 * sel button := by rw [two_mul]
    _ = 0 := by exact mul_eq_zero_of_left rfl (sel button)

theorem button_selections_commute (sel1 sel2 : ButtonSelection m n) (state : LightState m n) :
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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold ButtonSelection
  apply Module.finrank_pi

theorem buttonSelection_dimension_grid [NeZero m] [NeZero n] :
  Module.finrank (ZMod 2) (ButtonSelection m n) = m * n := by
  rw [buttonSelection_dimension]
  unfold Button
  simp only [Fintype.card_prod, Fintype.card_fin]




theorem button_effect_as_matrix_vector (btn : Button m n) :
  toVector (effect btn) = buttonMatrix.mulVec (Pi.single btn 1) := by
  funext pos
  simp only [buttonMatrix, Matrix.mulVec, Pi.single, Matrix.of_apply, dotProduct]
  rw [Finset.sum_eq_single btn]
  · simp only [Function.update_apply, if_true, mul_one]
  · intro b _ hb_ne
    simp only [Function.update_apply, if_neg hb_ne]
    simp
  · intro h
    exact absurd (Finset.mem_univ btn) h

/--
  In plain English: A button selection is in the kernel of the button linear map
  if and only if applying that selection to the all-off state leaves you in the
  all-off state.

  Intuitive meaning

  The Kernel = "Null" Button Combinations

  The kernel of the button linear map consists of all button selections that have
   no net effect on any light configuration. These are the "useless" or "null"
  button combinations.

  What this means for the puzzle:

  1. If you press buttons according to a kernel selection starting from all
  lights off, you'll end up with all lights still off
  2. More generally, if you press buttons according to a kernel selection
  starting from any configuration, you'll end up with the same configuration you
  started with

  Examples of kernel elements:

  - The empty selection (press no buttons) - obviously does nothing
  - Any button pressed twice - since pressing the same button twice cancels out
  in 𝔽₂
  - "Canceling patterns" - combinations where the effects exactly cancel each
  other out

  Why this matters for solvability:

  This theorem connects to a fundamental principle in linear algebra:
  - If you can solve the puzzle from some initial state, then you can solve it
  from any state that differs from the first by a kernel element
  - Conversely, if two states differ by a kernel element, they have the same
  solvability status

  A concrete example

  Imagine you found a button sequence that solves a particular puzzle. If you
  also know a kernel element (a "useless" button combination), then:
  - Adding the kernel element to your solution gives you another solution
  - The kernel element by itself applied to the all-off state keeps it all-off
-/
theorem kernel_characterization (sel : ButtonSelection m n) :
  sel ∈ LinearMap.ker buttonLinearMap ↔
  applySelection allOff sel = allOff := by
  simp only [LinearMap.mem_ker, buttonLinearMap, applySelection]
  constructor
  · intro h
    -- If buttonLinearMap sel = 0, then applying sel to allOff gives allOff
    -- buttonLinearMap sel = Matrix.toLin' buttonMatrix sel = buttonMatrix.mulVec sel
    have h_mulVec : (buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2)).mulVec sel = 0 := by
      rw [← Matrix.toLin'_apply (buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2))]
      exact h
    have fromVector_zero : fromVector (0 : Button m n → ZMod 2) = allOff := by
      unfold fromVector allOff
      rfl
    calc allOff + fromVector (buttonMatrix.mulVec sel)
      = allOff + fromVector 0 := by rw [h_mulVec]
      _ = allOff + allOff := by rw [fromVector_zero]
      _ = allOff := by
        funext i j
        simp only [allOff]
        exact add_zero 0
  · intro h
    -- If applying sel to allOff gives allOff, then buttonLinearMap sel = 0
    -- From h: allOff + fromVector (buttonMatrix.mulVec sel) = allOff
    -- This means fromVector (buttonMatrix.mulVec sel) = allOff
    have h_zero : fromVector ((buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2)).mulVec sel) = allOff := by
      have : allOff + fromVector (buttonMatrix.mulVec sel) = allOff + allOff := by
        rw [h]
        funext i j
        simp only [allOff]
        exact add_zero 0
      have cancel : ∀ (a b c : LightState m n), a + b = a + c → b = c := by
        intros a b c h_eq
        funext i j
        have : a i j + b i j = a i j + c i j := by
          exact congr_fun (congr_fun h_eq i) j
        exact add_left_cancel this
      exact cancel allOff (fromVector (buttonMatrix.mulVec sel)) allOff this
    -- Since toVector ∘ fromVector = id, we have buttonMatrix.mulVec sel = 0
    have toVector_fromVector_id : ∀ v : Button m n → ZMod 2, toVector (fromVector v) = v := by
      intro v
      unfold toVector fromVector
      simp
    have mulVec_zero : (buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2)).mulVec sel = 0 := by
      rw [← toVector_fromVector_id (buttonMatrix.mulVec sel)]
      rw [h_zero]
      unfold toVector allOff
      rfl
    -- Now we need to show: (Matrix.toLin' buttonMatrix) sel = 0
    -- We know buttonMatrix.mulVec sel = 0, and (Matrix.toLin' buttonMatrix) sel = buttonMatrix.mulVec sel
    calc (Matrix.toLin' (buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2))) sel
      = (buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2)).mulVec sel := by
          exact Matrix.toLin'_apply (buttonMatrix : Matrix (Button m n) (Button m n) (ZMod 2)) sel
      _ = 0 := mulVec_zero

-- A concrete 2×2 example
section TwoByTwo
variable [Fintype (Fin 2)]

example : Module.finrank (ZMod 2) (ButtonSelection 2 2) = 4 :=
  buttonSelection_dimension_grid

def singleButtonPress (btn : Button 2 2) : ButtonSelection 2 2 :=
  Pi.single btn 1

theorem singleButton_basis :
  LinearIndependent (ZMod 2) (singleButtonPress : Button 2 2 → ButtonSelection 2 2) := by
  unfold singleButtonPress
  have func_eq : (Pi.basisFun (ZMod 2) (Button 2 2) : Button 2 2 → ButtonSelection 2 2) = fun btn => Pi.single btn 1 := by
    funext btn
    exact Pi.basisFun_apply (ZMod 2) (Button 2 2) btn
  rw [← func_eq]
  exact (Pi.basisFun (ZMod 2) (Button 2 2)).linearIndependent

end TwoByTwo
