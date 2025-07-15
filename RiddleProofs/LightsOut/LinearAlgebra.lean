import Mathlib.LinearAlgebra.Matrix.ToLin
import RiddleProofs.LightsOut.Statement


/-- Decidability of solvability -/
instance [Fintype (Fin m)] [Fintype (Fin n)] :
    DecidablePred (isSolvable : LightState m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype


variable {m n : ℕ} [NeZero m] [NeZero n]

lemma toVector_injective : Function.Injective (@toVector m n) := by
  intros M N eq
  funext i j
  exact congr_fun eq ⟨i, j⟩

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





/-- Solvability criterion: initial state in button linear map image -/
theorem solvable_iff_in_image (initial : LightState m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range buttonLinearMap := by
    calc isSolvable initial
      ↔ ∃ selection, applySelection initial selection = allOff := Iff.rfl
      _ ↔ ∃ selection, initial + fromVector (buttonMatrix.mulVec selection) = allOff := by
          rfl
      _ ↔ ∃ selection, toVector (initial + fromVector (buttonMatrix.mulVec selection)) =
            toVector allOff := by
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
theorem button_self_inverse (button : Button m n) (state : LightState m n) :
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
theorem button_press_comm (button₁ button₂ : Button m n) (state : LightState m n) :
  press (press state button₁) button₂ = press (press state button₂) button₁ := by
  funext i j
  calc press (press state button₁) button₂ i j
    = state i j + effect button₁ i j + effect button₂ i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]
    _ = state i j + effect button₂ i j + effect button₁ i j := by ring
    _ = press (press state button₂) button₁ i j := by
        rw [press, press, Matrix.add_apply, Matrix.add_apply, add_assoc]
