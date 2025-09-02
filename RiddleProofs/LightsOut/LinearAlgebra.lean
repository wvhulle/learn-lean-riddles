import Mathlib.LinearAlgebra.Matrix.ToLin
import RiddleProofs.LightsOut.Statement

variable {m n : ℕ}

section BasicProperties

lemma matrix_to_vector_injective : Function.Injective (@toVector m n) := by
  intros state1 state2 eq
  funext i j
  exact congr_fun eq ⟨i, j⟩

lemma binary_add_cancel {a b : ZMod 2} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + 0 := by rw [add_zero]
         _ = a + (b + b) := by rw [← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]
         _ = (a + b) + b := by rw [add_assoc]
         _ = 0 + b := by rw [h]
         _ = b := by rw [zero_add]
  · intro h; rw [h, ← two_mul, (by decide : (2 : ZMod 2) = 0), zero_mul]

end BasicProperties

section LinearAlgebraStructure

def effectsLinearMap : ((Fin m × Fin n) → ZMod 2) →ₗ[ZMod 2] ((Fin m × Fin n) → ZMod 2) :=
  Matrix.toLin' buttonMatrix


theorem puzzle_solvable_iff_in_span (initial : LightState m n) :
  isSolvable initial ↔
  toVector initial ∈ Set.range effectsLinearMap := by
    calc isSolvable initial
      ↔ ∃ selection, applySelection initial selection = allOff := Iff.rfl
      _ ↔ ∃ selection, initial + fromVector (buttonMatrix.mulVec selection) = allOff := by
          rfl
      _ ↔ ∃ selection, toVector (initial + fromVector (buttonMatrix.mulVec selection)) =
            toVector allOff := by
          constructor
          · rintro ⟨selection, h⟩; use selection; rw [h]
          · rintro ⟨selection, h⟩; use selection; exact matrix_to_vector_injective h
      _ ↔ ∃ selection, toVector initial + buttonMatrix.mulVec selection = 0 := by
          simp only [fromVector]
          constructor
          · rintro ⟨selection, h⟩; use selection; funext pos; exact congr_fun h pos
          · rintro ⟨selection, h⟩; use selection; funext pos; exact congr_fun h pos
      _ ↔ ∃ selection, buttonMatrix.mulVec selection = toVector initial := by
          constructor
          · rintro ⟨selection, h⟩; use selection; funext pos
            exact binary_add_cancel.mp (by rw [add_comm]; exact congr_fun h pos)
          · rintro ⟨selection, h⟩; use selection; funext pos
            rw [← h]; exact binary_add_cancel.mpr rfl
      _ ↔ toVector initial ∈ Set.range (buttonMatrix.mulVec) := Set.mem_range.symm
      _ ↔ toVector initial ∈ Set.range effectsLinearMap := by
          simp only [effectsLinearMap]
          rfl

end LinearAlgebraStructure

section ButtonProperties


theorem press_involution (button : Button m n) (state : LightState m n) :
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

theorem press_commute (button₁ button₂ : Button m n) (state : LightState m n) :
  press (press state button₁) button₂ = press (press state button₂) button₁ := by
  funext i j
  simp only [press, Matrix.add_apply]
  ring

end ButtonProperties

section Decidability

instance [Fintype (Fin m)] [Fintype (Fin n)] :
    DecidablePred (isSolvable : LightState m n → Prop) := by
  intro initial
  unfold isSolvable
  have : Fintype (ButtonSelection m n) := by
    unfold ButtonSelection
    infer_instance
  apply Fintype.decidableExistsFintype

end Decidability
