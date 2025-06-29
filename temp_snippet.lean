import Mathlib.Data.ENNReal.Basic
open ENNReal

@[simp] lemma ennreal_nat_inv (n : ℕ) [NeZero n] : (n : ENNReal)⁻¹ = ENNReal.ofReal (1 / (n : ℝ)) := by
  have h_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  rw [← ENNReal.ofReal_natCast n]
  rw [← ENNReal.ofReal_inv_of_pos h_pos]
  simp [one_div]

-- Test it works
example : (18 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 18) := by simp