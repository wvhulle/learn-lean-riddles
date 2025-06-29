import Mathlib

-- Test the specific case that should work with our generic lemmas
open ENNReal

-- Basic simp lemmas for ENNReal arithmetic
@[simp] lemma ennreal_ofReal_div_pos (a b : ℝ) (hb : 0 < b) : ENNReal.ofReal (a / b) = ENNReal.ofReal a / ENNReal.ofReal b :=
  ENNReal.ofReal_div_of_pos hb

@[simp] lemma ennreal_ofReal_one_div_nat (n : ℕ) [NeZero n] : ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹ := by
  have h_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  rw [ENNReal.ofReal_div_of_pos h_pos]
  simp

@[simp] lemma ennreal_ofReal_nat_inv (n : ℕ) [NeZero n] : ENNReal.ofReal ((n : ℝ)⁻¹) = (n : ENNReal)⁻¹ := by
  rw [← one_div]
  exact ennreal_ofReal_one_div_nat n

@[simp] lemma ennreal_ofReal_add_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  ENNReal.ofReal a + ENNReal.ofReal b = ENNReal.ofReal (a + b) :=
  (ENNReal.ofReal_add ha hb).symm

@[simp] lemma ennreal_fraction_simplify (m n : ℕ) [NeZero n] [NeZero m] :
  ENNReal.ofReal ((m : ℝ) / (n : ℝ)) = (m : ENNReal) / (n : ENNReal) := by
  rw [ennreal_ofReal_div_pos]
  simp
  exact Nat.cast_pos.mpr (NeZero.pos n)

-- Test the problematic goal step by step
example : (18 : ENNReal)⁻¹ + 2 / 18 = (6 : ENNReal)⁻¹ := by
  -- First convert the mixed form to a pure ENNReal form
  rw [← ENNReal.inv_natCast]
  rw [← ENNReal.natCast_div]
  rw [← ENNReal.inv_natCast]
  -- Now we should have: (18 : ENNReal)⁻¹ + ((2 : ENNReal) / (18 : ENNReal)) = (6 : ENNReal)⁻¹
  rw [← add_div]
  rw [ENNReal.one_add_natCast]
  rw [ENNReal.natCast_div]
  norm_cast
  norm_num

-- Test a simpler case first
example : (18 : ENNReal)⁻¹ + (2 : ENNReal) * (18 : ENNReal)⁻¹ = (6 : ENNReal)⁻¹ := by
  rw [← add_mul]
  rw [← ENNReal.natCast_one]
  rw [← ENNReal.natCast_add]
  norm_cast
  norm_num

-- Test the most basic arithmetic
example : (1 : ENNReal) + 2 = 3 := by simp
