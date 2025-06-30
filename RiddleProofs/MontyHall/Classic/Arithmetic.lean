import Mathlib.Probability.Notation

open ENNReal


@[simp] lemma ennreal_frac_reduce {a b c : ℕ} {hc_pos : 0 < c} :
  (a * c : ENNReal) / (b * c) = a / b := by
  apply ENNReal.mul_div_mul_right
  · simp [Nat.cast_ne_zero, ne_of_gt hc_pos]
  · simp [ENNReal.natCast_ne_top]

@[simp] lemma ennreal_inv_frac_mul_frac_general {a b c : ℕ} :
  (1 / (a : ENNReal))⁻¹ * ((b : ENNReal) / (c : ENNReal)) = ((a * b : ℕ) : ENNReal) / (c : ENNReal) := by
  rw [one_div, inv_inv, ← mul_div_assoc, Nat.cast_mul]


@[simp] lemma ennreal_ofReal_div_pos {a b : ℝ} {hb : 0 < b} :
  ENNReal.ofReal (a / b) = ENNReal.ofReal a / ENNReal.ofReal b :=
  ENNReal.ofReal_div_of_pos hb

@[simp] lemma ennreal_inv_inv {a: ENNReal}: (a ⁻¹)⁻¹ = a := by simp

@[simp] lemma ennreal_div_inv {a : ENNReal} {g: a ≠ ⊤} :
  ENNReal.ofReal ((1 / ENNReal.toReal a)⁻¹) = a := by
  rw [one_div, inv_inv, ENNReal.ofReal_toReal g]


lemma ennreal_div_eq {a b : ENNReal} (h: b ≠ 0) (i: a ≠ ⊤):
  a / b = ENNReal.ofReal (ENNReal.toReal a / ENNReal.toReal b) := by
  rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top i h)]
  congr 1
  exact ENNReal.toReal_div a b


@[simp]  lemma ennreal_mul_frac_simplify {a b c d e : ℕ} (h : a * b * e = d * c)
  (hc_pos : 0 < c) (he_pos : 0 < e) :
  (a : ENNReal) * ((b : ENNReal) / (c : ENNReal)) = (d : ENNReal) / (e : ENNReal) := by
  have h1: (a : ENNReal) * (b / c) = (a * b) / c := by
    exact Eq.symm (mul_div_assoc (a : ENNReal) (b : ENNReal) (c : ENNReal))
  rw [h1]
  refine (ENNReal.div_eq_div_iff ?_ ?_ ?_ ?_).mpr ?_
  · simp [Nat.cast_ne_zero, ne_of_gt hc_pos]
    intro a
    linarith
  · simp [ENNReal.natCast_ne_top]
  · simp [Nat.cast_ne_zero, ne_of_gt he_pos]
    linarith
  · simp [ENNReal.natCast_ne_top]
  · norm_cast
    rw [mul_comm e (a * b)]
    rw [mul_comm c d]
    exact h
