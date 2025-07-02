import Mathlib.Probability.Notation

open ENNReal

@[simp] lemma ENNReal.div_mul_cancel_nat_cast {a b c : ℕ} {hc_pos : 0 < c} :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) :=
  calc (↑(a * c) : ENNReal) / (↑(b * c))
    = (↑a * ↑c : ENNReal) / (↑b * ↑c) := by rw [Nat.cast_mul, Nat.cast_mul]
    _ = (↑a : ENNReal) / (↑b : ENNReal) :=
      ENNReal.mul_div_mul_right (↑a) (↑b)
        (Nat.cast_ne_zero.mpr (ne_of_gt hc_pos))
        (ENNReal.natCast_ne_top c)

@[simp] lemma ENNReal.inv_div_mul_div {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) :=
  calc (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal))
    = (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) := rfl
    _ = ((↑a : ENNReal)⁻¹)⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) := by rw [one_div]
    _ = (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) := by rw [inv_inv]
    _ = ((↑a : ENNReal) * (↑b : ENNReal)) / (↑c : ENNReal) := by rw [← mul_div_assoc]
    _ = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by rw [← Nat.cast_mul]

@[simp] lemma ENNReal.ofReal_div_pos {a b : ℝ} {hb : 0 < b} :
  ENNReal.ofReal (a / b) = ENNReal.ofReal a / ENNReal.ofReal b :=
  ENNReal.ofReal_div_of_pos hb

@[simp] lemma ENNReal.ofReal_inv_div_toReal {a : ENNReal} {ha_ne_top: a ≠ ⊤} :
  ENNReal.ofReal ((1 / ENNReal.toReal a)⁻¹) = a :=
  calc ENNReal.ofReal ((1 / ENNReal.toReal a)⁻¹)
    = ENNReal.ofReal ((ENNReal.toReal a)⁻¹⁻¹) := by rw [one_div]
    _ = ENNReal.ofReal (ENNReal.toReal a) := by rw [inv_inv (ENNReal.toReal a)]
    _ = a := ENNReal.ofReal_toReal ha_ne_top

lemma ENNReal.div_eq_ofReal_div {a b : ENNReal} (hb_ne_zero: b ≠ 0) (ha_ne_top: a ≠ ⊤):
  a / b = ENNReal.ofReal (ENNReal.toReal a / ENNReal.toReal b) :=
  calc a / b
    = ENNReal.ofReal (ENNReal.toReal (a / b)) := (ENNReal.ofReal_toReal (ENNReal.div_ne_top ha_ne_top hb_ne_zero)).symm
    _ = ENNReal.ofReal (ENNReal.toReal a / ENNReal.toReal b) := by rw [ENNReal.toReal_div a b]

private lemma div_eq_div_of_nat_mul_eq {a b c d e : ℕ} (h : a * b * e = d * c)
  (hc_pos : 0 < c) (he_pos : 0 < e) :
  (↑(a * b) : ENNReal) / (↑c : ENNReal) = (↑d : ENNReal) / (↑e : ENNReal) :=
  (ENNReal.div_eq_div_iff
    (Nat.cast_ne_zero.mpr (ne_of_gt he_pos))
    (ENNReal.natCast_ne_top e)
    (Nat.cast_ne_zero.mpr (ne_of_gt hc_pos))
    (ENNReal.natCast_ne_top c)).mpr (by
      norm_cast
      rw [mul_comm e (a * b), mul_comm c d]
      exact h)

-- Simplify multiplication with fraction using proportional equality
@[simp] lemma ENNReal.mul_div_eq_div_of_mul_eq {a b c d e : ℕ} (h : a * b * e = d * c)
  (hc_pos : 0 < c) (he_pos : 0 < e) :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑d : ENNReal) / (↑e : ENNReal) :=
  calc (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal))
    = ((↑a : ENNReal) * (↑b : ENNReal)) / (↑c : ENNReal) := (mul_div_assoc (↑a : ENNReal) (↑b : ENNReal) (↑c : ENNReal)).symm
    _ = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by rw [← Nat.cast_mul]
    _ = (↑d : ENNReal) / (↑e : ENNReal) := div_eq_div_of_nat_mul_eq h hc_pos he_pos
