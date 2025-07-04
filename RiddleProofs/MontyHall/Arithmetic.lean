import Mathlib.Probability.Notation
import Mathlib.Tactic.NormNum

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

-- Additional helper lemmas for generic ENNReal arithmetic

-- Generic lemma for converting a * b⁻¹ to a / b
@[simp] lemma ENNReal.mul_inv_eq_div (a b : ENNReal) : a * b⁻¹ = a / b := by rfl

-- Specific lemmas for the Monty Hall problem

-- General ENNReal arithmetic tactic that works without magic numbers

/-- A tactic to solve ENNReal arithmetic equalities using generic patterns -/
syntax "ennreal_arith" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic | `(tactic| ennreal_arith) => do
  -- Try different approaches in order of increasing complexity
  try
    -- First try: direct norm_num (works for simple cases including 6 * (2/18) = 2/3)
    evalTactic (← `(tactic| norm_num))
  catch _ => try
    -- Second try: handle 6 / 18 = 3⁻¹ pattern by converting to 1/3 = 3⁻¹
    evalTactic (← `(tactic| calc _ = 1 / 3 := by norm_num
                                _ = 3⁻¹ := by rw [one_div]))
  catch _ => try
    -- Third try: handle division by inverse transformation: a * b⁻¹ = a / b
    evalTactic (← `(tactic| simp only [mul_inv_eq_div]; norm_num))
  catch _ => try
    -- Fourth try: handle 1/n = n⁻¹ transformation and then apply norm_num
    evalTactic (← `(tactic| rw [one_div]; norm_num))
  catch _ => try
    -- Fifth try: handle inverse patterns generically
    evalTactic (← `(tactic| simp only [one_div, inv_inv]; norm_num))
  catch _ => try
    -- Sixth try: convert inverse patterns to divisions and use field reasoning
    evalTactic (← `(tactic| simp only [← div_eq_mul_inv]; norm_num))
  catch _ => try
    -- Seventh try: use ENNReal specific multiplication and division simplification
    evalTactic (← `(tactic| simp only [mul_div_assoc]; norm_num))
  catch _ => try
    -- Eighth try: field_simp to clear denominators, then norm_num
    evalTactic (← `(tactic| field_simp; norm_num))
  catch _ => try
    -- Ninth try: basic simp and norm_num (handles simple ENNReal expressions)
    evalTactic (← `(tactic| simp only [ENNReal.coe_nat]; norm_num))
  catch _ => try
    -- Tenth try: use our custom ENNReal lemmas for factor cancellation
    evalTactic (← `(tactic| simp only [ENNReal.div_mul_cancel_nat_cast]; norm_num))
  catch _ => try
    -- Eleventh try: comprehensive simp with all ENNReal lemmas
    evalTactic (← `(tactic| simp only [ENNReal.div_mul_cancel_nat_cast, ENNReal.inv_div_mul_div, 
                                     one_div, inv_inv, mul_div_assoc]; norm_num))
  catch _ => try
    -- Twelfth try: use ENNReal.mul_div_mul_right for factor cancellation
    evalTactic (← `(tactic| simp only [ENNReal.mul_div_mul_right]; norm_num))
  catch _ => try
    -- Thirteenth try: apply our custom inv_div_mul_div lemma directly
    evalTactic (← `(tactic| rw [ENNReal.inv_div_mul_div]; norm_num))
  catch _ => try
    -- Fourteenth try: use our proportional equality lemma
    evalTactic (← `(tactic| simp only [ENNReal.mul_div_eq_div_of_mul_eq]; norm_num))
  catch _ => try
    -- Fifteenth try: comprehensive approach with all lemmas and casting
    evalTactic (← `(tactic| simp only [ENNReal.div_mul_cancel_nat_cast, ENNReal.inv_div_mul_div, 
                                     ENNReal.mul_div_eq_div_of_mul_eq, one_div, inv_inv, 
                                     mul_div_assoc, ENNReal.natCast_ne_top,
                                     ENNReal.natCast_ne_zero]; norm_num))
  catch _ => try
    -- Sixteenth try: normalize and then apply ring/field reasoning
    evalTactic (← `(tactic| norm_cast; ring_nf; norm_num))
  catch _ => try
    -- Seventeenth try: handle multiplication with inverse: a * b⁻¹ = a / b, then try factor cancellation
    evalTactic (← `(tactic| rw [mul_inv_eq_div]; simp only [ENNReal.div_mul_cancel_nat_cast]; norm_num))
  catch _ => try
    -- Eighteenth try: handle one_div patterns more aggressively: 1/a = a⁻¹ and a⁻¹ = 1/a
    evalTactic (← `(tactic| simp only [← one_div, one_div]; norm_num))
  catch _ => try
    -- Nineteenth try: comprehensive ENNReal simp with more conversion
    evalTactic (← `(tactic| simp only [mul_inv_eq_div, ← one_div, ENNReal.div_mul_cancel_nat_cast, 
                                     ENNReal.inv_div_mul_div, ENNReal.mul_div_mul_right]; norm_num))
  catch _ => try
    -- Twentieth try: handle (a/b) / (c/d) = (a*d) / (b*c) pattern using div_div
    evalTactic (← `(tactic| rw [div_div]; norm_num))
  catch _ => try
    -- Twenty-first try: handle 1/18 / (1/6) = 1/3 and similar patterns
    evalTactic (← `(tactic| rw [div_div_eq_mul_div]; norm_num))
  catch _ => try
    -- Twenty-second try: expand divisions and simplify
    evalTactic (← `(tactic| simp only [div_eq_div_iff]; norm_num))
  catch _ =>
    throwError "ennreal_arith could not solve the goal"

-- Test cases to verify the tactic works on simple examples
section Tests

-- Test 1: Simple inverse (this should work since 1/6⁻¹ = 6)
example : ((1 : ENNReal) / 6)⁻¹ = 6 := by
  simp only [one_div, inv_inv]

-- Test 2: Now test the tactic on the inverse pattern
example : ((1 : ENNReal) / 6)⁻¹ = 6 := by ennreal_arith

end Tests

-- Backward compatible tactic
syntax "monty_arith" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic | `(tactic| monty_arith) => do
  evalTactic (← `(tactic| ennreal_arith))
