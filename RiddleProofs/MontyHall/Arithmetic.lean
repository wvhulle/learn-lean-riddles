import Mathlib.Probability.Notation
import Mathlib.Tactic.Lift
import Mathlib.Tactic.CancelDenoms
import Mathlib.Tactic.NormNum
import Mathlib.Data.ENNReal.Basic
-- import Mathlib.Data.ENNReal
import RiddleProofs.MontyHall.TacticOpus

open ENNReal
open Lean Meta Elab Tactic


-- Simplify fraction by canceling common factor in numerator and denominator
@[simp] lemma ENNReal.div_mul_cancel_nat_cast {a b c : ℕ} {hc_pos : 0 < c} :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_arith

-- Inverse of division times fraction equals multiplication
@[simp] lemma ENNReal.inv_div_mul_div {a b c : ℕ} :
  (1 / (↑a : ENNReal))⁻¹ * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑(a * b) : ENNReal) / (↑c : ENNReal) := by
  ennreal_arith

-- ofReal distributes over division for positive denominators
@[simp] lemma ENNReal.ofReal_div_pos {a b : ℝ} {hb : 0 < b} :
  ENNReal.ofReal (a / b) = ENNReal.ofReal a / ENNReal.ofReal b :=
  ENNReal.ofReal_div_of_pos hb

-- Convert inverse of real division back to ENNReal
@[simp] lemma ENNReal.ofReal_inv_div_toReal {a : ENNReal} {ha_ne_top: a ≠ ⊤} :
  ENNReal.ofReal ((1 / ENNReal.toReal a)⁻¹) = a := by
  ennreal_arith

-- Convert ENNReal division to real division and back
lemma ENNReal.div_eq_ofReal_div {a b : ENNReal} (hb_ne_zero: b ≠ 0) (ha_ne_top: a ≠ ⊤):
  a / b = ENNReal.ofReal (ENNReal.toReal a / ENNReal.toReal b) := by
  ennreal_arith

-- Helper lemma for converting multiplication equality to division equality
private lemma div_eq_div_of_nat_mul_eq {a b c d e : ℕ} (h : a * b * e = d * c)
  (hc_pos : 0 < c) (he_pos : 0 < e) :
  (↑(a * b) : ENNReal) / (↑c : ENNReal) = (↑d : ENNReal) / (↑e : ENNReal) := by
  ennreal_arith
  rw [mul_comm, mul_assoc, mul_comm e, ← mul_assoc]
  exact h

-- Simplify multiplication with fraction using proportional equality
@[simp] lemma ENNReal.mul_div_eq_div_of_mul_eq {a b c d e : ℕ} (h : a * b * e = d * c)
  (hc_pos : 0 < c) (he_pos : 0 < e) :
  (↑a : ENNReal) * ((↑b : ENNReal) / (↑c : ENNReal)) = (↑d : ENNReal) / (↑e : ENNReal) := by
  ennreal_arith
  rw [← Nat.cast_mul, mul_comm, h]
