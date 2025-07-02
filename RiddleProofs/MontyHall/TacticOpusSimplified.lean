/-
This file provides a simplified version of the ENNReal arithmetic tactic.
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Lean Meta Elab Tactic
open ENNReal

namespace ENNRealArith

/-- Simplified tactic for ENNReal arithmetic -/
syntax "ennreal_arith_simplified" : tactic

macro_rules
| `(tactic| ennreal_arith_simplified) => `(tactic| first
  -- === BASIC CASTING PATTERNS ===
  | rw [← Nat.cast_add]
  | rw [← Nat.cast_mul]
  | rw [← Nat.cast_pow]
  | (rw [← Nat.cast_mul, ← Nat.cast_pow])
  | simp

  -- === DIVISION CANCELLATION PATTERNS ===
  -- Direct applications
  | (apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- With commutativity
  | (rw [mul_comm (_ : ENNReal) (_ : ENNReal)]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_comm (_ : ENNReal) (_ : ENNReal)]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])

  -- With cast simplification
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- Cast multiplication patterns with explicit assumption handling
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; rw [ENNReal.mul_div_mul_right]; norm_cast; assumption; simp [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; rw [ENNReal.mul_div_mul_left]; norm_cast; assumption; simp [ENNReal.natCast_ne_top])

  -- === REAL CONVERSION PATTERNS ===
  | (rw [ENNReal.toReal_div]; simp [ENNReal.toReal_natCast])
  | (simp [ENNReal.toReal_div, ENNReal.toReal_natCast])
  | (rw [ENNReal.toReal_eq_toReal_iff]; simp [ENNReal.natCast_ne_top]; ring_nf)

  -- === FALLBACKS ===
  | (norm_cast; ring_nf)
  | norm_cast
  | simp_all
  | ring_nf
  | (simp [ENNReal.natCast_ne_top]; ring_nf))

end ENNRealArith

-- Test suite for the simplified tactic
section TestSuite

example {a b c : ℕ} : (↑a + ↑b : ENNReal) / ↑c = (↑(a + b) : ENNReal) / ↑c := by
  ennreal_arith_simplified

example {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by
  ennreal_arith_simplified

example {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_arith_simplified

example {a b : ℕ} : (↑a : ENNReal) ^ b = ↑(a ^ b) := by
  ennreal_arith_simplified

example {a b : ℕ} : (↑a : ENNReal) - ↑b = ↑(a - b) := by
  ennreal_arith_simplified

example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_arith_simplified

example {a b : ℕ} : ((↑a : ENNReal) / ↑b).toReal = (a : ℝ) / (b : ℝ) := by
  ennreal_arith_simplified

end TestSuite
