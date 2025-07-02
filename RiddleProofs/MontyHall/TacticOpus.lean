/-
This file provides tactics for working with ENNReal (extended non-negative real) arithmetic.
The tactics are designed to simplify common ENNReal arithmetic proofs by automatically handling
casting between natural numbers and ENNReal values, and by leveraging the toReal conversion.
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

/-- Main tactic for ENNReal arithmetic -/
syntax "ennreal_arith" : tactic

macro_rules
| `(tactic| ennreal_arith) => `(tactic| first
  -- === SPECIFIC PATTERN FOR CAST MULTIPLICATION ===
  -- Handle ↑(a * c) / ↑(b * c) = ↑a / ↑b pattern first (most specific)
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])

  -- === BASIC CASTING PATTERNS ===
  -- Handle basic nat cast conversions (most common patterns first)
  | rw [← Nat.cast_add]
  | rw [← Nat.cast_mul]
  | rw [← Nat.cast_pow]
  | (rw [← Nat.cast_mul, ← Nat.cast_pow])  -- Combined for complex cases
  | simp  -- Handle simple cases that are already simp lemmas

  -- === DIVISION CANCELLATION PATTERNS ===
  -- Direct applications (try exact matches first)
  | (apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- For cast multiplication patterns: ↑(a * c) / ↑(b * c) = ↑a / ↑b
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- With commutativity adjustments
  | (rw [mul_comm (_ : ENNReal) (_ : ENNReal)]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_comm (_ : ENNReal) (_ : ENNReal)]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])

  -- With cast simplification first
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- Complex pattern for reordered multiplication: a * c / (c * b) = a / b
  | (rw [mul_comm a c, mul_comm b c]; exact ENNReal.mul_div_mul_left (a : ENNReal) (b : ENNReal) (by simp only [ne_eq, Nat.cast_eq_zero]; assumption) (ENNReal.natCast_ne_top c))

  -- === REAL CONVERSION PATTERNS ===
  -- toReal/ofReal conversions
  | (rw [ENNReal.toReal_div]; simp [ENNReal.toReal_natCast])
  | (simp [ENNReal.toReal_div, ENNReal.toReal_natCast])
  | (rw [ENNReal.toReal_eq_toReal_iff]; simp [ENNReal.natCast_ne_top]; ring_nf)
  | (rw [ENNReal.ofReal_toReal]; simp [*])
  | (simp [ENNReal.toReal_div, ENNReal.toReal_ofReal]; ring_nf)

  -- === FIELD AND ALGEBRAIC SIMPLIFICATION ===
  -- Field simplification for complex rational expressions
  | (field_simp; ring_nf; rw [← Nat.cast_mul])
  | (field_simp; simp [ENNReal.natCast_ne_top]; ring_nf)

  -- === COMPREHENSIVE FALLBACKS ===
  -- Progressive fallback tactics (from specific to general)
  | (norm_cast; ring_nf)  -- For mixed casting patterns
  | norm_cast  -- Standalone casting normalization
  | simp_all  -- Handle complex casting with context
  | ring_nf    -- Pure algebraic normalization
  | (simp [ENNReal.natCast_ne_top]; ring_nf))  -- Final fallback with ENNReal knowledge


/-- Variant that tries to automatically prove finiteness conditions -/
syntax "ennreal_arith!" : tactic

macro_rules
| `(tactic| ennreal_arith!) => `(tactic| first
  | ennreal_arith
  | (simp [ENNReal.natCast_ne_top, ENNReal.toReal_natCast, ENNReal.ofReal_toReal]; ring_nf)
  | (simp [ENNReal.natCast_ne_top, ENNReal.toReal_natCast, ENNReal.ofReal_toReal]; norm_cast; omega)
  | (simp [ENNReal.natCast_ne_top, ENNReal.toReal_natCast, ENNReal.ofReal_toReal]; linarith))


end ENNRealArith

-- =============================================================================
-- TEST SUITE: Progressive ENNReal Arithmetic Examples
-- =============================================================================

section TestSuite

-- Test 1: Basic Addition (already working)
example {a b c : ℕ} : (↑a + ↑b : ENNReal) / ↑c = (↑(a + b) : ENNReal) / ↑c := by
  ennreal_arith

example {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by
  ennreal_arith

example {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_arith

example {a b : ℕ} : (↑a : ENNReal) ^ b = ↑(a ^ b) := by
  ennreal_arith

example {a b : ℕ} : (↑a : ENNReal) - ↑b = ↑(a - b) := by
  ennreal_arith

example {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_arith


example {a b : ℕ} : ((↑a : ENNReal) / ↑b).toReal = (a : ℝ) / (b : ℝ) := by
  ennreal_arith



end TestSuite
