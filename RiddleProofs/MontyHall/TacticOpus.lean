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

-- =============================================================================
-- SPECIALIZED SUB-TACTICS FOR ENNREAL ARITHMETIC
-- =============================================================================

/-- Handle basic simp cases and simple identities -/
syntax "ennreal_basic" : tactic

macro_rules
| `(tactic| ennreal_basic) => `(tactic| first
  | simp  -- Handle simple cases that are already simp lemmas
  | (simp [pow_zero, pow_one])  -- Handle a^0 = 1, a^1 = a, etc.
  | norm_cast  -- Standalone casting normalization
)

/-- Handle division by self patterns: a / a = 1 -/
syntax "ennreal_div_self" : tactic

macro_rules
| `(tactic| ennreal_div_self) => `(tactic| first
  | (apply ENNReal.div_self; simp [*]; simp [ENNReal.natCast_ne_top])
  | (apply ENNReal.div_self; simp_all; simp [ENNReal.natCast_ne_top])
  | (apply ENNReal.div_self; simp [Nat.cast_ne_zero]; simp_all; simp [ENNReal.natCast_ne_top])
  | (apply ENNReal.div_self <;> simp_all [ENNReal.natCast_ne_top, Nat.cast_ne_zero])
)

/-- Handle basic casting preservation patterns -/
syntax "ennreal_cast" : tactic

macro_rules
| `(tactic| ennreal_cast) => `(tactic| first
  | rw [← Nat.cast_add]
  | rw [← Nat.cast_mul]
  | rw [← Nat.cast_pow]
  | (rw [← Nat.cast_mul, ← Nat.cast_pow])  -- Combined for complex cases
  | (rw [← Nat.cast_pow]; simp [pow_zero, pow_one])
)

/-- Handle positivity hypotheses: convert 0 < a to a ≠ 0 -/
syntax "ennreal_positivity" : tactic

macro_rules
| `(tactic| ennreal_positivity) => `(tactic| first
  | simp [ne_of_gt]
  | simp [ne_of_gt]; simp_all
  | (apply ne_of_gt; assumption)
  | (exact ne_of_gt (by assumption))
  | linarith
  | omega
)

/-- Handle multiplication cancellation: a * b / b = a -/
syntax "ennreal_mul_cancel" : tactic

macro_rules
| `(tactic| ennreal_mul_cancel) => `(tactic| first
  | (rw [ENNReal.mul_div_cancel_left] <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [ENNReal.mul_div_cancel_right] <;> simp_all [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_cancel_left <;> simp_all [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_cancel_right <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_div_cancel_left] <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_div_cancel_right] <;> simp_all [ENNReal.natCast_ne_top])
  | (apply mul_div_cancel_left <;> simp_all [ENNReal.natCast_ne_top])
  | (apply mul_div_cancel_right <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_comm]; rw [mul_div_cancel_left] <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_comm]; apply mul_div_cancel_left <;> simp_all [ENNReal.natCast_ne_top])
)

/-- Handle division cancellation: (a * c) / (b * c) = a / b -/
syntax "ennreal_div_cancel" : tactic

macro_rules
| `(tactic| ennreal_div_cancel) => `(tactic| first
  -- EXACT PATTERN from ennreal_div_cancel_mul manual proof: ↑(a * c) / ↑(b * c) = ↑a / ↑b with hc : c ≠ 0
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; exact Nat.cast_ne_zero.mpr ‹_›; exact ENNReal.natCast_ne_top _)
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; apply Nat.cast_ne_zero.mpr; assumption; exact ENNReal.natCast_ne_top _)
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; exact Nat.cast_ne_zero.mpr (by assumption); exact ENNReal.natCast_ne_top _)

  -- NEW: Handle the pre-simplified case ↑a * ↑c / (↑b * ↑c) = ↑a / ↑b directly
  | (apply ENNReal.mul_div_mul_right; exact Nat.cast_ne_zero.mpr ‹_›; exact ENNReal.natCast_ne_top _)
  | (apply ENNReal.mul_div_mul_right; exact Nat.cast_ne_zero.mpr (by assumption); exact ENNReal.natCast_ne_top _)

  -- EXACT PATTERN from manual proof discovery: ↑(a * c) / ↑(b * c) = ↑a / ↑b with 0 < c
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; exact Nat.cast_ne_zero.mpr (ne_of_gt (by assumption)); exact ENNReal.natCast_ne_top _)

  -- Handle case where hypothesis is directly available in context as c ≠ 0
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; exact Nat.cast_ne_zero.mpr (by assumption); exact ENNReal.natCast_ne_top _)
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; simp [Nat.cast_ne_zero]; exact ENNReal.natCast_ne_top _)

  -- KEY PATTERN: Handle ↑(a * c) / ↑(b * c) = ↑a / ↑b with positivity hypothesis 0 < c
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; exact ne_of_gt (by assumption); simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left; exact ne_of_gt (by assumption); simp [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_right; exact ne_of_gt (by assumption); simp [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_left; exact ne_of_gt (by assumption); simp [ENNReal.natCast_ne_top])

  -- Handle case where hypothesis is directly available in context as c ≠ 0
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; assumption; simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left; assumption; simp [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_right; assumption; simp [ENNReal.natCast_ne_top])
  | (rw [Nat.cast_mul, Nat.cast_mul]; apply ENNReal.mul_div_mul_left; assumption; simp [ENNReal.natCast_ne_top])

  -- Direct patterns for ↑a * ↑c / (↑b * ↑c) = ↑a / ↑b (most common case)
  | (apply ENNReal.mul_div_mul_right; simp [Nat.cast_ne_zero]; simp_all; simp [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_mul_left; simp [Nat.cast_ne_zero]; simp_all; simp [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top, Nat.cast_ne_zero])
  | (apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top, Nat.cast_ne_zero])

  -- Handle more complex positivity patterns
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; apply ne_of_gt; assumption; simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left; simp [ne_of_gt]; simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- Omega and linarith based patterns
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; simp [Nat.cast_ne_zero]; omega; simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; linarith; simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_right; omega; simp [ENNReal.natCast_ne_top])
  | (simp only [Nat.cast_mul]; apply ENNReal.mul_div_mul_left; omega; simp [ENNReal.natCast_ne_top])

  -- Direct application with hypotheses available in context
  | (apply ENNReal.mul_div_mul_right; simp [*]; simp [ENNReal.natCast_ne_top])
  | (apply ENNReal.mul_div_mul_left; simp [*]; simp [ENNReal.natCast_ne_top])

  -- Handle patterns like ↑a * ↑c / (↑b * ↑c) = ↑a / ↑b with rearrangement
  | (rw [← Nat.cast_mul, ← Nat.cast_mul]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [← Nat.cast_mul, ← Nat.cast_mul]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])

  -- With commutativity adjustments
  | (rw [mul_comm (_ : ENNReal) (_ : ENNReal)]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])
  | (rw [mul_comm (_ : ENNReal) (_ : ENNReal)]; apply ENNReal.mul_div_mul_right <;> simp_all [ENNReal.natCast_ne_top])

  -- Complex pattern for reordered multiplication: a * c / (c * b) = a / b
  | (rw [mul_comm (↑a) (↑c), mul_comm (↑b) (↑c)]; apply ENNReal.mul_div_mul_left <;> simp_all [ENNReal.natCast_ne_top])
)

/-- Handle reciprocal patterns: (1 / a) * a = 1 -/
syntax "ennreal_reciprocal" : tactic

macro_rules
| `(tactic| ennreal_reciprocal) => `(tactic| first
  | (rw [one_div]; apply ENNReal.inv_mul_cancel <;> simp_all [ENNReal.natCast_ne_top, ENNReal.coe_ne_top])
  | (rw [one_div]; exact ENNReal.inv_mul_cancel (by simp_all) (by simp_all [ENNReal.natCast_ne_top, ENNReal.coe_ne_top]))
)

/-- Handle real conversions: toReal/ofReal patterns -/
syntax "ennreal_real" : tactic

macro_rules
| `(tactic| ennreal_real) => `(tactic| first
  | (rw [ENNReal.toReal_div]; simp [ENNReal.toReal_natCast])
  | (simp [ENNReal.toReal_div, ENNReal.toReal_natCast])
  | (rw [ENNReal.toReal_eq_toReal_iff]; simp [ENNReal.natCast_ne_top]; ring_nf)
  | (rw [ENNReal.ofReal_toReal]; simp [*])
  | (simp [ENNReal.toReal_div, ENNReal.toReal_ofReal]; ring_nf)
)

/-- Handle field simplification for complex expressions -/
syntax "ennreal_field" : tactic

macro_rules
| `(tactic| ennreal_field) => `(tactic| first
  | (field_simp [ENNReal.natCast_ne_top]; ring_nf; norm_cast)
  | (field_simp [ENNReal.natCast_ne_top]; simp_all)
)

/-- Fallback tactics for general algebraic simplification -/
syntax "ennreal_fallback" : tactic

macro_rules
| `(tactic| ennreal_fallback) => `(tactic| first
  | (norm_cast; ring_nf)  -- For mixed casting patterns
  | simp_all  -- Handle complex casting with context
  | ring_nf    -- Pure algebraic normalization
  | (simp [ENNReal.natCast_ne_top]; ring_nf)  -- Final fallback with ENNReal knowledge
)

-- =============================================================================
-- SMART HEURISTIC-BASED MAIN TACTIC
-- =============================================================================

/-- Main tactic for ENNReal arithmetic with intelligent sub-tactic selection -/
syntax "ennreal_arith" : tactic

macro_rules
| `(tactic| ennreal_arith) => `(tactic| first
  -- PRIORITY 1: Division cancellation (most complex, should be tried first)
  -- Handles: ↑(a * c) / ↑(b * c) = ↑a / ↑b and ↑a * ↑c / (↑b * ↑c) = ↑a / ↑b
  | ennreal_div_cancel

  -- PRIORITY 2: Division by self (a / a = 1)
  -- Must come before basic simp which might interfere
  | ennreal_div_self

  -- PRIORITY 3: Multiplication cancellation (a * b / b = a)
  -- Common pattern that needs specific handling
  | ennreal_mul_cancel

  -- PRIORITY 4: Reciprocal patterns (1 / a * a = 1)
  -- Specific pattern that needs early handling
  | ennreal_reciprocal

  -- PRIORITY 5: Real conversions (toReal/ofReal)
  -- Specific domain conversions
  | ennreal_real

  -- PRIORITY 6: Casting preservation (↑(a + b) = ↑a + ↑b)
  -- Basic casting operations
  | ennreal_cast

  -- PRIORITY 7: Field operations (complex algebraic simplification)
  -- For more sophisticated algebraic manipulations
  | ennreal_field

  -- PRIORITY 8: Basic operations (simple simp cases)
  -- General simplification that works for many cases
  | ennreal_basic

  -- PRIORITY 9: Positivity handling (convert 0 < a to a ≠ 0)
  -- Only after other patterns have been tried to avoid interference
  | ennreal_positivity

  -- PRIORITY 10: General fallbacks (last resort)
  -- When all else fails
  | ennreal_fallback
)


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

-- =============================================================================
-- LEVEL 1: TRIVIAL CONSTANT CASES (simplest possible)
-- =============================================================================

lemma ennreal_zero_cast : (↑0 : ENNReal) = 0 := by
  ennreal_arith

lemma ennreal_one_cast : (↑1 : ENNReal) = 1 := by
  ennreal_arith

lemma ennreal_two_cast : (↑2 : ENNReal) = 2 := by
  ennreal_arith

-- =============================================================================
-- LEVEL 2: BASIC IDENTITY OPERATIONS (with 0 and 1)
-- =============================================================================

lemma ennreal_add_zero {a : ℕ} : (↑a : ENNReal) + 0 = ↑a := by
  ennreal_arith

lemma ennreal_zero_add {a : ℕ} : 0 + (↑a : ENNReal) = ↑a := by
  ennreal_arith

lemma ennreal_mul_one {a : ℕ} : (↑a : ENNReal) * 1 = ↑a := by
  ennreal_arith

lemma ennreal_one_mul {a : ℕ} : 1 * (↑a : ENNReal) = ↑a := by
  ennreal_arith

lemma ennreal_mul_zero {a : ℕ} : (↑a : ENNReal) * 0 = 0 := by
  ennreal_arith

lemma ennreal_zero_mul {a : ℕ} : 0 * (↑a : ENNReal) = 0 := by
  ennreal_arith

lemma ennreal_div_one {a : ℕ} : (↑a : ENNReal) / 1 = ↑a := by
  ennreal_arith

lemma ennreal_zero_div {a : ℕ} : (0 : ENNReal) / ↑a = 0 := by
  ennreal_arith

-- =============================================================================
-- LEVEL 3: BASIC POWER OPERATIONS
-- =============================================================================

lemma ennreal_pow_zero {a : ℕ} : (↑a : ENNReal) ^ 0 = 1 := by
  ennreal_arith

lemma ennreal_pow_one {a : ℕ} : (↑a : ENNReal) ^ 1 = ↑a := by
  ennreal_arith

lemma ennreal_one_pow {n : ℕ} : (1 : ENNReal) ^ n = 1 := by
  ennreal_arith

-- =============================================================================
-- LEVEL 4: CONCRETE ARITHMETIC (specific numbers)
-- =============================================================================

lemma ennreal_add_two_three : (↑2 : ENNReal) + ↑3 = ↑5 := by
  ennreal_arith

lemma ennreal_mul_two_three : (↑2 : ENNReal) * ↑3 = ↑6 := by
  ennreal_arith

lemma ennreal_pow_two_three : (↑2 : ENNReal) ^ 3 = ↑8 := by
  ennreal_arith

lemma ennreal_sub_five_three : (↑5 : ENNReal) - ↑3 = ↑2 := by
  ennreal_arith

-- =============================================================================
-- LEVEL 5: BASIC CASTING PRESERVATION (general forms)
-- =============================================================================

lemma ennreal_mul_cast {a b : ℕ} : (↑a : ENNReal) * (↑b : ENNReal) = ↑(a * b : ℕ) := by
  ennreal_arith

lemma ennreal_pow_cast {a b : ℕ} : (↑a : ENNReal) ^ b = ↑(a ^ b) := by
  ennreal_arith

lemma ennreal_sub_cast {a b : ℕ} : (↑a : ENNReal) - ↑b = ↑(a - b) := by
  ennreal_arith

-- =============================================================================
-- LEVEL 6: CASTING PRESERVATION (specific examples)
-- =============================================================================

lemma ennreal_cast_add_specific : (↑(2 + 3) : ENNReal) = ↑2 + ↑3 := by
  ennreal_arith

lemma ennreal_cast_mul_specific : (↑(2 * 3) : ENNReal) = ↑2 * ↑3 := by
  ennreal_arith

lemma ennreal_cast_pow_specific : (↑(2 ^ 3) : ENNReal) = ↑2 ^ 3 := by
  ennreal_arith

-- =============================================================================
-- LEVEL 7: TRIVIAL DIVISION CASES
-- =============================================================================

lemma ennreal_div_cast {a b : ℕ} : (↑a : ENNReal) / (↑b : ENNReal) = (↑a : ENNReal) / (↑b : ENNReal) := by
  ennreal_arith

-- =============================================================================
-- LEVEL 8: BASIC DIVISION WITH FRACTIONS
-- =============================================================================

lemma ennreal_add_div_cast {a b c : ℕ} : (↑a + ↑b : ENNReal) / ↑c = (↑(a + b) : ENNReal) / ↑c := by
  ennreal_arith

lemma ennreal_toReal_div_nat {a b : ℕ} : ((↑a : ENNReal) / ↑b).toReal = (a : ℝ) / (b : ℝ) := by
  ennreal_arith

-- =============================================================================
-- LEVEL 9: DIVISION WITH NONZERO HYPOTHESES (requires manual proofs)
-- =============================================================================

lemma ennreal_div_same {a : ℕ} (ha : a ≠ 0) : (↑a : ENNReal) / ↑a = 1 := by
  ennreal_arith


-- =============================================================================
-- LEVEL 10: MULTIPLICATION CANCELLATION PATTERNS (requires manual proofs)
-- =============================================================================

lemma ennreal_div_cancel_mul {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_arith


-- Test the exact same pattern but with c ≠ 0 hypothesis to debug tactic
lemma test_div_cancel_with_ne_zero {a b c : ℕ} (hc : c ≠ 0) : (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  ennreal_arith


-- =============================================================================
-- LEVEL 11: RECIPROCAL MULTIPLICATION (requires manual proofs)
-- =============================================================================

lemma ennreal_one_div_self {a : ℕ} (ha : a ≠ 0) : (1 / (↑a : ENNReal)) * ↑a = 1 := by
  rw [one_div]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr ha) (ENNReal.natCast_ne_top a)


-- =============================================================================
-- LEVEL 12: ARITHMETIC.LEAN PATTERNS - Test case 1
-- =============================================================================

-- Test: ENNReal.div_mul_cancel_nat_cast pattern with positivity hypothesis
lemma test_div_mul_cancel_nat_cast {a b c : ℕ} (hc_pos : 0 < c) :
  (↑(a * c) : ENNReal) / (↑(b * c)) = (↑a) / (↑b) := by
  simp only [Nat.cast_mul]
  apply ENNReal.mul_div_mul_right
  · exact Nat.cast_ne_zero.mpr (ne_of_gt hc_pos)
  · exact ENNReal.natCast_ne_top c




end TestSuite
