/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Copilot AI Assistant
-/
import Mathlib.Data.Nat.Divisors
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Range

/-!
# Perfect Numbers

This file contains problems inspired by Project Euler related to perfect numbers.
A perfect number is a positive integer that is equal to the sum of its proper positive divisors.

## Definition and Examples

Perfect numbers are rare and beautiful mathematical objects:
- 6 = 1 + 2 + 3 (first perfect number)
- 28 = 1 + 2 + 4 + 7 + 14 (second perfect number)

## Problems Covered

1. **Definition and Basic Properties**: Formal definition and examples
2. **Perfect Number Recognition**: Algorithm to check if a number is perfect
3. **Connection to Mersenne Primes**: Euclid-Euler theorem about even perfect numbers
4. **Sum of Perfect Numbers**: Finding sums of perfect numbers below limits
-/

namespace ProjectEuler.PerfectNumbers

open Finset Nat BigOperators

/-- A perfect number is equal to the sum of its proper divisors -/
def is_perfect (n : ℕ) : Prop :=
  n > 0 ∧ (n.divisors.filter (· < n)).sum id = n

/-- Alternative definition using the sum of all divisors -/
def is_perfect_alt (n : ℕ) : Prop :=
  n > 0 ∧ n.divisors.sum id = 2 * n

/-- The two definitions are equivalent -/
theorem is_perfect_iff_alt (n : ℕ) : is_perfect n ↔ is_perfect_alt n := by
  simp only [is_perfect, is_perfect_alt]
  constructor
  · intro ⟨hn_pos, h⟩
    constructor
    · exact hn_pos
    · rw [← h]
      have : n.divisors = insert n (n.divisors.filter (· < n)) := by
        rw [Finset.insert_eq, Finset.union_filter_neg]
        simp [Nat.mem_divisors, hn_pos]
      rw [this, sum_insert]
      · ring
      · simp [Nat.lt_irrefl]
  · intro ⟨hn_pos, h⟩
    constructor
    · exact hn_pos
    · have : n.divisors.sum id = n + (n.divisors.filter (· < n)).sum id := by
        rw [← sum_union (disjoint_filter.mpr fun x hx => (not_lt.mpr (le_of_mem_divisors hx hn_pos)))]
        congr 1
        ext x
        simp [mem_filter, mem_singleton, Nat.mem_divisors, hn_pos]
        constructor
        · intro h
          cases' eq_or_lt_of_le (le_of_mem_divisors h hn_pos) with h_eq h_lt
          · left; exact h_eq.symm
          · right; exact h_lt
        · intro h
          cases h with
          | inl h => rw [← h]; exact dvd_refl n
          | inr h => exact mem_divisors.mp ⟨mem_filter.mp h |>.1, hn_pos⟩
      rw [h] at this
      linarith

/-- Perfect numbers are decidable -/
instance : DecidablePred is_perfect := by
  intro n
  simp only [is_perfect]
  infer_instance

/-- The first perfect number is 6 -/
example : is_perfect 6 := by
  simp [is_perfect]
  norm_num
  simp [Nat.divisors]
  decide

/-- The second perfect number is 28 -/
example : is_perfect 28 := by
  simp [is_perfect]
  norm_num
  simp [Nat.divisors]
  decide

/-- 12 is not perfect (it's abundant) -/
example : ¬is_perfect 12 := by
  simp [is_perfect]
  norm_num
  simp [Nat.divisors]
  decide

/-- Find all perfect numbers below a given limit -/
def perfect_numbers_below (limit : ℕ) : Finset ℕ :=
  (range limit).filter is_perfect

/-- The first two perfect numbers are 6 and 28 -/
example : perfect_numbers_below 100 = {6, 28} := by
  ext n
  simp [perfect_numbers_below, mem_filter, mem_range]
  constructor
  · intro ⟨h_lt, h_perf⟩
    interval_cases n <;> simp [is_perfect] <;> norm_num <;> simp [Nat.divisors] <;> decide
  · intro h
    cases h with
    | inl h => simp [h]; exact ⟨by norm_num, by simp [is_perfect]; norm_num; simp [Nat.divisors]; decide⟩
    | inr h => simp [h]; exact ⟨by norm_num, by simp [is_perfect]; norm_num; simp [Nat.divisors]; decide⟩

/-- Sum of perfect numbers below a limit -/
def sum_perfect_below (limit : ℕ) : ℕ :=
  (perfect_numbers_below limit).sum id

/-- The sum of perfect numbers below 100 -/
example : sum_perfect_below 100 = 34 := by
  simp [sum_perfect_below, perfect_numbers_below]
  norm_num

/-- Connection to Mersenne primes: If 2^p - 1 is prime, then 2^(p-1) * (2^p - 1) is perfect -/
def mersenne_form (p : ℕ) : ℕ := 2^(p-1) * (2^p - 1)

/-- Euclid's theorem: Numbers of the form 2^(p-1) * (2^p - 1) where 2^p - 1 is prime are perfect -/
theorem euclid_perfect (p : ℕ) (hp : p ≥ 2) (h_mersenne_prime : Nat.Prime (2^p - 1)) :
    is_perfect (mersenne_form p) := by
  sorry -- This requires more advanced number theory

/-- The converse (Euler's theorem): Every even perfect number has this form -/
theorem euler_perfect (n : ℕ) (hn_even : Even n) (hn_perfect : is_perfect n) :
    ∃ p : ℕ, p ≥ 2 ∧ Nat.Prime (2^p - 1) ∧ n = mersenne_form p := by
  sorry -- This is quite advanced

/-- A computational check: the first few perfect numbers have Mersenne form -/
example : mersenne_form 2 = 6 := by norm_num [mersenne_form]
example : mersenne_form 3 = 28 := by norm_num [mersenne_form]

/-- Helper: Sum of proper divisors function -/
def sum_proper_divisors (n : ℕ) : ℕ :=
  if n = 0 then 0 else (n.divisors.filter (· < n)).sum id

/-- Abundant numbers: sum of proper divisors exceeds the number -/
def is_abundant (n : ℕ) : Prop := n > 0 ∧ sum_proper_divisors n > n

/-- Deficient numbers: sum of proper divisors is less than the number -/
def is_deficient (n : ℕ) : Prop := n > 0 ∧ sum_proper_divisors n < n

/-- Every positive integer is exactly one of perfect, abundant, or deficient -/
theorem trichotomy (n : ℕ) (hn : n > 0) : 
    is_perfect n ∨ is_abundant n ∨ is_deficient n := by
  simp [is_perfect, is_abundant, is_deficient, sum_proper_divisors, hn]
  omega

/-- Perfect numbers are neither abundant nor deficient -/
theorem perfect_not_abundant_not_deficient (n : ℕ) (hn : is_perfect n) :
    ¬is_abundant n ∧ ¬is_deficient n := by
  simp [is_perfect, is_abundant, is_deficient, sum_proper_divisors] at *
  exact ⟨not_lt.mpr (le_of_eq hn.2), not_gt.mpr (le_of_eq hn.2.symm)⟩

end ProjectEuler.PerfectNumbers