/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Copilot AI Assistant
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Basic

/-!
# Fibonacci Numbers

This file contains problems inspired by Project Euler related to Fibonacci numbers.
We prove properties about the famous Fibonacci sequence and solve computational problems.

The Fibonacci sequence is defined as:
- F(0) = 0
- F(1) = 1  
- F(n) = F(n-1) + F(n-2) for n ≥ 2

## Problems Covered

1. **Sum of Even Fibonacci Numbers**: Find the sum of even Fibonacci numbers below a given limit
2. **Fibonacci Divisibility**: Properties of when Fibonacci numbers divide each other
3. **Fibonacci Modular Arithmetic**: Patterns in Fibonacci numbers modulo small integers
-/

namespace ProjectEuler.Fibonacci

open Finset Nat BigOperators

/-- The Fibonacci sequence defined recursively -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Basic properties of Fibonacci numbers -/
theorem fib_zero : fib 0 = 0 := by rfl

theorem fib_one : fib 1 = 1 := by rfl

theorem fib_succ_succ (n : ℕ) : fib (n + 2) = fib (n + 1) + fib n := by rfl

/-- The first few Fibonacci numbers for reference -/
example : fib 2 = 1 := by rfl
example : fib 3 = 2 := by rfl  
example : fib 4 = 3 := by rfl
example : fib 5 = 5 := by rfl
example : fib 6 = 8 := by rfl
example : fib 7 = 13 := by rfl

/-- Fibonacci numbers are non-decreasing -/
theorem fib_mono : ∀ n : ℕ, fib n ≤ fib (n + 1)
  | 0 => by simp [fib_zero, fib_one]
  | 1 => by simp [fib_one, fib]
  | n + 2 => by
    simp only [fib_succ_succ]
    exact Nat.le_add_left (fib (n + 2)) (fib (n + 1))

/-- A Fibonacci number is even if and only if its index is divisible by 3 -/
theorem fib_even_iff_index_mod_three_eq_zero (n : ℕ) : 
    Even (fib n) ↔ n % 3 = 0 := by
  -- Pattern: F(0)=0(even), F(1)=1(odd), F(2)=1(odd), F(3)=2(even), F(4)=3(odd), F(5)=5(odd), F(6)=8(even)...
  -- We can prove this by strong induction on the pattern mod 3
  sorry -- Exercise: prove by induction that F(3k) is even, F(3k+1) and F(3k+2) are odd

/-- Problem 1: Sum of even Fibonacci numbers below a limit
    Inspired by Project Euler Problem 2 -/
def sum_even_fib_below (limit : ℕ) : ℕ :=
  (range limit).filter (fun n => fib n < limit ∧ Even (fib n)) |>.sum fib

/-- The sum of the first few even Fibonacci numbers -/
example : sum_even_fib_below 100 = 44 := by
  -- The even Fibonacci numbers below 100 are: F(3)=2, F(6)=8, F(9)=34
  -- So sum = 2 + 8 + 34 = 44
  unfold sum_even_fib_below
  simp [range, filter]
  -- This would require computational verification
  sorry

/-- Problem 2: Fibonacci numbers grow exponentially -/
theorem fib_grows_exponentially : ∀ n ≥ 5, fib n ≥ 2 ^ (n / 2) := by
  sorry

/-- Problem 3: GCD property of Fibonacci numbers -/
theorem fib_gcd (m n : ℕ) : Nat.gcd (fib m) (fib n) = fib (Nat.gcd m n) := by
  sorry

/-- Problem 4: Fibonacci modulo patterns
    Every third Fibonacci number is even, every fourth is divisible by 3, etc. -/
theorem fib_mod_pattern (n k : ℕ) (hk : k > 0) : 
    (∃ period : ℕ, ∀ i : ℕ, fib (i + period) % k = fib i % k) := by
  sorry

/-- Helper: Check if a number is a Fibonacci number -/
def is_fibonacci (n : ℕ) : Prop := ∃ k : ℕ, fib k = n

instance : DecidablePred is_fibonacci := by
  intro n
  -- We can check up to a reasonable bound since Fibonacci grows exponentially
  sorry

/-- Problem 5: Sum of Fibonacci numbers up to index n -/
def fib_sum (n : ℕ) : ℕ := (range (n + 1)).sum fib

/-- Identity: Sum of first n Fibonacci numbers equals F(n+2) - 1 -/
theorem fib_sum_identity (n : ℕ) : fib_sum n = fib (n + 2) - 1 := by
  induction n with
  | zero => simp [fib_sum, fib_zero, fib]
  | succ n ih =>
    simp [fib_sum, sum_range_succ, ih]
    simp [fib_succ_succ]
    omega

end ProjectEuler.Fibonacci