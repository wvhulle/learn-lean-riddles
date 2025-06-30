import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.Bayesian.Common
open Finset Door

/-!
This section demonstrates how to formalize the Monty Hall problem using proper probability theory concepts from Mathlib4: Probability Mass Functions (PMF) and conditional probabilities.
-/

open ProbabilityTheory PMF



-- Use Mathlib's uniform distribution instead of manual construction
noncomputable def car_pmf : PMF Door := PMF.uniformOfFintype Door

-- Verify our PMF gives the correct probabilities using Mathlib's theorem
theorem car_pmf_correct (d : Door) : car_pmf d = ENNReal.ofReal (1/3) := by
  simp [car_pmf, PMF.uniformOfFintype_apply]
  simp [Fintype.card, Finset.card, Door.univ_eq]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3)]
  simp

-- Example: Our PMF correctly represents uniform distribution
example : car_pmf left = car_pmf middle := by simp [car_pmf_correct]

example : car_pmf left + car_pmf middle + car_pmf right = 1 := by
  rw [car_pmf_correct, car_pmf_correct, car_pmf_correct]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

-- Convert likelihood functions to ENNReal for PMF operations
noncomputable def likelihood_ennreal (player_door host_door car_door : Door) : ENNReal :=
  ENNReal.ofReal (general_likelihood player_door host_door car_door)

-- Helper lemma for likelihood non-negativity
theorem general_likelihood_nonneg (player_door host_door car_door : Door) :
  general_likelihood player_door host_door car_door >= 0 := by
  simp [general_likelihood]; split_ifs <;> norm_num

-- Evidence calculation using uniform PMF - much simpler!
noncomputable def evidence_pmf_val (player_door host_door : Door) : ENNReal :=
  ∑ car_door, car_pmf car_door * ENNReal.ofReal (general_likelihood player_door host_door car_door)

-- Direct connection to our manual calculation
theorem pmf_equivalence (player_door host_door : Door) :
  evidence_pmf_val player_door host_door = ENNReal.ofReal (general_evidence player_door host_door) := by
  simp only [evidence_pmf_val, general_evidence, car_pmf_correct, car_prior_eval]
  rw [Door.sum_eq]
  -- Use the fact that ENNReal.ofReal is additive and multiplicative for non-negative reals
  have h1 : (0 : ℝ) ≤ 1/3 := by norm_num
  have h2 : general_likelihood player_door host_door left ≥ 0 := general_likelihood_nonneg _ _ _
  have h3 : general_likelihood player_door host_door middle ≥ 0 := general_likelihood_nonneg _ _ _
  have h4 : general_likelihood player_door host_door right ≥ 0 := general_likelihood_nonneg _ _ _
  rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h1]
  rw [← ENNReal.ofReal_add (mul_nonneg h1 h2) (mul_nonneg h1 h3)]
  rw [← ENNReal.ofReal_add (add_nonneg (mul_nonneg h1 h2) (mul_nonneg h1 h3)) (mul_nonneg h1 h4)]
