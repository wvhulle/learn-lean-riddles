import Mathlib.Probability.Distributions.Uniform
import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.Bayesian.Common

open Door

/-!
# Formal Bayesian Monty Hall Analysis

This section demonstrates how to formalize the Monty Hall problem using proper probability theory concepts from Mathlib4: Probability Mass Functions (PMF) and conditional probabilities.
-/


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

-- Evidence calculation using uniform PMF - much simpler!
noncomputable def evidence_pmf_val (player_door host_door : Door) : ENNReal :=
  ∑ car_door, car_pmf car_door * ENNReal.ofReal (general_likelihood player_door host_door car_door)

-- Posterior probability using Bayes' theorem with PMF
noncomputable def posterior_pmf (player_door host_door car_door : Door) : ENNReal :=
  if evidence_pmf_val player_door host_door = 0 then 0
  else (car_pmf car_door * ENNReal.ofReal (general_likelihood player_door host_door car_door)) /
       evidence_pmf_val player_door host_door
