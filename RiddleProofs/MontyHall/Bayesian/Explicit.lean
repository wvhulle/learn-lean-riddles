import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.Bayesian.Common

open  Door

/-!
# Excplicit Bayesian Monty Hall Analysis

This file demonstrates the superiority of the Bayesian approach to the Monty Hall problem.
Rather than modeling the complex joint distribution, we focus on the unknown (car position)
and use Bayes' theorem to compute posterior probabilities.

**Key insight**: The sample space is just the car position (3 states), not all game configurations (27 states).
-/


theorem prior_uniform (d : Door) : car_prior d = 1/3 := rfl

theorem prior_sums_to_one : car_prior left + car_prior middle + car_prior right = 1 := by
  simp; norm_num

/-!
## Likelihood Function (Host Behavior Model)
-/

-- Scenario: Player chose left, host opened middle
-- Likelihood: P(host opens middle | car at each door, player chose left)
noncomputable def likelihood_player_left_host_middle (car_door : Door) : ℝ :=
  match car_door with
  | left => 1/2    -- Host can choose middle or right, picks randomly
  | middle => 0    -- Host never opens car door
  | right => 1     -- Host forced to open middle (can't open left=player, right=car)

-- Specific likelihood simplification lemmas
@[simp] theorem likelihood_player_left_host_middle_left :
  likelihood_player_left_host_middle left = 1/2 := rfl
@[simp] theorem likelihood_player_left_host_middle_middle :
  likelihood_player_left_host_middle middle = 0 := rfl
@[simp] theorem likelihood_player_left_host_middle_right :
  likelihood_player_left_host_middle right = 1 := rfl

theorem likelihood_nonneg (d : Door) : likelihood_player_left_host_middle d ≥ 0 := by
  cases d <;> simp

/-!
## Evidence (Normalization Factor)
-/

-- Evidence: P(host opens middle | player chose left)
noncomputable def evidence_left_middle : ℝ :=
  car_prior left * likelihood_player_left_host_middle left +
  car_prior middle * likelihood_player_left_host_middle middle +
  car_prior right * likelihood_player_left_host_middle right

theorem evidence_calculation : evidence_left_middle = 1/2 := by
  simp [evidence_left_middle]; norm_num

theorem evidence_positive : evidence_left_middle > 0 := by
  rw [evidence_calculation]; norm_num

/-!
## Posterior Distribution via Bayes' Theorem
-/

-- Posterior: P(car at door | host opened middle, player chose left)
noncomputable def posterior_left_middle (car_door : Door) : ℝ :=
  car_prior car_door * likelihood_player_left_host_middle car_door / evidence_left_middle

-- The main Monty Hall results
theorem posterior_stay : posterior_left_middle left = 1/3 := by
  simp [posterior_left_middle, evidence_calculation]

theorem posterior_switch : posterior_left_middle right = 2/3 := by
  simp [posterior_left_middle, evidence_calculation]; norm_num

theorem posterior_opened_door : posterior_left_middle middle = 0 := by
  simp [posterior_left_middle]

-- Example: Calculate step by step with explicit reasoning
example : posterior_left_middle right = 2/3 := calc
  posterior_left_middle right
    = car_prior right * likelihood_player_left_host_middle right / evidence_left_middle := rfl
  _ = (1/3) * 1 / (1/2) := by simp [evidence_calculation]
  _ = 2/3 := by norm_num

-- Example: Show the Bayesian update intuition
example : posterior_left_middle left + posterior_left_middle right = 1 := calc
  posterior_left_middle left + posterior_left_middle right
    = 1/3 + 2/3 := by rw [posterior_stay, posterior_switch]
  _ = 1 := by norm_num

-- Probabilities sum to 1 (sanity check)
theorem posterior_sums_to_one :
  posterior_left_middle left + posterior_left_middle middle + posterior_left_middle right = 1 := by
  rw [posterior_stay, posterior_switch, posterior_opened_door]
  norm_num

/-!
## General Bayesian Framework
-/



-- General likelihood simplification lemmas for common patterns
@[simp] theorem general_likelihood_host_eq_player (p c : Door) :
  general_likelihood p p c = 0 := by simp only [general_likelihood, if_true]
@[simp] theorem general_likelihood_host_eq_car (p h : Door) :
  general_likelihood p h h = 0 := by simp only [general_likelihood]; split_ifs <;> simp
@[simp] theorem general_likelihood_car_eq_player_ne_host (p h : Door) (hne : h ≠ p) :
  general_likelihood p h p = 1/2 := by simp only [general_likelihood, if_neg hne, if_true]
@[simp] theorem general_likelihood_forced (p h c : Door) (h1 : h ≠ p) (h2 : h ≠ c) (h3 : c ≠ p) :
  general_likelihood p h c = 1 := by simp only [general_likelihood, if_neg h1, if_neg h2, if_neg h3]



-- Example: Let's verify our general framework matches the specific case
example : general_posterior left middle left = posterior_left_middle left := by
  simp [general_posterior, posterior_left_middle, general_evidence, evidence_left_middle]
  norm_num

example : general_posterior left middle right = posterior_left_middle right := by
  simp [general_posterior, posterior_left_middle, general_evidence, evidence_left_middle]
  norm_num


-- First, let's prove that evidence is always 1/2 in valid scenarios
theorem evidence_is_half (player_door host_door : Door) (h : host_door ≠ player_door) :
  general_evidence player_door host_door = 1/2 := by
  fin_cases player_door <;> fin_cases host_door <;> {
    first | exfalso; exact h rfl | {
      simp [general_evidence]; norm_num
    }
  }

-- Example: The intuition behind Bayes' theorem in this context
example : general_evidence left middle = 1/2 := by
  simp [general_evidence]; norm_num

-- The staying probability is always 1/3
theorem staying_probability (player_door host_door : Door) (h : host_door ≠ player_door) :
  general_posterior player_door host_door player_door = 1/3 := by
  fin_cases player_door <;> fin_cases host_door <;> {
    first | exfalso; exact h rfl | {
      simp [general_posterior, general_evidence]; norm_num
    }
  }

-- The switching probability is always 2/3
theorem switching_probability (player_door host_door : Door) (h : host_door ≠ player_door) :
  general_posterior player_door host_door (switch_door player_door host_door) = 2/3 := by
  fin_cases player_door <;> fin_cases host_door <;> {
    first | exfalso; exact h rfl | {
      simp [switch_door, general_posterior, general_evidence]; norm_num
    }
  }



/-!
## Main Results

-/

-- Concrete example showing the simplicity
example : posterior_left_middle left = 1/3 ∧ posterior_left_middle right = 2/3 := by
  exact ⟨posterior_stay, posterior_switch⟩

-- The fundamental insight: Switching doubles your probability of winning
theorem monty_hall_advantage : posterior_left_middle right = 2 * posterior_left_middle left := by
  rw [posterior_switch, posterior_stay]; norm_num

-- Example: Step-by-step calculation showing why switching is better
example : posterior_left_middle right = 2 * posterior_left_middle left := calc
  posterior_left_middle right
    = car_prior right * likelihood_player_left_host_middle right / evidence_left_middle := rfl
  _ = (1/3) * 1 / (1/2) := by simp [evidence_calculation]
  _ = 2/3 := by norm_num
  _ = 2 * (1/3) := by norm_num
  _ = 2 * posterior_left_middle left := by rw [posterior_stay]

-- General switching advantage
theorem general_switching_advantage (player_door host_door : Door) (h : host_door ≠ player_door) :
  general_posterior player_door host_door (switch_door player_door host_door) =
  2 * general_posterior player_door host_door player_door := by
  rw [switching_probability player_door host_door h, staying_probability player_door host_door h]
  norm_num


-- Key theorem: staying always gives 1/3, switching gives 2/3
theorem expl_bay_monty_hall (player_door host_door : Door) (h : host_door ≠ player_door) :
  general_posterior player_door host_door player_door = 1/3 ∧
  general_posterior player_door host_door (switch_door player_door host_door) = 2/3 := by
  exact ⟨staying_probability player_door host_door h, switching_probability player_door host_door h⟩
