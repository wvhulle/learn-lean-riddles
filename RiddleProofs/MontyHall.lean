import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset

/-!
# The Monty Hall Problem - Bayesian Approach

This file demonstrates the superiority of the Bayesian approach to the Monty Hall problem.
Rather than modeling the complex joint distribution, we focus on the unknown (car position)
and use Bayes' theorem to compute posterior probabilities.

**Key insight**: The sample space is just the car position (3 states), not all game configurations (27 states).
-/

inductive Door : Type
| left | middle | right
deriving DecidableEq, Repr

-- Manual Fintype instance for Door
instance : Fintype Door := {
  elems := {Door.left, Door.middle, Door.right}
  complete := fun x => by cases x <;> simp
}

open Door

/-!
## Section 1: Prior Distribution (Before Any Evidence)
-/

-- Prior: Each door equally likely to have the car
noncomputable def car_prior : Door → ℝ := fun _ => 1/3

theorem prior_uniform (d : Door) : car_prior d = 1/3 := rfl

theorem prior_sums_to_one : car_prior left + car_prior middle + car_prior right = 1 := by
  simp [car_prior]; norm_num

/-!
## Section 2: Likelihood Function (Host Behavior Model)
-/

-- Scenario: Player chose left, host opened middle
-- Likelihood: P(host opens middle | car at each door, player chose left)
noncomputable def likelihood_player_left_host_middle (car_door : Door) : ℝ :=
  match car_door with
  | left => 1/2    -- Host can choose middle or right, picks randomly
  | middle => 0    -- Host never opens car door
  | right => 1     -- Host forced to open middle (can't open left=player, right=car)

theorem likelihood_nonneg (d : Door) : likelihood_player_left_host_middle d ≥ 0 := by
  cases d <;> simp [likelihood_player_left_host_middle]

/-!
## Section 3: Evidence (Normalization Factor)
-/

-- Evidence: P(host opens middle | player chose left)
noncomputable def evidence_left_middle : ℝ :=
  car_prior left * likelihood_player_left_host_middle left +
  car_prior middle * likelihood_player_left_host_middle middle +
  car_prior right * likelihood_player_left_host_middle right

theorem evidence_calculation : evidence_left_middle = 1/2 := by
  simp [evidence_left_middle, car_prior, likelihood_player_left_host_middle]
  norm_num

theorem evidence_positive : evidence_left_middle > 0 := by
  rw [evidence_calculation]; norm_num

/-!
## Section 4: Posterior Distribution via Bayes' Theorem
-/

-- Posterior: P(car at door | host opened middle, player chose left)
noncomputable def posterior_left_middle (car_door : Door) : ℝ :=
  car_prior car_door * likelihood_player_left_host_middle car_door / evidence_left_middle

-- The main Monty Hall results
theorem posterior_stay : posterior_left_middle left = 1/3 := by
  simp [posterior_left_middle, car_prior, likelihood_player_left_host_middle, evidence_calculation]

theorem posterior_switch : posterior_left_middle right = 2/3 := by
  simp [posterior_left_middle, car_prior, likelihood_player_left_host_middle, evidence_calculation]
  norm_num

theorem posterior_opened_door : posterior_left_middle middle = 0 := by
  simp [posterior_left_middle, likelihood_player_left_host_middle]

-- Probabilities sum to 1 (sanity check)
theorem posterior_sums_to_one :
  posterior_left_middle left + posterior_left_middle middle + posterior_left_middle right = 1 := by
  rw [posterior_stay, posterior_switch, posterior_opened_door]
  norm_num

/-!
## Section 5: General Bayesian Framework
-/

-- General likelihood function for any scenario
noncomputable def general_likelihood (player_door host_door car_door : Door) : ℝ :=
  if host_door = player_door then 0  -- Invalid: host never opens player's door
  else if host_door = car_door then 0  -- Host never opens car door
  else if car_door = player_door then 1/2  -- Host has 2 choices
  else 1  -- Host forced to open this door

-- General evidence function
noncomputable def general_evidence (player_door host_door : Door) : ℝ :=
  car_prior left * general_likelihood player_door host_door left +
  car_prior middle * general_likelihood player_door host_door middle +
  car_prior right * general_likelihood player_door host_door right

-- General posterior via Bayes' theorem
noncomputable def general_posterior (player_door host_door car_door : Door) : ℝ :=
  if general_evidence player_door host_door = 0 then 0
  else car_prior car_door * general_likelihood player_door host_door car_door / general_evidence player_door host_door

-- Helper lemmas for computing posteriors in specific scenarios

lemma posterior_stay_left_middle : general_posterior left middle left = 1/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_switch_left_middle : general_posterior left middle right = 2/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_stay_left_right : general_posterior left right left = 1/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_switch_left_right : general_posterior left right middle = 2/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_stay_middle_left : general_posterior middle left middle = 1/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_switch_middle_left : general_posterior middle left right = 2/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_stay_middle_right : general_posterior middle right middle = 1/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_switch_middle_right : general_posterior middle right left = 2/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_stay_right_left : general_posterior right left right = 1/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_switch_right_left : general_posterior right left middle = 2/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_stay_right_middle : general_posterior right middle right = 1/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

lemma posterior_switch_right_middle : general_posterior right middle left = 2/3 := by
  simp [general_posterior, general_evidence, general_likelihood, car_prior]
  norm_num

-- Key theorem: staying always gives 1/3, switching gives 2/3
-- This is the core mathematical result that makes the Bayesian approach superior
theorem general_monty_hall (player_door host_door : Door) (h : host_door ≠ player_door) :
  let switch_door := if player_door ≠ left ∧ host_door ≠ left then left
                     else if player_door ≠ middle ∧ host_door ≠ middle then middle
                     else right
  general_posterior player_door host_door player_door = 1/3 ∧
  general_posterior player_door host_door switch_door = 2/3 := by
  -- Enumerate all 6 valid cases explicitly
  constructor
  · -- First prove staying probability = 1/3
    fin_cases player_door <;> fin_cases host_door <;> (
      try contradiction  -- Skip invalid cases where player_door = host_door
      all_goals { simp [general_posterior, general_evidence, general_likelihood, car_prior]; norm_num }
    )
  · -- Then prove switching probability = 2/3
    fin_cases player_door <;> fin_cases host_door <;> (
      try contradiction  -- Skip invalid cases where player_door = host_door
      all_goals { simp [general_posterior, general_evidence, general_likelihood, car_prior]; norm_num }
    )

/-!
## Section 6: Main Results
-/

-- Concrete example showing the simplicity
example : posterior_left_middle left = 1/3 ∧ posterior_left_middle right = 2/3 := by
  exact ⟨posterior_stay, posterior_switch⟩

-- The fundamental insight: Switching doubles your probability of winning
theorem monty_hall_advantage : posterior_left_middle right = 2 * posterior_left_middle left := by
  rw [posterior_switch, posterior_stay]; norm_num

-- General switching advantage
theorem general_switching_advantage (player_door host_door : Door) (h : host_door ≠ player_door) :
  let switch_door := if player_door ≠ left ∧ host_door ≠ left then left
                     else if player_door ≠ middle ∧ host_door ≠ middle then middle
                     else right
  general_posterior player_door host_door switch_door = 2 * general_posterior player_door host_door player_door := by
  have ⟨stay_prob, switch_prob⟩ := general_monty_hall player_door host_door h
  -- Apply the let definition first
  show general_posterior player_door host_door
    (if player_door ≠ left ∧ host_door ≠ left then left
     else if player_door ≠ middle ∧ host_door ≠ middle then middle
     else right) = 2 * general_posterior player_door host_door player_door
  rw [switch_prob, stay_prob]
  norm_num

/-!
## Section 7: Advantages of the Bayesian Approach

### Compared to Joint Distribution Approach:

1. **Sample Space Complexity**:
   - Joint approach: 3³ = 27 game states (car, pick, host)
   - Bayesian approach: 3 car positions

2. **Mathematical Framework**:
   - Joint approach: Custom probability measures and weighting functions
   - Bayesian approach: Standard Bayes' theorem

3. **Calculation Complexity**:
   - Joint approach: Weighted sums over 27 states with validity constraints
   - Bayesian approach: Simple 3-term Bayes calculation

4. **Conceptual Clarity**:
   - Joint approach: Mixes unknowns and observations in same probability space
   - Bayesian approach: Clear separation of unknowns vs evidence

5. **Extensibility**:
   - Joint approach: 4-door version requires 4³ = 64 states
   - Bayesian approach: 4-door version requires 4 states

### Key Mathematical Insight:

The Bayesian approach recognizes that we only need to model the **unknown** (car position).
Everything else (player choice, host action) is **evidence** that updates our beliefs.

This is exactly what the commenter meant by focusing on "the unknown state of the world"
and using "likelihood functions" rather than "weighting functions".
-/
