import RiddleProofs.MontyHall.Bayesian.Common
import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.Bayesian.Explicit
import RiddleProofs.MontyHall.Bayesian.Formal

open Door

-- Main equivalence theorem: shows that formal PMF approach gives same results as explicit Bayesian calculation
theorem formal_explicit_equivalence (player_door host_door : Door) (h : host_door ≠ player_door) :
  car_pmf player_door = ENNReal.ofReal (1/3) ∧
  general_posterior player_door host_door player_door = 1/3 ∧
  general_posterior player_door host_door (switch_door player_door host_door) = 2/3 := by
  exact ⟨car_pmf_correct player_door, expl_bay_monty_hall player_door host_door h⟩

-- Evidence equivalence: shows that PMF-based evidence equals manual Bayesian evidence calculation
theorem evidence_equivalence (player_door host_door : Door) :
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
