import RiddleProofs.MontyHall.Bayesian.Common
import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.Bayesian.Explicit
import RiddleProofs.MontyHall.Bayesian.Formal

-- Key theorem: staying always gives 1/3, switching gives 2/3
-- This is the core mathematical result that makes the Bayesian approach superior
theorem general_monty_hall (player_door host_door : Door) (h : host_door ≠ player_door) :
  general_posterior player_door host_door player_door = 1/3 ∧
  general_posterior player_door host_door (switch_door player_door host_door) = 2/3 := by
  exact ⟨staying_probability player_door host_door h, switching_probability player_door host_door h⟩



-- Simplified Bayes theorem connection
theorem manual_implements_bayes (player_door host_door car_door : Door) :
  general_posterior player_door host_door car_door =
  (car_prior car_door * general_likelihood player_door host_door car_door) /
  general_evidence player_door host_door := by
  unfold general_posterior; split_ifs <;> simp [*]

-- Main equivalence theorem - concise and clear
theorem pmf_bayes_equivalence (player_door host_door : Door) (h : host_door ≠ player_door) :
  car_pmf player_door = ENNReal.ofReal (1/3) ∧
  general_posterior player_door host_door player_door = 1/3 ∧
  general_posterior player_door host_door (switch_door player_door host_door) = 2/3 := by
  exact ⟨car_pmf_correct player_door, general_monty_hall player_door host_door h⟩
