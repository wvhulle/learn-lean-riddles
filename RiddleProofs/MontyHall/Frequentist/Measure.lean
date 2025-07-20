/- This file constructs the proper probability measure for the Monty Hall problem.
The key insight is that not all 27 possible games are equally likely - we need
to account for the host's strategy and the rules of the game.
-/

import RiddleProofs.MontyHall.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ENNRealArith



open MeasureTheory Door ENNRealArith

instance measurableSpace : MeasurableSpace Game := ⊤

instance : DiscreteMeasurableSpace Game := ⟨fun _ => trivial⟩

-- **The probability density function for games**
-- This encodes the rules and probabilities of the Monty Hall problem
noncomputable def game_density (ω : Game) : ENNReal :=
  if ω.host = ω.pick then 0        -- Invalid: host can't open contestant's door
  else if ω.host = ω.car then 0    -- Invalid: host can't reveal the car
  else
    if ω.car = ω.pick then 1/18    -- Contestant guessed correctly: host has 2 valid choices
    else 2/18                      -- Contestant guessed wrong: host has 1 valid choice

theorem density_sum_one : ∑ ω : Game, game_density ω = 1 := by
  simp [game_density]
  simp [equivalence_game_repr, game_enumeration, pairs]
  simp [Finset.sum_product]
  simp [fin_to_door]
  eq_as_reals


lemma prob_density_zero_outside : ∀ a ∉ (Finset.univ : Finset Game), game_density a = 0 := by
  intro a ha
  exfalso
  exact ha (Finset.mem_univ a)

noncomputable def p : PMF Game :=
  PMF.ofFinset game_density (Finset.univ : Finset Game) density_sum_one prob_density_zero_outside

notation:max "ℙ[" A "]" => p.toMeasure A

noncomputable def Prob := p.toMeasure

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance
