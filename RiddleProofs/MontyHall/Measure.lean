import RiddleProofs.MontyHall.Enumeration
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ENNRealArith

/-!
# Monty Hall Problem: Probability measure approach

This file constructs the proper probability measure for the Monty Hall problem.
The key insight is that not all 27 possible games are equally likely - we need
to account for the host's strategy and the rules of the game.

**The probability model**:
- The car is equally likely to be behind any of the 3 doors (1/3 each)
- The contestant picks a door uniformly at random (1/3 each)
- The host must open a door that: (1) wasn't picked by contestant, (2) doesn't have the car
- If the host has multiple valid choices, they choose randomly

**Mathematical setup**:
- Games where host violates the rules get probability 0
- Valid games get probability proportional to the number of host's valid choices
- This gives us a proper probability measure that sums to 1

**Learning goals**:
- Understand conditional probability and measure theory
- Learn about probability mass functions (PMF) in Lean
- See how to construct measures from density functions
- Practice with ENNReal (extended non-negative reals)
-/

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
