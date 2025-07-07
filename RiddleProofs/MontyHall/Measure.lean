import RiddleProofs.MontyHall.Enumeration
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ENNRealArith

open MeasureTheory Door ENNRealArith

instance measurableSpace : MeasurableSpace Game := ⊤

instance : DiscreteMeasurableSpace Game := ⟨fun _ => trivial⟩

-- Direct ENNReal density function
noncomputable def game_density (ω : Game) : ENNReal :=
  if ω.host = ω.pick then 0
  else if ω.host = ω.car then 0
  else
    if ω.car = ω.pick then 1/18
    else 2/18

theorem density_sum_one : ∑ ω : Game, game_density ω = 1 := by
  simp [game_density]
  simp [equivalence_game_repr, game_enumeration, pairs]
  simp [Finset.sum_product]
  split_ifs <;> ennreal_arith

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
