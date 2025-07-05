import RiddleProofs.MontyHall.Enumeration
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory Door

instance measurableSpace : MeasurableSpace Game := ⊤

instance : DiscreteMeasurableSpace Game := ⟨fun _ => trivial⟩

noncomputable def game_weight (ω : Game) : ℝ :=
  if ω.host = ω.pick then 0
  else if ω.host = ω.car then 0
  else
    if ω.car = ω.pick then 1
    else 2

noncomputable def total_game_weights : ℝ := ∑ ω : Game, game_weight ω

theorem total_weight_value: total_game_weights = 18 := by
  simp [total_game_weights, game_weight]
  simp [equivalence_game_repr, game_enumeration, pairs]
  simp [Finset.sum_product]
  norm_cast

noncomputable def real_density (ω : Game) : ℝ  :=
  game_weight ω / total_game_weights

def non_zero_event : Game := {car := left, pick := left, host := middle}

theorem real_sum_one : HasSum real_density 1 := by
  convert hasSum_fintype real_density
  unfold real_density
  unfold total_game_weights
  have ne_zero : ∑ a, game_weight a ≠ 0 := by
    intro sum_zero
    have : game_weight non_zero_event ≤ 0 := by
      rw [← sum_zero]
      apply Finset.single_le_sum
      · intro i _
        simp [game_weight]
        split_ifs <;> norm_num
      · exact Finset.mem_univ _
    simp [game_weight, non_zero_event] at this
    norm_num at this
  rw [<- Finset.sum_div]
  rw [div_self ne_zero]

noncomputable def prob_density (i : Game) : ENNReal :=
  ENNReal.ofReal (real_density i)

theorem density_sums_to_one : HasSum prob_density 1 := by
  apply ENNReal.hasSum_coe.mpr
  apply NNReal.hasSum_coe.mp
  convert real_sum_one using 1
  have dpos: ∀ i, game_weight i ≥ 0 := by
    intro i
    simp [game_weight]
    split_ifs <;> norm_num
  have: ∀ i, real_density i >= 0 := by
    intro i
    simp [real_density]
    apply div_nonneg
    · exact dpos i
    · rw [total_game_weights]
      exact Finset.sum_nonneg (fun i _ => dpos i)
  ext i
  rw [Real.coe_toNNReal (real_density i) (this i)]



lemma prob_density_zero_outside : ∀ a ∉ (Finset.univ : Finset Game), prob_density a = 0 := by
  intro a ha
  exfalso
  exact ha (Finset.mem_univ a)


theorem sum_one: ∑ i, prob_density i = 1 := by
  exact (hasSum_fintype prob_density).unique density_sums_to_one


noncomputable def p : PMF Game :=
  PMF.ofFinset prob_density (Finset.univ : Finset Game)  sum_one prob_density_zero_outside



noncomputable def Prob  := p.toMeasure

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance
