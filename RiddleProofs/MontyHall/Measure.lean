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

noncomputable def raw_real_density (ω : Game) : ℝ  :=
  game_weight ω / total_game_weights

def non_zero_event : Game := {car := left, pick := left, host := middle}

theorem real_sum_one : HasSum raw_real_density 1 := by
  convert hasSum_fintype raw_real_density
  have ne_zero : ∑ a, game_weight a ≠ 0 := by
    intro sum_zero
    have : game_weight non_zero_event ≤ 0 := by
      calc game_weight non_zero_event
        _ ≤ ∑ a, game_weight a := Finset.single_le_sum (fun i _ => by simp [game_weight]; split_ifs <;> norm_num) (Finset.mem_univ _)
        _ = 0 := sum_zero
    simp [game_weight, non_zero_event] at this
    norm_num at this
  calc 1
    _ = total_game_weights / total_game_weights := (div_self ne_zero).symm
    _ = (∑ i, game_weight i) / total_game_weights := by rw [total_game_weights]
    _ = ∑ i, (game_weight i / total_game_weights) := by rw [Finset.sum_div]
    _ = ∑ i, raw_real_density i := rfl

noncomputable def raw_enn_density (i : Game) : ENNReal :=
  ENNReal.ofReal (raw_real_density i)

lemma game_weight_nonneg (i : Game) : game_weight i ≥ 0 := by
  simp [game_weight]; split_ifs <;> norm_num

lemma raw_real_density_nonneg (i : Game) : raw_real_density i ≥ 0 := by
  simp [raw_real_density]
  exact div_nonneg (game_weight_nonneg i) (Finset.sum_nonneg (fun i _ => game_weight_nonneg i))

theorem density_sums_to_one : HasSum raw_enn_density 1 := by
  apply ENNReal.hasSum_coe.mpr
  apply NNReal.hasSum_coe.mp
  convert real_sum_one using 1
  ext i
  rw [Real.coe_toNNReal (raw_real_density i) (raw_real_density_nonneg i)]

lemma prob_density_zero_outside : ∀ a ∉ (Finset.univ : Finset Game), raw_enn_density a = 0 := by
  intro a ha
  exfalso
  exact ha (Finset.mem_univ a)

theorem sum_one: ∑ i, raw_enn_density i = 1 := by
  exact (hasSum_fintype raw_enn_density).unique density_sums_to_one

noncomputable def p : PMF Game :=
  PMF.ofFinset raw_enn_density (Finset.univ : Finset Game) sum_one prob_density_zero_outside

notation:max "ℙ[" A "]" => p.toMeasure A

noncomputable def Prob := p.toMeasure

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance
