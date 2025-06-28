import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open  MeasureTheory ProbabilityMeasure ProbabilityTheory Set ENNReal
/-!
# The Monty Hall Problem

**Problem**: You're on a game show with three doors. Behind one door is a car, behind the other two are goats. You pick a door (say door 1). The host, who knows what's behind each door, opens another door (say door 3) revealing a goat. The host then asks: "Do you want to switch to door 2?"

**Question**: Should you switch doors to maximize your chance of winning the car?

**Intuition**: Many people think it doesn't matter (50/50 chance), but switching actually gives you a 2/3 probability of winning versus 1/3 for staying with your original choice.


See https://brilliant.org/wiki/monty-hall-problem/
-/



inductive Door : Type
| left
| middle
| right
deriving DecidableEq, Repr, Fintype

open Door


instance : MeasurableSpace Door := ⊤
instance : MeasurableSingletonClass Door := by infer_instance

structure Game where
  car   : Door
  pick  : Door
  host  : Door
  deriving DecidableEq, Repr, Fintype


def door_to_fin (d : Door) : Fin 3 :=
  match d with
  | left => 0
  | middle => 1
  | right => 2

def fin_to_door (f : Fin 3) : Door :=
  match f with
  | 0 => left
  | 1 => middle
  | 2 => right

lemma fin_to_door_injective : Function.Injective fin_to_door := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [fin_to_door] at h <;> rfl

def pairs := ({0, 1, 2} ×ˢ {0, 1, 2} ×ˢ {0, 1, 2} : Finset (Fin 3 × Fin 3 × Fin 3) )

def game_enumeration: Finset Game :=
  pairs.map ⟨(fun x => match x with
    | (car_idx, pick_idx, host_idx) =>
      {car := fin_to_door car_idx, pick := fin_to_door pick_idx, host := fin_to_door host_idx}),
    by
      intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
      simp at h
      have h1 : a1 = b1 := fin_to_door_injective h.1
      have h2 : a2 = b2 := fin_to_door_injective h.2.1
      have h3 : a3 = b3 := fin_to_door_injective h.2.2
      simp [h1, h2, h3]⟩


theorem equivalence_game_repr : (Finset.univ : Finset Game) = game_enumeration := by
  rfl

instance fin_outcome: Finset Game :=
  Finset.univ

instance measurableSpace : MeasurableSpace Game := ⊤

instance : DiscreteMeasurableSpace Game := ⟨fun _ => trivial⟩

def game_weight (ω : Game) : ℝ :=
  if ω.host = ω.pick then 0     -- Host never opens the picked door.
  else if ω.host = ω.car then 0 -- Host never opens the car door.
  else
    if ω.car = ω.pick then 1    -- Contestant chose the car. Host chooses from 2 doors.
    else 2                      -- Contestant chose a goat. Host is forced to open the only other goat door.

def total_game_weights : ℝ := ∑ ω : Game, game_weight ω


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

noncomputable def p : PMF Game :=
  { val := prob_density,
    property :=  density_sums_to_one
  }


lemma third_door_available (pick host : Door) : ((Finset.univ.erase pick).erase host).Nonempty := by
  fin_cases pick <;> fin_cases host <;> decide

-- This had to be deterministic.
def remaining_door (pick host : Door) : Door :=
  match pick, host with
  | left, middle => right
  | left, right => middle
  | middle, left => right
  | right, left => middle
  | right, middle => left
  | right, right => left
  | middle, right => left
  | middle, middle => left
  | left, left => right

def switch_win_event : Set Game :=
  { ω | remaining_door ω.pick ω.host = ω.car }

def noswitch_win_event : Set Game :=
  { ω | ω.pick = ω.car }

 def switch_win_pred (ω : Game) : Prop := remaining_door ω.pick ω.host = ω.car
 def no_switch_win_pred (ω : Game) : Prop := ω.pick = ω.car

instance : DecidablePred switch_win_pred :=  by
  unfold switch_win_pred
  infer_instance
instance : DecidablePred no_switch_win_pred := by
  unfold no_switch_win_pred
  infer_instance


noncomputable def Prob  := p.toMeasure

instance: IsFiniteMeasure Prob := by
  unfold Prob
  infer_instance

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance



noncomputable instance measureSpace : MeasureSpace Game :=
  ⟨Prob⟩


def H := { ω : Game | ω.car = left}


instance  : MeasurableSet H :=
  DiscreteMeasurableSpace.forall_measurableSet H


example : Prob H = 1/3 := by
  -- Use PMF.toMeasure_apply_fintype to convert to sum over Game
  unfold Prob H
  rw [PMF.toMeasure_apply_fintype]

  -- Convert indicator to conditional sum
  simp only [Set.indicator_apply, H, Set.mem_setOf_eq]

  -- Now we have ∑ x, if x.car = left then p x else 0
  -- Use definition of p in terms of real_density
  have h_pmf : ∀ ω, p ω = ENNReal.ofReal (real_density ω) := by
    intro ω
    rfl
  simp [h_pmf]

  -- Convert to real sum using symmetry
  have h_nonneg : ∀ x, 0 ≤ real_density x := by
    intro x
    simp [real_density]
    apply div_nonneg
    · simp [game_weight]; split_ifs <;> norm_num
    · rw [total_weight_value]; norm_num

  sorry

def E := { ω : Game | ω.pick = left ∧  ω.host = right }


instance : MeasurableSet E :=
  DiscreteMeasurableSpace.forall_measurableSet E




theorem total_prob_eq: Prob E = Prob[E|H] * Prob H + Prob[E|Hᶜ] * Prob Hᶜ  := by
  -- I could not find the law of total probability in mathlib, maybe I overlooked it.
  sorry



theorem do_not_switch_eq : Prob[H|E]  = Prob switch_win_pred  := by
  -- This should use conditional probability and relate to switching probabilities
  sorry

theorem do_switch_eq : Prob[Hᶜ|E] = Prob no_switch_win_pred := by
  -- It was kind of important for me to use Bayes theorem here, because I want to show the benefit of having Mathlib provided.
  -- This should use conditional probability and relate to non-switching probabilities
  sorry

-- The official solution to the Monty Hall problem is that switching gives you a 2/3 chance of winning compared to 1/3 for not switching.
theorem monty_hall_solution: Prob switch_win_pred > Prob no_switch_win_pred := by
  have switch_prob: Prob switch_win_pred = 2/3 := by
    rw [<- do_not_switch_eq]
    sorry
  have noswitch_prob: Prob no_switch_win_pred = 1/3 := by
    rw [<- do_switch_eq]
    sorry
  simp [switch_prob, noswitch_prob]
  sorry
