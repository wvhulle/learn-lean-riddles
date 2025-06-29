import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open  MeasureTheory ProbabilityTheory Set ENNReal Finset
/-!
# The Monty Hall Problem

This file formalizes the Monty Hall problem, a classic probability puzzle.

**The Problem**

You are a contestant on a game show. You are presented with three closed doors. Behind one door is a car (the prize), and behind the other two are goats. You complete the following steps:
1. You choose one door.
2. The host, who knows where the car is, opens one of the other two doors to reveal a goat.
3. The host asks if you want to switch your choice to the remaining closed door.

**The Question**

Is it to your advantage to switch doors?

**The Solution**

Yes. Switching doors doubles your probability of winning the car from 1/3 to 2/3. This proof demonstrates this result using probability theory.

See also: https://en.wikipedia.org/wiki/Monty_Hall_problem
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

-- Extensionality for Game
@[ext]
theorem Game.ext {g₁ g₂ : Game} : g₁.car = g₂.car → g₁.pick = g₂.pick → g₁.host = g₂.host → g₁ = g₂ := by
  intro h₁ h₂ h₃
  cases g₁ with | mk c₁ p₁ h₁ =>
  cases g₂ with | mk c₂ p₂ h₂ =>
  simp at h₁ h₂ h₃
  simp [h₁, h₂, h₃]


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

def is_valid_game : Game → Prop := fun (ω : Game) => ω.host ≠ ω.pick ∧ ω.host ≠ ω.car

instance : DecidablePred is_valid_game := by
  unfold is_valid_game
  infer_instance

def valid_games_finset : Finset Game :=
  Finset.filter is_valid_game (Finset.univ : Finset Game)

lemma valid_games_nonempty : valid_games_finset.Nonempty := by
  use {car := left, pick := left, host := middle}
  simp [valid_games_finset, Finset.mem_filter, Finset.mem_univ, is_valid_game]

-- We need to show that prob_density is zero outside the finite universe
lemma prob_density_zero_outside : ∀ a ∉ (Finset.univ : Finset Game), prob_density a = 0 := by
  intro a ha
  -- This is vacuously true since Finset.univ contains all elements of a finite type
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

def host_opens (d : Door) : Set Game := {ω | ω.host = d}

def car_at (d : Door) : Set Game := {ω | ω.car = d}

def pick_door (d : Door) : Set Game := {ω | ω.pick = d}

-- Specific case theorem for player picks left, host opens right
theorem specific_monty_hall_case:
  Prob[car_at left | pick_door left ∩ host_opens right] = 1/3 ∧
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  constructor
  · -- P(car at left | picked left, host opened right) = 1/3
    -- Direct computation: P(car=left ∩ pick=left ∩ host=right) / P(pick=left ∩ host=right)
    have joint_prob : Prob (car_at left ∩ (pick_door left ∩ host_opens right)) = 1/18 := by
      unfold car_at pick_door host_opens Prob
      simp [PMF.toMeasure_apply_finset, Set.inter_def]
      show ∑ x, {ω | ω.car = left ∧ ω.pick = left ∧ ω.host = right}.indicator (⇑p) x = 18⁻¹
      -- Only one game satisfies this: {car := left, pick := left, host := right}
      -- This game has weight 1, so probability 1/18
      rw [equivalence_game_repr]
      simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
      simp [Finset.sum_product]
      norm_cast
      simp [fin_to_door]
      -- For the game {car := left, pick := left, host := right}:
      -- host ≠ pick (right ≠ left) ✓
      -- host ≠ car (right ≠ left) ✓
      -- car = pick (left = left) ✓
      -- So weight = 1, density = 1/18
      simp [prob_density, real_density, game_weight, total_weight_value]
      norm_num
      -- Now we need to prove ENNReal.ofReal (1 / 18) = 18⁻¹
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 18)]
      rw [ENNReal.ofReal_one]
      rw [one_div]
      simp [ENNReal.ofReal_natCast]

    have marginal_prob : Prob (pick_door left ∩ host_opens right) = 1/6 := by
      unfold pick_door host_opens Prob
      simp [PMF.toMeasure_apply_finset, Set.inter_def]
      show ∑ x, {ω | ω.pick = left ∧ ω.host = right}.indicator (⇑p) x = 6⁻¹
      -- Two games satisfy this:
      -- {car := left, pick := left, host := right} with weight 1
      -- {car := middle, pick := left, host := right} with weight 2
      -- Total: 1 + 2 = 3, so probability 3/18 = 1/6
      rw [equivalence_game_repr]
      simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
      simp [Finset.sum_product]
      norm_cast
      simp [fin_to_door]
      simp [prob_density, real_density, game_weight, total_weight_value]
      norm_num
      -- Need to prove ENNReal.ofReal (1/18) + ENNReal.ofReal (1/9) = 6⁻¹
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1/18) (by norm_num : (0 : ℝ) ≤ 1/9)]
      norm_num
      -- Now need to prove ENNReal.ofReal (1/6) = 6⁻¹
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 6)]
      rw [ENNReal.ofReal_one]
      rw [one_div]
      simp [ENNReal.ofReal_natCast]

    -- Now use the definition of conditional probability
    rw [ProbabilityTheory.cond_apply]
    rw [Set.inter_comm]
    rw [joint_prob, marginal_prob]
    norm_num
    -- (1/18) / (1/6) = (1/18) * (6/1) = 6/18 = 1/3

  · -- P(car at middle | picked left, host opened right) = 2/3
    -- Direct computation: P(car=middle ∩ pick=left ∩ host=right) / P(pick=left ∩ host=right)
    have joint_prob : Prob (car_at middle ∩ (pick_door left ∩ host_opens right)) = 2/18 := by
      unfold car_at pick_door host_opens Prob
      simp [PMF.toMeasure_apply_finset, Set.inter_def]
      show ∑ x, {ω | ω.car = middle ∧ ω.pick = left ∧ ω.host = right}.indicator (⇑p) x = 2 * 18⁻¹
      -- Only one game satisfies this: {car := middle, pick := left, host := right}
      -- This game has weight 2, so probability 2/18
      rw [equivalence_game_repr]
      simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
      simp [Finset.sum_product]
      norm_cast
      simp [fin_to_door]
      simp [game_weight]
      norm_num

    have marginal_prob : Prob (pick_door left ∩ host_opens right) = 1/6 := by
      unfold pick_door host_opens Prob
      simp [PMF.toMeasure_apply_finset, Set.inter_def]
      show ∑ x, {ω | ω.pick = left ∧ ω.host = right}.indicator (⇑p) x = 6⁻¹
      -- Same as above: 3/18 = 1/6
      rw [equivalence_game_repr]
      simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
      simp [Finset.sum_product]
      norm_cast
      simp [fin_to_door]
      simp [game_weight]
      norm_num

    rw [ProbabilityTheory.cond_apply]
    rw [Set.inter_comm]
    rw [joint_prob, marginal_prob]
    norm_num
    -- (2/18) / (1/6) = (2/18) * (6/1) = 12/18 = 2/3

-- Main Monty Hall theorem (the general case)
theorem simplified_monty_hall:
  Prob[car_at left | pick_door left ∩ host_opens right ∪ pick_door left ∩ host_opens middle] = 1/3 := by
  sorry
