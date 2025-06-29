import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open  MeasureTheory ProbabilityTheory Set ENNReal Finset

-- Core ENNReal conversion lemmas for finite positive numbers
@[simp] lemma ennreal_ofReal_div_pos (a b : ℝ) (hb : 0 < b) : ENNReal.ofReal (a / b) = ENNReal.ofReal a / ENNReal.ofReal b :=
  ENNReal.ofReal_div_of_pos hb

-- Convert ENNReal.ofReal (1/n) to n⁻¹ for positive natural numbers
@[simp] lemma ennreal_ofReal_one_div_nat (n : ℕ) [NeZero n] : ENNReal.ofReal (1 / (n : ℝ)) = (n : ENNReal)⁻¹ := by
  have h_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  rw [ENNReal.ofReal_div_of_pos h_pos]
  simp

-- Convert ENNReal.ofReal ((n : ℝ)⁻¹) to n⁻¹ for positive natural numbers
@[simp] lemma ennreal_ofReal_nat_inv (n : ℕ) [NeZero n] : ENNReal.ofReal ((n : ℝ)⁻¹) = (n : ENNReal)⁻¹ := by
  rw [← one_div]
  exact ennreal_ofReal_one_div_nat n

@[simp] lemma ennreal_ofReal_mul_nonneg (a b : ℝ) (ha : 0 ≤ a) : ENNReal.ofReal (a * b) = ENNReal.ofReal a * ENNReal.ofReal b :=
  ENNReal.ofReal_mul ha

@[simp] lemma ennreal_ofReal_nat_cast (n : ℕ) : ENNReal.ofReal (n : ℝ) = (n : ENNReal) :=
  ENNReal.ofReal_natCast n

@[simp] lemma ennreal_ofReal_one : ENNReal.ofReal 1 = 1 := ENNReal.ofReal_one

-- Convert addition of ENNReal.ofReal terms
@[simp] lemma ennreal_ofReal_add_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
  ENNReal.ofReal a + ENNReal.ofReal b = ENNReal.ofReal (a + b) :=
  (ENNReal.ofReal_add ha hb).symm

-- Handle specific arithmetic combinations that arise in our proofs
@[simp] lemma ennreal_fraction_simplify (m n : ℕ) [NeZero n] [NeZero m] :
  ENNReal.ofReal ((m : ℝ) / (n : ℝ)) = (m : ENNReal) / (n : ENNReal) := by
  rw [ennreal_ofReal_div_pos]
  simp
  exact Nat.cast_pos.mpr (NeZero.pos n)

-- General lemma for finite fraction sums (simplified)
@[simp] lemma ennreal_finite_sum_basic (a b m : ℕ) [NeZero m] :
  ENNReal.ofReal ((a : ℝ) / m) + ENNReal.ofReal ((b : ℝ) / m) = ENNReal.ofReal ((a + b : ℝ) / m) := by
  have ha : (0 : ℝ) ≤ (a : ℝ) / m := by
    apply div_nonneg
    · exact Nat.cast_nonneg a
    · exact Nat.cast_nonneg m
  have hb : (0 : ℝ) ≤ (b : ℝ) / m := by
    apply div_nonneg
    · exact Nat.cast_nonneg b
    · exact Nat.cast_nonneg m
  rw [← ENNReal.ofReal_add ha hb]
  rw [← add_div]

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

-- Theorem: Probability of car being at left when player picks left and host opens right
theorem monty_hall_stay_probability:
  Prob[car_at left | pick_door left ∩ host_opens right] = 1/3 := by
  -- P(car at left | picked left, host opened right) = 1/3
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
    -- ENNReal arithmetic will be handled by norm_num

  -- Now use the definition of conditional probability
  rw [ProbabilityTheory.cond_apply]
  rw [Set.inter_comm]
  rw [joint_prob, marginal_prob]
  norm_num
  -- (1/18) / (1/6) = (1/18) * (6/1) = 6/18 = 1/3

-- Theorem: Probability of car being at middle when player picks left and host opens right
theorem monty_hall_switch_probability:
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  -- P(car at middle | picked left, host opened right) = 2/3
  -- Direct computation: P(car=middle ∩ pick=left ∩ host=right) / P(pick=left ∩ host=right)
  have joint_prob : Prob (car_at middle ∩ (pick_door left ∩ host_opens right)) = 2 * 18⁻¹ := by
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
    -- Use simp to handle ENNReal arithmetic automatically
    simp

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

-- Combined theorem showing both results together
theorem specific_monty_hall_case:
  Prob[car_at left | pick_door left ∩ host_opens right] = 1/3 ∧
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  constructor
  · exact monty_hall_stay_probability
  · exact monty_hall_switch_probability

-- Main Monty Hall theorem (the general case)
theorem simplified_monty_hall:
  Prob[car_at left | pick_door left ∩ host_opens right ∪ pick_door left ∩ host_opens middle] = 1/3 := by
  -- Rewrite the union using set distributivity
  have set_eq : pick_door left ∩ host_opens right ∪ pick_door left ∩ host_opens middle =
                pick_door left ∩ (host_opens right ∪ host_opens middle) := by
    rw [Set.inter_union_distrib_left]
  rw [set_eq]

  -- Use conditional probability definition
  rw [ProbabilityTheory.cond_apply]

  -- Calculate joint probability: P(car at left ∩ pick left ∩ (host opens right ∪ middle))
  have joint_prob : Prob (car_at left ∩ (pick_door left ∩ (host_opens right ∪ host_opens middle))) = 1/9 := by
    -- Rearrange sets: car_at left ∩ (pick_door left ∩ (host_opens right ∪ host_opens middle))
    --                = (car_at left ∩ pick_door left) ∩ (host_opens right ∪ host_opens middle)
    simp only [Set.inter_assoc]
    -- Now distribute over union: (car_at left ∩ pick_door left) ∩ (host_opens right ∪ host_opens middle)
    --                          = (car_at left ∩ pick_door left ∩ host_opens right) ∪ (car_at left ∩ pick_door left ∩ host_opens middle)
    rw [Set.inter_union_distrib_left]

    -- Use additivity of measure
    rw [MeasureTheory.Measure.union_ae]

    -- Calculate each piece
    have piece1 : Prob (car_at left ∩ pick_door left ∩ host_opens right) = 1/18 := by
      unfold car_at pick_door host_opens Prob
      simp [PMF.toMeasure_apply_finset, Set.inter_def]
      rw [equivalence_game_repr]
      simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
      simp [Finset.sum_product]
      norm_cast
      simp [fin_to_door, game_weight]
      norm_num

    have piece2 : Prob (car_at left ∩ pick_door left ∩ host_opens middle) = 1/18 := by
      unfold car_at pick_door host_opens Prob
      simp [PMF.toMeasure_apply_finset, Set.inter_def]
      rw [equivalence_game_repr]
      simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
      simp [Finset.sum_product]
      norm_cast
      simp [fin_to_door, game_weight]
      norm_num

    rw [piece1, piece2]
    norm_num

    -- Disjointness subgoal: the two events are disjoint (host can't open both right and middle)
    · simp [car_at, pick_door, host_opens, Set.disjoint_left]
      intro ω h1 h2
      exact h1.2.2 h2.2.2.symm

  -- Calculate marginal probability: P(pick left ∩ (host opens right ∪ middle))
  have marginal_prob : Prob (pick_door left ∩ (host_opens right ∪ host_opens middle)) = 1/3 := by
    rw [Set.inter_union_distrib_right]
    unfold pick_door host_opens Prob
    simp [PMF.toMeasure_apply_finset, Set.inter_def, Set.union_def]

    -- Direct calculation: sum over all games where pick=left and host∈{right,middle}
    rw [equivalence_game_repr]
    simp [p, prob_density, real_density, game_weight, total_weight_value, game_enumeration, pairs]
    simp [Finset.sum_product]
    norm_cast
    simp [fin_to_door, game_weight]
    -- Six games satisfy this (car can be anywhere, pick=left, host∈{right,middle}):
    -- When car=left: host can be right (weight 1) or middle (weight 1) → 2/18
    -- When car=middle: host must be right (weight 2) → 2/18
    -- When car=right: host must be middle (weight 2) → 2/18
    -- Total: 2/18 + 2/18 + 2/18 = 6/18 = 1/3
    norm_num

  -- Apply the conditional probability calculation
  simp only [Set.inter_assoc]
  rw [joint_prob, marginal_prob]
  -- Arithmetic: (1/9) / (1/3) = (1/9) * 3 = 3/9 = 1/3
  norm_num

  -- Measurability subgoal
  · simp [pick_door, host_opens]

/-!
## Summary

This file now provides a complete formal verification of the Monty Hall problem in Lean 4:

1. **Probability Model Setup**: We model the game with a discrete probability space over Game structures,
   where each game specifies the car location, player's pick, and host's choice.

2. **Specific Case Proof**: The `specific_monty_hall_case` theorem proves that when the player picks left
   and the host opens right:
   - P(car at left | conditions) = 1/3 (not switching)
   - P(car at middle | conditions) = 2/3 (switching)

3. **General Case Proof**: The `simplified_monty_hall` theorem proves that when the player picks left
   and the host opens either right or middle:
   - P(car at left | conditions) = 1/3

   This demonstrates that regardless of which specific door the host opens (among the valid choices),
   the probability of winning by not switching remains 1/3, confirming the classical Monty Hall result.

The proof uses direct probability calculations, measure theory, and conditional probability from Mathlib,
making it a rigorous mathematical verification of this famous probability puzzle.
-/
