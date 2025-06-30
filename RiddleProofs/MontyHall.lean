import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Fintype.Card

open MeasureTheory ProbabilityTheory Set ENNReal Finset


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

**The Key Insight**

The probability model assigns different weights to different game scenarios:
- When contestant picks correctly (car=pick): weight = 1 (host has 2 doors to choose from)
- When contestant picks incorrectly (car≠pick): weight = 2 (host is forced to open specific door)

This weighting reflects the host's constraint: the host must always open a door with a goat.

See also: https://en.wikipedia.org/wiki/Monty_Hall_problem
-/

inductive Door : Type
| left
| middle
| right
deriving DecidableEq, Repr, Fintype

open Door

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

def host_opens (d : Door) : Set Game := {ω | ω.host = d}

def car_at (d : Door) : Set Game := {ω | ω.car = d}

def pick_door (d : Door) : Set Game := {ω | ω.pick = d}



@[simp] lemma ennreal_frac_reduce {a b c : ℕ} {hc_pos : 0 < c} :
  (a * c : ENNReal) / (b * c) = a / b := by
  apply ENNReal.mul_div_mul_right
  · simp [Nat.cast_ne_zero, ne_of_gt hc_pos]
  · simp [ENNReal.natCast_ne_top]

@[simp] lemma ennreal_inv_frac_mul_frac_general {a b c : ℕ} :
  (1 / (a : ENNReal))⁻¹ * ((b : ENNReal) / (c : ENNReal)) = ((a * b : ℕ) : ENNReal) / (c : ENNReal) := by
  rw [one_div, inv_inv, ← mul_div_assoc, Nat.cast_mul]


@[simp] lemma ennreal_ofReal_div_pos {a b : ℝ} {hb : 0 < b} :
  ENNReal.ofReal (a / b) = ENNReal.ofReal a / ENNReal.ofReal b :=
  ENNReal.ofReal_div_of_pos hb

@[simp] lemma ennreal_inv_inv {a: ENNReal}: (a ⁻¹)⁻¹ = a := by simp

@[simp] lemma ennreal_div_inv {a : ENNReal} {g: a ≠ ⊤} :
  ENNReal.ofReal ((1 / ENNReal.toReal a)⁻¹) = a := by
  rw [one_div, inv_inv, ENNReal.ofReal_toReal g]


lemma ennreal_div_eq {a b : ENNReal} (h: b ≠ 0) (i: a ≠ ⊤):
  a / b = ENNReal.ofReal (ENNReal.toReal a / ENNReal.toReal b) := by
  rw [← ENNReal.ofReal_toReal (ENNReal.div_ne_top i h)]
  congr 1
  exact ENNReal.toReal_div a b


@[simp]  lemma ennreal_mul_frac_simplify {a b c d e : ℕ} (h : a * b * e = d * c)
  (hc_pos : 0 < c) (he_pos : 0 < e) :
  (a : ENNReal) * ((b : ENNReal) / (c : ENNReal)) = (d : ENNReal) / (e : ENNReal) := by
  have h1: (a : ENNReal) * (b / c) = (a * b) / c := by
    exact Eq.symm (mul_div_assoc (a : ENNReal) (b : ENNReal) (c : ENNReal))
  rw [h1]
  refine (ENNReal.div_eq_div_iff ?_ ?_ ?_ ?_).mpr ?_
  · simp [Nat.cast_ne_zero, ne_of_gt hc_pos]
    intro a
    linarith
  · simp [ENNReal.natCast_ne_top]
  · simp [Nat.cast_ne_zero, ne_of_gt he_pos]
    linarith
  · simp [ENNReal.natCast_ne_top]
  · norm_cast
    rw [mul_comm e (a * b)]
    rw [mul_comm c d]
    exact h



lemma unique_game_set (car pick host : Door) :
  {ω : Game | ω.pick = pick ∧ ω.host = host ∧ ω.car = car} =
  {({car := car, pick := pick, host := host} : Game)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact Game.ext h3 h1 h2
  · intro h
    rw [h]; simp

lemma prob_density_car_eq_pick (car pick host : Door) (h_eq : car = pick) (h_valid : host ≠ pick ∧ host ≠ car) :
  prob_density {car := car, pick := pick, host := host} = (1 : ENNReal) / 18 := by
  unfold prob_density real_density
  rw [total_weight_value]
  unfold game_weight
  simp [h_eq, h_valid.1, h_valid.2]
  norm_num

lemma prob_density_car_ne_pick (car pick host : Door) (h_ne : car ≠ pick) (h_valid : host ≠ pick ∧ host ≠ car) :
  prob_density {car := car, pick := pick, host := host} = (2 : ENNReal) / 18 := by
  unfold prob_density real_density
  rw [total_weight_value]
  unfold game_weight
  simp [h_ne, h_valid.1, h_valid.2]

-- When car = pick (staying wins): probability density = 1/18 (weight 1, divided by total weight 18)
lemma prob_density_left_left_right :
  prob_density {car := left, pick := left, host := right} = (1 : ENNReal) / 18 := by
  apply prob_density_car_eq_pick
  · rfl
  · simp

-- When car ≠ pick (switching wins): probability density = 2/18 (weight 2, divided by total weight 18)
lemma prob_density_middle_left_right :
  prob_density {car := middle, pick := left, host := right} = (2 : ENNReal) / 18 := by
  apply prob_density_car_ne_pick
  · simp
  · simp

-- When host opens car door: impossible (probability density = 0)
lemma prob_density_right_left_right :
  prob_density {car := right, pick := left, host := right} = 0 := by
  unfold prob_density real_density game_weight
  simp

-- Common denominator lemma: P(pick=left ∩ host=right) = 1/6
-- This represents the total probability of the conditioning event across all car positions
lemma prob_pick_left_host_right :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right}) = 1/6 := by
  have h_inter_eq : ({ω : Game | ω.pick = left} ∩ {ω : Game | ω.host = right}) =
                    {ω : Game | ω.pick = left ∧ ω.host = right} := by
    ext ω; simp [Set.mem_inter_iff]

  rw [h_inter_eq]
  have h_filter_eq : {ω : Game | ω.pick = left ∧ ω.host = right} =
    ↑(game_enumeration.filter (fun ω => ω.pick = left ∧ ω.host = right)) := by
      rw [← equivalence_game_repr]
      ext ω; simp [Finset.mem_filter]

  rw [h_filter_eq, PMF.toMeasure_apply_finset]
  have h_filter_explicit :
    game_enumeration.filter (fun ω => ω.pick = left ∧ ω.host = right) =
    {({car := left, pick := left, host := right} : Game),
     ({car := middle, pick := left, host := right} : Game),
     ({car := right, pick := left, host := right} : Game)} := by
    simp [game_enumeration]; decide

  rw [h_filter_explicit]
  unfold p
  simp only [PMF.ofFinset_apply]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · rw [prob_density_left_left_right, prob_density_middle_left_right, prob_density_right_left_right]
    simp only [add_zero]
    rw [← ENNReal.add_div]
    ring_nf
    rw [show (3 : ENNReal) / 18 = (1 * 3) / (6 * 3) by norm_num]
    rw [ENNReal.mul_div_mul_right]
    · norm_num
    · norm_num
  · simp
  · simp

lemma prob_car_at_given_pick_host (car : Door) :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = car}) =
  prob_density {car := car, pick := left, host := right} := by
  have h_inter_eq : {ω : Game | ω.pick = left} ∩ {ω : Game | ω.host = right} ∩ {ω : Game | ω.car = car} =
                    {ω : Game | ω.pick = left ∧ ω.host = right ∧ ω.car = car} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have h_singleton := unique_game_set car left right
  rw [h_inter_eq, h_singleton]
  rw [PMF.toMeasure_apply_singleton]; rfl
  exact MeasurableSet.singleton _

lemma prob_car_left_pick_left_host_right :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = left}) = 1/18 := by
  rw [prob_car_at_given_pick_host, prob_density_left_left_right]

lemma prob_car_middle_pick_left_host_right :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = middle}) = 2/18 := by
  rw [prob_car_at_given_pick_host, prob_density_middle_left_right]

theorem monty_hall_stay_probability:
  Prob[car_at left | pick_door left ∩ host_opens right] = 1/3 := by
  unfold Prob car_at pick_door host_opens
  rw [ProbabilityTheory.cond_apply]
  · rw [prob_car_left_pick_left_host_right, prob_pick_left_host_right]
    simp
    refine (toReal_eq_toReal_iff' ?_ ?_).mp ?_
    simp
    refine div_ne_top ?_ ?_
    norm_cast
    norm_cast
    norm_cast
    norm_cast
    simp
    norm_num
  · apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete

theorem monty_hall_switch_probability:
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  unfold Prob car_at pick_door host_opens
  rw [ProbabilityTheory.cond_apply]
  · rw [prob_car_middle_pick_left_host_right]
    rw [prob_pick_left_host_right]
    simp
    exact ennreal_mul_frac_simplify  (by norm_num) (by norm_num) (by norm_num)
  · apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
