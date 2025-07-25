import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Distributions.Uniform
import ENNRealArith

open PMF ProbabilityTheory MeasureTheory

/-!
# The Monty Hall Problem

## Statement

You are a contestant on a game show. You are presented with three closed doors. Behind one door is a car (the prize), and behind the other two are goats.

   ┌───────┐   ┌───────┐   ┌───────┐
   │ Door 1│   │ Door 2│   │ Door 3│
   │  ???  │   │  ???  │   │  ???  │
   └───────┘   └───────┘   └───────┘
      ^           ^           ^
   [Goat/Car]  [Goat/Car]  [Goat/Car]

You complete the following steps:
1. You choose one door.
2. The host, who knows where the car is, opens one of the other two doors to reveal a goat.
3. The host asks if you want to switch your choice to the remaining closed door.

## Question

Is it to your advantage to switch doors?

-/

inductive Door : Type
| left
| middle
| right
deriving DecidableEq, Repr, Fintype

instance : Nonempty Door := ⟨Door.left⟩

open Door

structure Game where
  car  : Door
  pick : Door
  host : Door
  host_not_pick : host ≠ pick
  host_not_car : host ≠ car
deriving DecidableEq, Repr, Fintype

instance : Nonempty Game := ⟨{
  pick := left, host := right, car := middle,
  host_not_car := by simp, host_not_pick := by simp
}⟩

instance : MeasurableSpace Game := ⊤

def host_opens (d : Door) : Set Game := {ω | ω.host = d}
def car_at (d : Door) : Set Game := {ω | ω.car = d}

@[ext]
theorem Game.ext {g₁ g₂ : Game} (h₁ : g₁.car = g₂.car) (h₂ : g₁.pick = g₂.pick)
    (h₃ : g₁.host = g₂.host) : g₁ = g₂ := by
  cases g₁; cases g₂; simp at h₁ h₂ h₃; simp [h₁, h₂, h₃]

noncomputable def Prob : Measure Game := (uniformOfFintype Game).toMeasure

instance : IsProbabilityMeasure Prob := by unfold Prob; infer_instance

notation:max "ℙ[" A "]" => Prob A


theorem law_of_total_probability {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω)
  {hA : MeasurableSet A} {hB : MeasurableSet B} :
  μ A = μ[A | B] * μ B + μ[A | Bᶜ] * μ Bᶜ := by
  have h_partition : A = (A ∩ B) ∪ (A ∩ Bᶜ) := by
    ext ω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have h_disjoint : Disjoint (A ∩ B) (A ∩ Bᶜ) := by
    simp only [Set.disjoint_iff_inter_eq_empty]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false]
    constructor
    · intro ⟨⟨_, hωB⟩, ⟨_, hωBc⟩⟩
      exact hωBc hωB
    · intro h
      exfalso
      exact h
  calc μ A
    _ = μ (A ∩ B ∪ A ∩ Bᶜ) := by
      exact congrArg (⇑μ) h_partition
    _ = μ (A ∩ B) + μ (A ∩ Bᶜ) := by
      rw [measure_union h_disjoint (MeasurableSet.inter hA hB.compl)]
    _ = μ[A | B] * μ B + μ (A ∩ Bᶜ) := by
      congr 1
      rw [Set.inter_comm]
      rw [← ProbabilityTheory.cond_mul_eq_inter hB A μ]
    _ = μ[A | B] * μ B + μ[A | Bᶜ] * μ Bᶜ := by
      congr 2
      rw [Set.inter_comm]
      rw [← ProbabilityTheory.cond_mul_eq_inter (by exact MeasurableSet.compl_iff.mpr hB) A μ]


lemma set_to_finset_conv {P : Game → Prop} [DecidablePred P] :
  {ω : Game | P ω} = ↑(Finset.univ.filter P) := by
  ext ω; simp

lemma total_games : Fintype.card Game = 12 := by decide

lemma car_finset_card {car : Door} :
  (Finset.univ.filter (fun ω : Game => ω.car = car)).card = 4 := by
  fin_cases car <;> decide

lemma car_host_card {car host : Door} (hnc : host ≠ car) :
  (Finset.univ.filter (fun ω : Game => ω.car = car ∧ ω.host = host)).card = 2 := by
  fin_cases host <;> fin_cases car <;> simp at hnc <;> decide

lemma car_behind_door {car : Door} : Prob (car_at car) = 1/3 := by
  unfold Prob car_at
  rw [set_to_finset_conv, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_const, nsmul_eq_mul, car_finset_card, total_games]
  norm_num; eq_as_reals

lemma car_not_behind_door {car : Door} : Prob ((car_at car)ᶜ) = 2/3 := by
  rw [measure_compl (by trivial) (measure_ne_top _ _), measure_univ, car_behind_door]
  rw [ENNReal.sub_eq_of_eq_add_rev]; norm_num
  rw [ENNReal.div_add_div_same]; eq_as_reals

lemma door_opened_by_host_when_car_equals_pick {pick host : Door} (hnp : host ≠ pick) :
  Prob[host_opens host | car_at pick] = 1/2 := by
  unfold Prob
  rw [cond_apply]
  simp only [host_opens, car_at]
  have h_inter : {ω : Game | ω.car = pick} ∩ {ω : Game | ω.host = host} = {ω : Game | ω.car = pick ∧ ω.host = host} := by
    ext ω; simp
  rw [h_inter, set_to_finset_conv, set_to_finset_conv,
      PMF.toMeasure_apply_finset, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, car_finset_card, car_host_card hnp, total_games]
  norm_num; eq_as_reals

lemma door_opened_by_host_when_car_not_equals_pick {pick host : Door} (hnp : host ≠ pick) :
  Prob[host_opens host | (car_at pick)ᶜ] = 1/2 := by
  sorry

theorem monty_hall_stay_probability (pick host : Door) (hnp : host ≠ pick) :
  Prob[car_at pick | host_opens host] = 1/3 := by
  rw [cond_eq_inv_mul_cond_mul (by trivial) (by trivial)]
  nth_rewrite 1 [law_of_total_probability Prob (host_opens host) (car_at pick)]
  · rw [door_opened_by_host_when_car_equals_pick hnp, car_behind_door,
        door_opened_by_host_when_car_not_equals_pick hnp, car_not_behind_door]
    ring_nf; norm_num; eq_as_reals
  · trivial
  · trivial
