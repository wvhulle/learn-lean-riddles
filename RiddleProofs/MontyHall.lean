import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Basic
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

def is_valid_game : Game → Prop := fun (ω : Game) => ω.host ≠ ω.pick ∧ ω.host ≠ ω.car

instance : DecidablePred is_valid_game := by
  unfold is_valid_game
  infer_instance

def valid_games_finset : Finset Game :=
  Finset.filter is_valid_game (Finset.univ : Finset Game)

lemma valid_games_nonempty : valid_games_finset.Nonempty := by
  use {car := left, pick := left, host := middle}
  simp [valid_games_finset, Finset.mem_filter, Finset.mem_univ, is_valid_game]

noncomputable def p : PMF Game :=
  PMF.uniformOfFinset valid_games_finset valid_games_nonempty




noncomputable def Prob  := p.toMeasure

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance

def host_opens (d : Door) : Set Game := {ω | ω.host = d}

def car_at (d : Door) : Set Game := {ω | ω.car = d}

def pick_door (d : Door) : Set Game := {ω | ω.pick = d}

theorem simplified_monty_hall: Prob[car_at left | pick_door left ∩ host_opens right ∪ pick_door left ∩ host_opens middle] = 1/3 := by
    set H := car_at left
    set E := pick_door left ∩ host_opens right ∪ pick_door left ∩ host_opens middle

    have prior_car_left: Prob H   = 1/3  := by
      unfold H car_at Prob
      simp [PMF.toMeasure_apply_finset]
      show ∑ x, {ω | ω.car = left}.indicator (⇑p) x = 3⁻¹
      /-
      How can convert this into an expression that is computable?
      Should I change the index set to  `game_enumeration`? I have encountered that transforming the index set into  something that is more easily enumerable may help in reducing the sum.
      -/
      sorry
    have prior_car_not_left: Prob Hᶜ = 2/3 := by
      rw [MeasureTheory.prob_compl_eq_one_sub (DiscreteMeasurableSpace.forall_measurableSet H)]
      simp [prior_car_left]
      rw [<- ENNReal.div_self (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ⊤)]
      have: (3 : ENNReal)⁻¹ = 1/3 := by
        norm_num
      rw [this]
      rw [ENNReal.sub_eq_of_eq_add]
      · rw [<- ENNReal.inv_ne_zero]
        norm_num
      · rw [ENNReal.div_add_div_same]
        norm_num

    have shows_goat_left_car : Prob[E | H] = 1 := by
      /-
      This should be one according to the rules of the game. The host will always open a door with a goat behind it. If the car is at left, and we pick left, then the host will open middle or right.
      -/

      simp [ProbabilityTheory.cond_apply]
      rw [prior_car_left]
      norm_num
      have: Prob (H ∩ E) = 1 / 3 := by
        sorry
      rw [this]
      norm_num
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    have shows_goat_no_left_car : Prob[E | H ᶜ ] = 1 := by
      /-
      The probability that the host shows a goat when the care is not at the left. It should be 1, because the host will always open a door with a goat behind it.
      -/
      simp [ProbabilityTheory.cond_apply]
      rw [prior_car_not_left]
      sorry
    have:  Prob[H | E] = 1/3 := by
      rw [ProbabilityTheory.cond_eq_inv_mul_cond_mul (DiscreteMeasurableSpace.forall_measurableSet _) (DiscreteMeasurableSpace.forall_measurableSet _) Prob]
      rw [<- cond_add_cond_compl_eq (DiscreteMeasurableSpace.forall_measurableSet H)]
      rw [shows_goat_left_car, shows_goat_no_left_car, prior_car_left, prior_car_not_left]
      simp only [one_mul]
      rw [ENNReal.div_add_div_same]
      norm_num
      simp only [ENNReal.div_self (by norm_num : (3 : ENNReal) ≠ 0) (by norm_num : (3 : ENNReal) ≠ ⊤)]
      simp only [inv_one, one_mul]
    unfold H E at this
    exact this
