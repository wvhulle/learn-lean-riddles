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

def host_opens (d : Door) : Set Game := {ω | ω.host = d}

def car_at (d : Door) : Set Game := {ω | ω.car = d}

def pick_door (d : Door) : Set Game := {ω | ω.pick = d}

instance (d : Door) : MeasurableSet (host_opens d) :=
  DiscreteMeasurableSpace.forall_measurableSet _

instance (d : Door) : MeasurableSet (car_at d) :=
  DiscreteMeasurableSpace.forall_measurableSet _

instance (d : Door) : MeasurableSet (pick_door d) :=
  DiscreteMeasurableSpace.forall_measurableSet _




theorem bayes_monty_hall_mathlib (pick_d host_d : Door) (h_ne : pick_d ≠ host_d) :
  let remaining_d := remaining_door pick_d host_d
  let evidence := host_opens host_d ∩ pick_door pick_d
  Prob[car_at remaining_d | evidence] > Prob[car_at pick_d | evidence] := by
  set remaining_d := remaining_door pick_d host_d
  set evidence := host_opens host_d ∩ pick_door pick_d
  have bayes_remaining : Prob[car_at remaining_d | evidence] =
    (Prob evidence)⁻¹ * Prob[evidence | car_at remaining_d] * Prob (car_at remaining_d) := by
    rw [ProbabilityTheory.cond_eq_inv_mul_cond_mul]
    · exact DiscreteMeasurableSpace.forall_measurableSet _
    · exact DiscreteMeasurableSpace.forall_measurableSet _
  have bayes_pick : Prob[car_at pick_d | evidence] =
    (Prob evidence)⁻¹ * Prob[evidence | car_at pick_d] * Prob (car_at pick_d) := by
    rw [ProbabilityTheory.cond_eq_inv_mul_cond_mul]
    · exact DiscreteMeasurableSpace.forall_measurableSet _
    · exact DiscreteMeasurableSpace.forall_measurableSet _
  sorry
