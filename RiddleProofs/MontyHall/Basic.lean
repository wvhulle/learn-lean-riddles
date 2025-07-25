import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Distributions.Uniform
import ENNRealArith
open PMF
/-!
# The Monty Hall Problem

## Statement**

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
| left    -- Door 1
| middle  -- Door 2
| right   -- Door 3
deriving DecidableEq, Repr, Fintype

instance : Nonempty Door := ⟨Door.left⟩

structure Game where
  car   : Door  -- which door has the car behind it
  pick  : Door  -- which door the contestant initially picks
  host  : Door  -- which door the host opens (must have a goat)
  host_not_pick: host ≠ pick
  host_not_car: host ≠ car
  deriving DecidableEq, Repr, Fintype

open Door ProbabilityTheory MeasureTheory


instance measurableSpace : MeasurableSpace Game := ⊤



/-- The set of games where the host opens door d -/
def host_opens (d : Door) : Set Game := {ω | ω.host = d}

/-- The set of games where the car is behind door d -/
def car_at (d : Door) : Set Game := {ω | ω.car = d}

/-- The set of games where the player picks door d -/
def pick_door (d : Door) : Set Game := {ω | ω.pick = d}




@[ext]
theorem Game.ext {g₁ g₂ : Game} : g₁.car = g₂.car → g₁.pick = g₂.pick →
    g₁.host = g₂.host → g₁ = g₂ := by
  intro h₁ h₂ h₃
  cases g₁ with | mk c₁ p₁ h₁ =>
  cases g₂ with | mk c₂ p₂ h₂ =>
  simp at h₁ h₂ h₃
  simp [h₁, h₂, h₃]

-- Convert numbers 0,1,2 to doors (left, middle, right)
def fin_to_door (f : Fin 3) : Door :=
  match f with
  | 0 => left
  | 1 => middle
  | 2 => right

lemma fin_to_door_injective : Function.Injective fin_to_door := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [fin_to_door] at h <;> rfl

def game_triples := ({0, 1, 2} ×ˢ {0, 1, 2} ×ˢ {0, 1, 2} : Finset (Fin 3 × Fin 3 × Fin 3) )

def game_enumeration : Finset Game :=
  (Finset.univ : Finset Game)

theorem equivalence_game_repr : (Finset.univ : Finset Game) = game_enumeration := by
  rfl



def door_tuples := ({0, 1, 2} ×ˢ {0, 1, 2} : Finset (Fin 3 × Fin 3) )

def door_enumeration: Finset (Door × Door) :=
  door_tuples.map ⟨ (fun x => match x with
    | (door_1, door_2) => (fin_to_door door_1, fin_to_door door_2)), by
      unfold Function.Injective
      intros a b h
      simp at h
      refine Prod.ext_iff.mpr ?_
      constructor
      . exact fin_to_door_injective h.1
      . exact fin_to_door_injective h.2 ⟩

lemma equivalence_door_repr: (Finset.univ : Finset (Door × Door)) = door_enumeration := by rfl

instance: Nonempty Game :=
  ⟨ {pick := left, host := right, car := middle, host_not_car := (by simp), host_not_pick := (by simp)} ⟩

noncomputable def p  :=
  PMF.uniformOfFintype Game

notation:max "ℙ[" A "]" => p.toMeasure A

noncomputable def Prob := p.toMeasure

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance


/-- Apply a permutation of doors to a game -/
def permute_game (σ : Equiv.Perm Door) (g : Game) : Game where
  car := σ g.car
  pick := σ g.pick
  host := σ g.host
  host_not_pick := σ.injective.ne g.host_not_pick
  host_not_car := σ.injective.ne g.host_not_car

/-- Two games are equivalent if one can be obtained from the other by a door permutation -/
def GameEquiv : Game → Game → Prop :=
  fun g₁ g₂ => ∃ σ : Equiv.Perm Door, permute_game σ g₁ = g₂


open Equiv

instance: Equivalence GameEquiv where
  refl g := ⟨1, by ext <;> simp [permute_game]⟩
  symm {g₁ g₂} := fun ⟨σ, h⟩ => ⟨σ⁻¹, by
    rw [← h]
    ext <;> simp [permute_game]⟩
  trans {g₁ g₂ g₃} := fun ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ => ⟨σ₂ * σ₁, by
    rw [← h₂, ← h₁]
    ext <;> simp [permute_game, Perm.mul_apply]⟩



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


lemma total_games : Fintype.card Game = 12 := by
  decide

lemma car_finset_card { car: Door} : (Finset.univ.filter (fun (ω : Game) => ω.car = car)).card = 4 := by
  fin_cases car <;> decide

-- Count games where host opens a specific door AND car is at a specific position
lemma host_car_finset_card { host car: Door} (hnc: host ≠ car) :
  (Finset.univ.filter (fun (ω : Game) => ω.host = host ∧ ω.car = car)).card = 2 := by
  fin_cases host <;> fin_cases car <;> simp at hnc <;> decide

-- General conversion lemma for sets to finsets
lemma set_to_finset_conv {P : Game → Prop} [DecidablePred P] :
  {(ω : Game) | P ω} = ↑(Finset.univ.filter P) := by
  ext ω
  simp [Finset.mem_univ]

lemma car_set_to_finset { car: Door} : {(ω : Game) | ω.car = car} = ↑(Finset.univ.filter (fun (ω : Game) => ω.car = car)) := by
  exact set_to_finset_conv

lemma host_car_set_to_finset { host car: Door} :
  {(ω : Game) | ω.host = host ∧ ω.car = car} = ↑(Finset.univ.filter (fun (ω : Game) => ω.host = host ∧ ω.car = car)) := by
  exact set_to_finset_conv


lemma car_host_set_to_finset { car host: Door} :
  {(ω : Game) | ω.car = car ∧ ω.host = host} = ↑(Finset.univ.filter (fun (ω : Game) => ω.car = car ∧ ω.host = host)) := by
  exact set_to_finset_conv

-- Conversion lemma for pick, host and car triple
lemma pick_host_car_set_to_finset { pick host car: Door} :
  {(ω : Game) | ω.car = car ∧ ω.host = host ∧ ω.pick = pick} = ↑(Finset.univ.filter (fun (ω : Game) => ω.car = car ∧ ω.host = host ∧ ω.pick = pick)) := by
  exact set_to_finset_conv



lemma car_behind_door { car: Door}: Prob (car_at car) = 1 / 3 := by
    unfold Prob p car_at
    rw [car_set_to_finset]
    rw [PMF.toMeasure_apply_finset]
    simp only [PMF.uniformOfFintype_apply]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [car_finset_card]
    rw [total_games]
    norm_num
    eq_as_reals

lemma host_car_card { host car: Door} (hnc: host ≠ car) : (Finset.univ.filter (fun (ω : Game) => ω.host = host ∧ ω.car = car)).card = 2 := by
  fin_cases host <;> fin_cases car <;> simp at hnc <;> decide

-- Same lemma but with reversed conjunction order
lemma car_host_card { car host: Door} (hnc: host ≠ car) : (Finset.univ.filter (fun (ω : Game) => ω.car = car ∧ ω.host = host)).card = 2 := by
  have h : (Finset.univ.filter (fun (ω : Game) => ω.car = car ∧ ω.host = host)) =
           (Finset.univ.filter (fun (ω : Game) => ω.host = host ∧ ω.car = car)) := by
    ext ω
    simp [and_comm]
  rw [h]
  exact host_car_card hnc


-- When car = pick, the host cannot open that door, so this probability is 0
lemma door_opened_by_host_when_car_equals_pick { pick host : Door} {hnp: host ≠ pick} :
  Prob[host_opens host | car_at pick] = 1/2 := by
  unfold Prob p
  rw [cond_apply]
  simp only [host_opens, car_at]
  -- Convert intersection to conjunction
  have h_inter : {(ω : Game) | ω.car = pick} ∩ {(ω : Game) | ω.host = host} =
                 {(ω : Game) | ω.car = pick ∧ ω.host = host} := by
    ext ω
    simp [Set.mem_inter_iff]
  rw [h_inter]
  -- Convert to finsets
  have h_conv1 : {(ω : Game) | ω.car = pick} = ↑(Finset.univ.filter (fun (ω : Game) => ω.car = pick)) := by
    exact set_to_finset_conv
  have h_conv2 : {(ω : Game) | ω.car = pick ∧ ω.host = host} =
                 ↑(Finset.univ.filter (fun (ω : Game) => ω.car = pick ∧ ω.host = host)) := by
    exact set_to_finset_conv
  rw [h_conv1, h_conv2]
  rw [PMF.toMeasure_apply_finset, PMF.toMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply]
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  -- Count cardinalities
  have h_pick_card : (Finset.univ.filter (fun (ω : Game) => ω.car = pick)).card = 4 := by
    exact car_finset_card
  have h_pick_host_card : (Finset.univ.filter (fun (ω : Game) => ω.car = pick ∧ ω.host = host)).card = 2 := by
    -- When car = pick, host ≠ pick, there are 2 games (one for each possible player pick)
    exact car_host_card hnp
  rw [h_pick_card, h_pick_host_card, total_games]
  -- Now we have: (4 * 12⁻¹)⁻¹ * (2 * 12⁻¹) = 1/2
  norm_num
  eq_as_reals

lemma door_opened_by_host_when_car_not_equals_pick { pick host : Door} {hnp: host ≠ pick} :
  Prob[host_opens host | (car_at pick)ᶜ] = 1/2 := by
  unfold Prob p
  rw [cond_apply]
  · simp only [host_opens]
    sorry
  · trivial

lemma car_not_behind_door {car: Door} : Prob ((car_at car)ᶜ) = 2/3 := by
  -- Use that Prob(car_at car) = 1/3 and Prob(Aᶜ) = 1 - Prob(A)
  have h_car : Prob (car_at car) = 1/3 := car_behind_door
  rw [measure_compl (by trivial) (by exact measure_ne_top Prob _)]
  rw [measure_univ, h_car]
  rw [ENNReal.sub_eq_of_eq_add_rev]
  norm_num
  rw [ENNReal.div_add_div_same]
  eq_as_reals

theorem monty_hall_stay_probability (pick host : Door) (hnp: host ≠ pick) : Prob[car_at pick | host_opens host] = 1/3 := by
    rw [ProbabilityTheory.cond_eq_inv_mul_cond_mul (by exact trivial) (by exact trivial)]
    nth_rewrite 1 [law_of_total_probability Prob (host_opens host) (car_at pick)]
    · rw [@door_opened_by_host_when_car_equals_pick pick host hnp, car_behind_door,
          @door_opened_by_host_when_car_not_equals_pick pick host hnp, car_not_behind_door]
      have: ((1/2) * (1/3) + (1/2) * (2/3))⁻¹ * (1/2) * (1/3) = 1/(3: ENNReal) := by
        ring_nf
        norm_num
        eq_as_reals
      rw [this]
    . trivial
    . trivial
