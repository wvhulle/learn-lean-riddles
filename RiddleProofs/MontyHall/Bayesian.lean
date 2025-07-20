/-
# Bayesian Approach to the Monty Hall Problem

This file implements a Bayesian formulation of the Monty Hall problem using
proper probability mass functions (PMFs) from Mathlib.

The key idea is to define:
- A prior distribution over car locations
- A likelihood function P(pick, host | car)
- The joint distribution using Bayes' rule

This provides a cleaner and more modular approach compared to computing
everything from the explicit game_density.
-/

import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.Solution  -- To use law_of_total_probability
import RiddleProofs.MontyHall.Enumeration  -- For fin_to_door
import RiddleProofs.MontyHall.Measure  -- For p and game_density
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Notation
import ENNRealArith

open Door ProbabilityTheory MeasureTheory ENNReal ENNRealArith

-- Game has a discrete measurable space structure
instance : MeasurableSingletonClass Game := ⟨fun _ => MeasurableSet.of_discrete⟩



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

-- Helper lemma: Door has exactly 3 elements
lemma door_card : Fintype.card Door = 3 := by
  -- Count the constructors: left, middle, right
  rfl

-- Prior distribution: car is equally likely behind each door
noncomputable def car_prior : PMF Door :=
  PMF.ofFintype (fun _ => (1 : ENNReal) / 3) (by
    simp only [Finset.sum_const, Finset.card_univ]
    rw [door_card]
    rw [<- toReal_eq_one_iff]
    eq_as_reals)

-- Raw likelihood values for P(pick, host | car)
noncomputable def likelihood_val (car pick host : Door) : ENNReal :=
  if host = car ∨ host = pick then 0    -- Invalid configurations
  else if car = pick then
    -- Contestant picks the car: host uniformly chooses from 2 remaining doors
    -- P(pick = car | car) = 1/3 (uniform pick)
    -- P(host | pick = car, car) = 1/2 (2 valid doors)
    -- So P(pick, host | car) = 1/3 × 1/2 = 1/6
    (1 : ENNReal) / 6
  else
    -- Contestant picks a goat: host must open the other goat door
    -- P(pick ≠ car | car) = 1/3 for each of the 2 goat doors
    -- P(host | pick ≠ car, car) = 1 (forced choice)
    -- So P(pick, host | car) = 1/3 × 1 = 1/3
    (1 : ENNReal) / 3


-- Define the inverse of fin_to_door
def door_to_fin : Door → Fin 3
  | left => 0
  | middle => 1
  | right => 2

lemma door_to_fin_to_door (d : Door) : fin_to_door (door_to_fin d) = d := by
  cases d <;> rfl

lemma fin_to_door_to_fin (i : Fin 3) : door_to_fin (fin_to_door i) = i := by
  fin_cases i <;> rfl

lemma door_to_fin_injective : Function.Injective door_to_fin := by
  intro a b h
  cases a <;> cases b <;> simp [door_to_fin] at h <;> try rfl

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

lemma likelihood_val_sum_one (car : Door) :
  ∑ p : Door × Door, likelihood_val car p.1 p.2 = 1 := by

  simp [equivalence_door_repr]
  simp [door_enumeration]
  simp [door_tuples]
  simp [Finset.sum_product]
  simp [fin_to_door]
  simp [likelihood_val]
  cases car
  case left =>
     split_ifs <;> (first | contradiction | eq_as_reals)
  case middle =>
    split_ifs <;> (first | contradiction | eq_as_reals)
  case right =>
    split_ifs <;> (first | contradiction | eq_as_reals)

-- Likelihood function: P(pick, host | car)
-- Given where the car is, what are the probabilities of (pick, host) pairs?
noncomputable def monty_likelihood (car : Door) : PMF (Door × Door) :=
  PMF.ofFintype (fun (pick, host) => likelihood_val car pick host)
  (likelihood_val_sum_one car)


-- Joint distribution over games using the prior and likelihood
noncomputable def monty_joint : PMF Game :=
  car_prior.bind (fun car =>
    (monty_likelihood car).map (fun (pick, host) => ⟨car, pick, host⟩))

-- Helper lemma: Measure of singleton for joint distribution
lemma prob_game_joint_measure (g : Game) : monty_joint.toMeasure {g} =
    car_prior g.car * likelihood_val g.car g.pick g.host := by
  rw [PMF.toMeasure_apply_singleton, monty_joint, PMF.bind_apply]
  -- Simplify the sum over all car positions
  trans (∑' c, car_prior c * (PMF.map (fun ph => ⟨c, ph.1, ph.2⟩) (monty_likelihood c)) g)
  · rfl
  -- Each PMF.map term gives the probability that the constructed game equals g
  have h_map : ∀ c, (PMF.map (fun ph => ⟨c, ph.1, ph.2⟩) (monty_likelihood c)) g =
               if c = g.car then monty_likelihood c (g.pick, g.host) else 0 := by
    intro c
    rw [PMF.map_apply]
    by_cases hc : c = g.car
    · -- When c = g.car
      subst hc
      simp only [if_true]
      rw [tsum_eq_single (g.pick, g.host)]
      · have : (⟨g.car, g.pick, g.host⟩ : Game) = g := by cases g; rfl
        simp [this]
      · intro ph hph
        split_ifs with heq
        · exfalso
          have : ph = (g.pick, g.host) := by
            have ⟨_, _, _⟩ := g
            cases heq
            rfl
          exact hph this
        · rfl
    · -- When c ≠ g.car
      rw [if_neg hc]
      simp
      intros a b h
      have hc_neg: c = g.car := by
        rw [h]
      contradiction
  simp only [h_map]
  -- Sum simplifies to just the g.car term
  rw [tsum_eq_single g.car]
  · simp only [if_true, monty_likelihood, PMF.ofFintype_apply]
  · intro c hc; simp [hc]
  · measurability

-- Helper lemma: P(pick=left ∩ host=right)
lemma prob_pick_left_host_right_joint :
  monty_joint.toMeasure (pick_door left ∩ host_opens right) = 1/6 := by
  -- This event consists of games where pick=left and host=right, for any car position
  -- Sum over all three possible car positions
  -- Decompose the event by car position
  have h_decomp : pick_door left ∩ host_opens right =
    {⟨left, left, right⟩} ∪ {⟨middle, left, right⟩} ∪ {⟨right, left, right⟩} := by
    ext g
    simp only [pick_door, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq,
               Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro ⟨hp, hh⟩
      -- g.pick = left and g.host = right
      cases g with
      | mk car pick host =>
        simp only at hp hh
        subst hp hh
        cases car <;> simp
    · intro h
      rcases h with (rfl | rfl) | rfl <;> simp

  rw [h_decomp]
  -- The last set has probability 0 since host=car
  have h_zero : monty_joint.toMeasure {⟨right, left, right⟩} = 0 := by
    rw [prob_game_joint_measure]
    simp only [car_prior, PMF.ofFintype_apply, likelihood_val]
    -- host=right=car, so likelihood is 0
    norm_num

  -- We can rewrite the union
  rw [Set.union_assoc]

  -- Since the third set has measure 0, we can calculate the measure of the union
  have h_disj1 : Disjoint ({⟨left, left, right⟩} : Set Game)
                         ({⟨middle, left, right⟩} ∪ {⟨right, left, right⟩}) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_union, Set.mem_singleton_iff]
    push_neg
    constructor <;> simp

  have h_disj2 : Disjoint ({⟨middle, left, right⟩} : Set Game) ({⟨right, left, right⟩} : Set Game) := by
    simp
  rw [measure_union h_disj1]
  rw [measure_union h_disj2]
  rw [h_zero, add_zero]

  -- Calculate each probability using prob_game_joint_measure
  rw [prob_game_joint_measure, prob_game_joint_measure]
  simp only [car_prior, PMF.ofFintype_apply, likelihood_val]
  -- For {left, left, right}: car=left, pick=left, host=right
  -- likelihood_val left left right = 1/6 (car=pick case)
  -- For {middle, left, right}: car=middle, pick=left, host=right
  -- likelihood_val middle left right = 1/3 (car≠pick case)
  simp only [if_true]
  -- We have (1/3 * 1/6) + (1/3 * 1/3) = 1/18 + 1/9 = 1/18 + 2/18 = 3/18 = 1/6
  simp
  eq_as_reals

-- Conditional probability lemmas for the Monty Hall problem
lemma prob_stay_wins_given_pick_left_host_right :
  (monty_joint.toMeasure)[car_at left | pick_door left ∩ host_opens right] = 1/3 := by
  -- Use the definition of conditional probability: P(A|B) = P(A∩B)/P(B)
  have h_meas : MeasurableSet (pick_door left ∩ host_opens right) := by
    apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
  rw [ProbabilityTheory.cond_apply h_meas]

  -- Calculate P(car=left ∩ pick=left ∩ host=right) / P(pick=left ∩ host=right)
  have h_inter : (pick_door left ∩ host_opens right) ∩ car_at left = {⟨left, left, right⟩} := by
    ext g
    simp only [car_at, pick_door, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨⟨hp, hh⟩, hc⟩
      simp [Game.ext_iff, hc, hp, hh]
    · intro h
      rw [h]
      simp

  rw [h_inter]
  rw [prob_pick_left_host_right_joint]
  rw [prob_game_joint_measure]
  simp only [car_prior, PMF.ofFintype_apply, likelihood_val]
  -- car=left, pick=left, host=right: likelihood is 1/6 (car=pick case)
  -- The goal is: (if right = left then 0 else 1/6 * 2) = 1/3
  -- Since right ≠ left, this becomes: 1/6 * 2 = 1/3
  split_ifs <;> (first | contradiction | eq_as_reals)

lemma prob_switch_wins_given_pick_left_host_right :
  (monty_joint.toMeasure)[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  -- Use the definition of conditional probability: P(A|B) = P(A∩B)/P(B)
  have h_meas : MeasurableSet (pick_door left ∩ host_opens right) := by
    apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
  rw [ProbabilityTheory.cond_apply h_meas]

  -- Calculate P(car=middle ∩ pick=left ∩ host=right) / P(pick=left ∩ host=right)
  have h_inter : (pick_door left ∩ host_opens right) ∩ car_at middle = {⟨middle, left, right⟩} := by
    ext g
    simp only [car_at, pick_door, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro ⟨⟨hp, hh⟩, hc⟩
      simp [Game.ext_iff, hc, hp, hh]
    · intro h
      rw [h]
      simp

  rw [h_inter]
  rw [prob_pick_left_host_right_joint]
  rw [prob_game_joint_measure]
  simp only [car_prior, PMF.ofFintype_apply, likelihood_val]
  -- car=middle, pick=left, host=right: likelihood is 1/3 (car≠pick case)
  -- The goal should be: 1/3 * 1/3 * 6 = 2/3
  -- Since host ≠ car and host ≠ pick and car ≠ pick
  simp only [if_neg (show ¬(right = middle ∨ right = left) from by simp),
             if_neg (show ¬(middle = left) from by simp)]
  eq_as_reals

/-- The Monty Hall theorem: Switching doors doubles your probability of winning.
This theorem shows that the optimal strategy is to switch doors. -/
theorem monty_hall_switch_optimal :
  (monty_joint.toMeasure)[car_at middle | pick_door left ∩ host_opens right] =
  2 * (monty_joint.toMeasure)[car_at left | pick_door left ∩ host_opens right] := by
  rw [prob_switch_wins_given_pick_left_host_right, prob_stay_wins_given_pick_left_host_right]
  eq_as_reals
