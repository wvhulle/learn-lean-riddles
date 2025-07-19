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
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Notation
import ENNRealArith

open Door ProbabilityTheory MeasureTheory ENNReal ENNRealArith



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

-- Helper lemmas for specific probabilities
lemma prob_car_middle_joint : monty_joint.toMeasure (car_at middle) = 1/3 := by
  -- The prior probability is preserved in the joint distribution
  -- This is because monty_joint is constructed by:
  -- 1. Drawing car from car_prior (uniform, so P(car=middle) = 1/3)
  -- 2. Drawing (pick,host) from monty_likelihood(car)
  -- 3. Combining into a Game
  -- The marginal probability P(car=middle) remains 1/3
  sorry

lemma prob_car_not_middle_joint : monty_joint.toMeasure (car_at middle)ᶜ = 2/3 := by
  rw [measure_compl MeasurableSet.of_discrete (measure_ne_top _ _)]
  rw [prob_car_middle_joint]
  simp only [measure_univ]
  refine ENNReal.sub_eq_of_eq_add_rev ?_ ?_
  norm_num
  rw [ENNReal.div_add_div_same]
  eq_as_reals

-- Key conditional probabilities
lemma cond_prob_E_given_H :
  ProbabilityTheory.cond (monty_joint.toMeasure) (car_at middle) (pick_door left ∩ host_opens right) = 1/3 := by
  -- When car is at middle and we pick left, host must open right
  -- So P(pick=left, host=right | car=middle) = P(pick=left | car=middle) = 1/3
  sorry

lemma cond_prob_E_given_not_H :
  ProbabilityTheory.cond (monty_joint.toMeasure) (car_at middle)ᶜ (pick_door left ∩ host_opens right) = 1/12 := by
  -- When car is not at middle (either left or right)
  -- If car=left and pick=left: host cannot open right (must open middle)
  -- If car=right and pick=left: host cannot open right (that's where car is)
  -- So we need to recalculate...
  sorry

-- Prove that our Bayesian model matches the original
lemma monty_joint_eq_p : monty_joint.toMeasure = p.toMeasure := by
  -- Show the two PMFs give the same probabilities for all games
  sorry

-- Main result using the Bayesian formulation
lemma explicit_total_bayesian :
  ProbabilityTheory.cond (monty_joint.toMeasure) (car_at middle) (pick_door left ∩ host_opens right) *
    monty_joint.toMeasure (car_at middle) +
  ProbabilityTheory.cond (monty_joint.toMeasure) (car_at middle)ᶜ (pick_door left ∩ host_opens right) *
    monty_joint.toMeasure (car_at middle)ᶜ = 1/6 := by
  -- Use the conditional probability lemmas
  rw [cond_prob_E_given_H, cond_prob_E_given_not_H]
  -- Use the prior probabilities
  rw [prob_car_middle_joint, prob_car_not_middle_joint]
  -- Simple arithmetic: 1/3 * 1/3 + 1/12 * 2/3 = 1/9 + 2/36 = 1/9 + 1/18 = 1/6
  norm_num
  eq_as_reals

-- Connect to the original explicit_total using the fact that monty_joint = p
theorem explicit_total_from_bayesian :
  Prob[pick_door left ∩ host_opens right | car_at middle] * p.toMeasure (car_at middle) +
  Prob[pick_door left ∩ host_opens right | (car_at middle)ᶜ] * p.toMeasure {ω | ω.car = middle}ᶜ = 1/6 := by
  -- Use the fact that p = monty_joint
  have h_eq1 : Prob = p.toMeasure := rfl
  have h_eq2 : monty_joint.toMeasure = p.toMeasure := monty_joint_eq_p
  rw [h_eq1]
  rw [← h_eq2]
  have h_car_eq : (car_at middle)ᶜ = {ω | ω.car = middle}ᶜ := by rfl
  rw [← h_car_eq]
  exact explicit_total_bayesian

-- Show this equals the marginal probability using law of total probability
theorem bayesian_total_probability :
  monty_joint.toMeasure (pick_door left ∩ host_opens right) = 1/6 := by
  -- Apply law_of_total_probability from Solution.lean
  have h_meas_event : MeasurableSet (pick_door left ∩ host_opens right) :=
    MeasurableSet.inter MeasurableSet.of_discrete MeasurableSet.of_discrete
  have h_meas_car : MeasurableSet (car_at middle) := MeasurableSet.of_discrete
  have h_prob : IsProbabilityMeasure monty_joint.toMeasure := inferInstance
  rw [law_of_total_probability monty_joint.toMeasure
       (pick_door left ∩ host_opens right) (car_at middle)
       (hA := h_meas_event) (hB := h_meas_car)]
  exact explicit_total_bayesian
