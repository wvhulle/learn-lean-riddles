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
  -- The marginal probability of car position is preserved in the joint distribution.
  -- Since car_prior is uniform (1/3 for each door), P(car = middle) = 1/3.

  -- Expand the joint distribution using PMF.bind
  simp only [monty_joint, car_at]
  rw [PMF.toMeasure_bind_apply _ _ _ MeasurableSet.of_discrete]

  -- The sum is: ∑' c, car_prior(c) * P(car = middle | we sampled c from car_prior)
  -- This equals: car_prior(middle) * 1 + car_prior(left) * 0 + car_prior(right) * 0

  -- For each door c, the mapped distribution assigns probability 1 to games with car = c
  have h_indicator : ∀ c : Door,
    ((monty_likelihood c).map (fun ph : Door × Door => (⟨c, ph.1, ph.2⟩ : Game))).toMeasure {ω | ω.car = middle} =
    if c = middle then 1 else 0 := by
    intro c
    -- After mapping, all games have car = c, so the measure is 1 if c = middle, 0 otherwise
    rw [PMF.toMeasure_map_apply _ _ _ (by measurability) MeasurableSet.of_discrete]
    simp only [Set.preimage_setOf_eq]
    split_ifs with h <;> simp [h, Set.setOf_true, Set.setOf_false]

  -- Substitute the indicator values
  simp only [h_indicator]

  -- The sum reduces to just car_prior(middle)
  rw [tsum_eq_single middle]
  · -- car_prior is uniform, so car_prior(middle) = 1/3
    simp only [car_prior, PMF.ofFintype_apply, if_true]
    -- Need to show: 1/3 * 1 = 1/3
    eq_as_reals
  · -- Other terms are 0
    intro c hc
    simp [if_neg hc]

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
  -- When car is at middle and we pick left, host must open right with probability 1/2
  -- So P(pick=left, host=right | car=middle) = P(pick=left) * P(host=right | pick=left, car=middle)
  -- = 1/3 * 1/2 = 1/6
  -- But wait, that's not right. Let me recalculate...
  -- Actually: P(E|H) = P(pick=left, host=right | car=middle) = likelihood_val(middle, left, right) = 1/3

  -- Use the definition of conditional probability
  rw [ProbabilityTheory.cond_apply MeasurableSet.of_discrete]
  rw [prob_car_middle_joint]

  -- Need to show: (1/3)⁻¹ * P(car=middle ∩ pick=left ∩ host=right) = 1/3
  -- Which means: P(car=middle ∩ pick=left ∩ host=right) = 1/9

  -- Reorder the intersection
  have h_inter_eq : car_at middle ∩ (pick_door left ∩ host_opens right) =
                    (pick_door left ∩ host_opens right) ∩ car_at middle := by
    ext; simp [Set.inter_comm]
  rw [h_inter_eq]

  -- The probability of this specific game configuration
  have h_game_prob : monty_joint.toMeasure ((pick_door left ∩ host_opens right) ∩ car_at middle) = 1/9 := by
    -- This equals car_prior(middle) * monty_likelihood(middle)(left, right)
    -- = 1/3 * 1/3 = 1/9

    -- First, rewrite the set as a singleton
    have h_set_eq : (pick_door left ∩ host_opens right) ∩ car_at middle =
                    {⟨middle, left, right⟩} := by
      ext ω
      simp only [pick_door, host_opens, car_at, Set.mem_inter_iff, Set.mem_setOf_eq,
                 Set.mem_singleton_iff]
      constructor
      · intro ⟨⟨h_pick, h_host⟩, h_car⟩
        ext <;> simp [h_pick, h_host, h_car]
      · intro h
        rw [h]
        simp

    rw [h_set_eq]

    -- Now compute the probability of this singleton
    rw [PMF.toMeasure_apply_singleton]

    -- Expand monty_joint
    simp only [monty_joint, PMF.bind_apply, PMF.map_apply]

    -- The sum has only one non-zero term: when we start with car=middle
    rw [tsum_eq_single middle]
    rw [tsum_eq_single]
    simp [car_prior, PMF.ofFintype_apply]
    sorry
    sorry
    sorry
    sorry
    sorry






  rw [h_game_prob]
  eq_as_reals

lemma cond_prob_E_given_not_H :
  ProbabilityTheory.cond (monty_joint.toMeasure) (car_at middle)ᶜ (pick_door left ∩ host_opens right) = 1/12 := by
  -- When car is not at middle (either left or right)
  -- We'll prove this directly by computing the probability

  -- Use the definition of conditional probability
  rw [ProbabilityTheory.cond_apply MeasurableSet.of_discrete]
  rw [prob_car_not_middle_joint]

  -- Need to show: (2/3)⁻¹ * P((car≠middle) ∩ (pick=left ∩ host=right)) = 1/12
  -- Which means: P((car≠middle) ∩ (pick=left ∩ host=right)) = 1/12 * 2/3 = 1/18

  -- The complement of car_at middle is the union of car_at left and car_at right
  have h_compl : (car_at middle)ᶜ ∩ (pick_door left ∩ host_opens right) =
                 (car_at left ∩ pick_door left ∩ host_opens right) ∪
                 (car_at right ∩ pick_door left ∩ host_opens right) := by
    ext ω
    simp only [car_at, pick_door, host_opens, Set.mem_compl_iff, Set.mem_setOf_eq,
               Set.mem_inter_iff, Set.mem_union]
    constructor
    · intro ⟨h_not_middle, h_pick, h_host⟩
      cases door_cases ω.car with
      | inl h => left; exact ⟨h, h_pick, h_host⟩
      | inr h => cases h with
        | inl h => exfalso; exact h_not_middle h
        | inr h => right; exact ⟨h, h_pick, h_host⟩
    · intro h
      cases h with
      | inl ⟨h_left, h_pick, h_host⟩ =>
        exact ⟨fun h => (by rw [h] at h_left; cases h_left), h_pick, h_host⟩
      | inr ⟨h_right, h_pick, h_host⟩ =>
        exact ⟨fun h => (by rw [h] at h_right; cases h_right), h_pick, h_host⟩

  rw [h_compl]

  -- The two sets are disjoint
  have h_disj : Disjoint (car_at left ∩ pick_door left ∩ host_opens right)
                         (car_at right ∩ pick_door left ∩ host_opens right) := by
    simp only [Set.disjoint_iff_inter_eq_empty]
    ext ω
    simp only [car_at, Set.mem_inter_iff, Set.mem_empty_iff_false, Set.mem_setOf_eq]
    intro ⟨h_left, _, _, h_right, _, _⟩
    have : left = right := by rw [← h_left, h_right]
    cases this

  rw [measure_union h_disj MeasurableSet.of_discrete]

  -- Calculate each part
  have h_left_prob : monty_joint.toMeasure (car_at left ∩ pick_door left ∩ host_opens right) = 1/18 := by
    -- This is the configuration {car=left, pick=left, host=right}
    have h_set : car_at left ∩ pick_door left ∩ host_opens right = {⟨left, left, right⟩} := by
      ext ω
      simp only [car_at, pick_door, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq,
                 Set.mem_singleton_iff]
      constructor
      · intro ⟨h_car, h_pick, h_host⟩
        ext <;> simp [h_car, h_pick, h_host]
      · intro h
        rw [h]
        simp

    rw [h_set, PMF.toMeasure_apply_singleton]
    simp only [monty_joint, PMF.bind_apply, PMF.map_apply]

    rw [Finset.sum_eq_single left]
    · simp only [car_prior, PMF.ofFintype_apply]
      simp only [monty_likelihood, PMF.ofFintype_apply]
      simp only [likelihood_val]
      -- When car=left, pick=left, host=right: valid config with car=pick
      simp
      norm_num
    · intro c hc _
      simp only [PMF.map_apply]
      apply Finset.sum_eq_zero
      intro ph _
      have : (⟨c, ph.1, ph.2⟩ : Game) ≠ ⟨left, left, right⟩ := by
        intro h
        injection h with h_car
        exact hc h_car
      simp [this]
    · simp

  have h_right_prob : monty_joint.toMeasure (car_at right ∩ pick_door left ∩ host_opens right) = 0 := by
    -- This is the configuration {car=right, pick=left, host=right}
    -- Invalid because host=car
    have h_set : car_at right ∩ pick_door left ∩ host_opens right = {⟨right, left, right⟩} := by
      ext ω
      simp only [car_at, pick_door, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq,
                 Set.mem_singleton_iff]
      constructor
      · intro ⟨h_car, h_pick, h_host⟩
        ext <;> simp [h_car, h_pick, h_host]
      · intro h
        rw [h]
        simp

    rw [h_set, PMF.toMeasure_apply_singleton]
    simp only [monty_joint, PMF.bind_apply, PMF.map_apply]

    rw [Finset.sum_eq_single right]
    · simp only [car_prior, PMF.ofFintype_apply]
      simp only [monty_likelihood, PMF.ofFintype_apply]
      simp only [likelihood_val]
      -- When car=right, pick=left, host=right: host=car, so 0
      simp
    · intro c hc _
      simp only [PMF.map_apply]
      apply Finset.sum_eq_zero
      intro ph _
      have : (⟨c, ph.1, ph.2⟩ : Game) ≠ ⟨right, left, right⟩ := by
        intro h
        injection h with h_car
        exact hc h_car
      simp [this]
    · simp

  rw [h_left_prob, h_right_prob]
  simp
  eq_as_reals

-- Prove that our Bayesian model matches the original
lemma monty_joint_eq_p : monty_joint.toMeasure = p.toMeasure := by
  -- Show the two PMFs give the same probabilities for all games
  -- Actually, I realize the issue: my likelihood_val is not the same as game_density
  -- because likelihood_val is conditional on the car position, while game_density
  -- is the joint probability.

  -- The relationship should be:
  -- game_density(g) = P(car=g.car) * P(pick=g.pick|car=g.car) * P(host=g.host|car=g.car,pick=g.pick)
  -- = 1/3 * 1/3 * likelihood_factor

  -- Where likelihood_factor is:
  -- - 0 if invalid (host = car or host = pick)
  -- - 1/2 if car = pick (host has 2 choices)
  -- - 1 if car ≠ pick (host has 1 choice)

  -- So game_density should be:
  -- - 0 if invalid
  -- - 1/3 * 1/3 * 1/2 = 1/18 if car = pick
  -- - 1/3 * 1/3 * 1 = 1/9 if car ≠ pick

  -- But the actual game_density is:
  -- - 0 if invalid
  -- - 1/18 if car = pick
  -- - 2/18 = 1/9 if car ≠ pick

  -- So they match! The issue is that my likelihood_val already includes the P(pick|car) term.
  -- Let me recalculate...

  -- Actually, likelihood_val(car, pick, host) represents P(pick, host | car), not just P(host | car, pick)
  -- So monty_joint(g) = car_prior(g.car) * likelihood_val(g.car, g.pick, g.host)
  --                   = 1/3 * likelihood_val(g.car, g.pick, g.host)

  -- And we need this to equal game_density(g)
  -- So likelihood_val should be 3 * game_density

  -- Let's verify:
  -- When car = pick and valid: likelihood_val = 1/6, game_density = 1/18
  -- 1/3 * 1/6 = 1/18 ✓

  -- When car ≠ pick and valid: likelihood_val = 1/3, game_density = 1/9
  -- 1/3 * 1/3 = 1/9 ✓

  -- So the relationship is correct! Let me prove it properly.

  apply Measure.ext
  intro s hs

  -- Both measures are discrete, so it suffices to check singletons
  -- For a general measurable set s, both measures decompose as sums over singletons

  -- Actually, let's use a different approach
  -- Show that for every game g, monty_joint(g) = p(g)

  have h_singleton : ∀ g : Game, monty_joint.toMeasure {g} = p.toMeasure {g} := by
    intro g
    rw [PMF.toMeasure_apply_singleton, PMF.toMeasure_apply_singleton]

    -- Expand monty_joint
    simp only [monty_joint, PMF.bind_apply, PMF.map_apply]

    -- The sum has only one non-zero term: when c = g.car
    rw [Finset.sum_eq_single g.car]
    · -- The g.car case
      simp only [car_prior, PMF.ofFintype_apply]
      rw [Finset.sum_eq_single (g.pick, g.host)]
      · -- The (g.pick, g.host) case
        simp only [monty_likelihood, PMF.ofFintype_apply]
        simp

        -- Now show: 1/3 * likelihood_val g.car g.pick g.host = game_density g
        have h_eq : (1:ENNReal)/3 * likelihood_val g.car g.pick g.host = game_density g := by
          simp only [likelihood_val, game_density]
          split_ifs with h1 h2
          · -- Invalid cases: both give 0
            simp
          · -- car = pick case
            push_neg at h1
            norm_num
          · -- car ≠ pick case
            push_neg at h1
            norm_num
            eq_as_reals

        -- Use the PMF definition
        simp only [p, PMF.ofFinset_apply]
        rw [← h_eq]
        simp

      · -- Other (pick, host) pairs give different games
        intro ph hph hph_in
        simp
        intro h_eq
        apply hph
        ext <;> [exact h_eq.1, exact h_eq.2]

      · -- (g.pick, g.host) is in the support
        simp [monty_likelihood, PMF.support_ofFintype]

    · -- Other car positions give different games
      intro c hc _
      simp only [PMF.map_apply]
      apply Finset.sum_eq_zero
      intro ph _
      simp
      intro h_contra
      apply hc
      exact h_contra

    · -- g.car is in the support
      simp [car_prior, PMF.support_ofFintype]

  -- Now use the fact that discrete measures are determined by their values on singletons
  -- We've shown the measures agree on all singletons
  -- For discrete spaces with countable support, this implies the measures are equal

  -- Use the characterization that measures on discrete spaces are determined by singletons
  have h_discrete : ∀ t : Set Game, MeasurableSet t →
    monty_joint.toMeasure t = ∑' g : Game, if g ∈ t then monty_joint.toMeasure {g} else 0 := by
    intro t ht
    exact PMF.toMeasure_apply_eq_sum_singleton _ t

  have h_discrete_p : ∀ t : Set Game, MeasurableSet t →
    p.toMeasure t = ∑' g : Game, if g ∈ t then p.toMeasure {g} else 0 := by
    intro t ht
    exact PMF.toMeasure_apply_eq_sum_singleton _ t

  rw [h_discrete s hs, h_discrete_p s hs]
  congr 1
  ext g
  split_ifs
  · exact h_singleton g
  · rfl

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
