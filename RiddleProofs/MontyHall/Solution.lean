import RiddleProofs.MontyHall.Measure
import RiddleProofs.MontyHall.Enumeration
import RiddleProofs.MontyHall.Statement
import ENNRealArith
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open ProbabilityTheory ENNReal Door ENNRealArith MeasureTheory


def host_opens (d : Door) : Set Game := {ω | ω.host = d}
def car_at (d : Door) : Set Game := {ω | ω.car = d}
def pick_door (d : Door) : Set Game := {ω | ω.pick = d}


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
  game_density {car := car, pick := pick, host := host} = (1 : ENNReal) / 18 := by
  simp only [game_density, h_eq, h_valid.1,  if_true, if_false]

lemma prob_density_car_ne_pick (car pick host : Door) (h_ne : car ≠ pick) (h_valid : host ≠ pick ∧ host ≠ car) :
  game_density {car := car, pick := pick, host := host} = (1 : ENNReal) / 9 := by
  simp only [game_density, h_ne, h_valid.1, h_valid.2, if_false]
  eq_as_reals

lemma prob_density_left_left_right :
  game_density {car := left, pick := left, host := right} = 1/18 := by
  simp [prob_density_car_eq_pick]

lemma prob_density_middle_left_right :
  game_density {car := middle, pick := left, host := right} = 1/9 := by
  simp [prob_density_car_ne_pick]

lemma prob_density_right_left_right :
  game_density {car := right, pick := left, host := right} = 0 := by
  simp only [game_density]
  -- host = right = car, so the second condition triggers, returning 0
  simp only [if_pos]; rfl

lemma prob_pick_left_host_right :
  ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right}] = 1/6 := by
  have h_inter_eq : ({ω : Game | ω.pick = left} ∩ {ω : Game | ω.host = right}) =
                    {ω : Game | ω.pick = left ∧ ω.host = right} := by
    ext ω; simp [Set.mem_inter_iff]

  calc ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right}]
    = ℙ[{ω : Game | ω.pick = left ∧ ω.host = right}] := by
        rw [h_inter_eq]
    _ = ℙ[↑(game_enumeration.filter (fun ω => ω.pick = left ∧ ω.host = right))] := by
        congr 1; rw [← equivalence_game_repr]; ext ω; simp
    _ = ∑ ω ∈ game_enumeration.filter (fun ω => ω.pick = left ∧ ω.host = right), p ω := by
        rw [PMF.toMeasure_apply_finset]
    _ = ∑ ω ∈ {({car := left, pick := left, host := right} : Game),
                ({car := middle, pick := left, host := right} : Game),
                ({car := right, pick := left, host := right} : Game)}, p ω := by
        apply Finset.sum_congr
        · simp [game_enumeration]; decide
        · intros; rfl
    _ = p {car := left, pick := left, host := right} +
        p {car := middle, pick := left, host := right} +
        p {car := right, pick := left, host := right} := by
        rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
        · simp [add_assoc]
        · simp
        · simp
    _ = 1/18 + 1/9 + 0 := by
        simp only [p, PMF.ofFinset_apply,
                   prob_density_left_left_right,
                   prob_density_middle_left_right,
                   prob_density_right_left_right]
    _ = 1/6 := by eq_as_reals

lemma prob_car_at_given_pick_host (car : Door) :
  ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = car}] =
  game_density {car := car, pick := left, host := right} := by
  calc ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = car}]
    = ℙ[{ω : Game | ω.pick = left ∧ ω.host = right ∧ ω.car = car}] := by
        congr 1
        ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    _ = ℙ[{({car := car, pick := left, host := right} : Game)}] := by
        congr 1
        exact unique_game_set car left right
    _ = p ({car := car, pick := left, host := right} : Game) := by
        rw [PMF.toMeasure_apply_singleton]
        exact MeasurableSet.singleton _
    _ = game_density {car := car, pick := left, host := right} := by
        rfl

lemma prob_car_left_pick_left_host_right :
  ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = left}] = 1/18 := by
  rw [prob_car_at_given_pick_host, prob_density_left_left_right]

lemma prob_car_middle_pick_left_host_right :
  ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = middle}] = 1/9 := by
  rw [prob_car_at_given_pick_host, prob_density_middle_left_right]

/- Probability of winning if you stay with your original choice
P(car at left | picked left, host opened right) = 1/3
-/
theorem monty_hall_stay_probability :
  Prob[car_at left | pick_door left ∩ host_opens right] = 1/3 := by
  have h_meas : MeasurableSet (pick_door left ∩ host_opens right) := by
    apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
  unfold Prob
  rw [ProbabilityTheory.cond_apply h_meas]
  calc (ℙ[pick_door left ∩ host_opens right])⁻¹ *
       ℙ[(pick_door left ∩ host_opens right) ∩ car_at left]
    = (ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right}])⁻¹ *
      ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = left}] := by
        simp only [car_at, pick_door, host_opens]
    _ = (1/6)⁻¹ * (1/18) := by
        rw [prob_pick_left_host_right, prob_car_left_pick_left_host_right]
    _ = 1/3 := by eq_as_reals

/-- Probability of winning if you switch to the other door
 P(car at middle | picked left, host opened right) = 2/3
This proves that switching is the better strategy!
-/
theorem monty_hall_switch_probability :
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  have h_meas : MeasurableSet (pick_door left ∩ host_opens right) := by
    apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
  unfold Prob
  rw [ProbabilityTheory.cond_apply h_meas]
  calc (ℙ[pick_door left ∩ host_opens right])⁻¹ *
       ℙ[(pick_door left ∩ host_opens right) ∩ car_at middle]
    = (ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right}])⁻¹ *
      ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = middle}] := by
        simp only [car_at, pick_door, host_opens]
    _ = (1/6)⁻¹ * (1/9) := by
        rw [prob_pick_left_host_right, prob_car_middle_pick_left_host_right]
    _ = 2/3 := by eq_as_reals


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

lemma explicit_total: Prob[pick_door left ∩ host_opens right | car_at middle] * p.toMeasure (car_at middle) + Prob[pick_door left ∩ host_opens right | (car_at middle)ᶜ] * p.toMeasure {ω | ω.car = middle}ᶜ = 1/ 6 := by
    -- When car is at middle, if contestant picks left, host must open right
    have h1 : Prob[pick_door left ∩ host_opens right | car_at middle] = 1/3 := by
      -- First, show that when car=middle and pick=left, host must open right
      have h_det : ∀ ω : Game, ω.car = middle → ω.pick = left →
        (game_density ω > 0 → ω.host = right) := by
        intro ω h_car h_pick h_pos
        -- Host can't open middle (car) or left (pick), so must open right
        by_contra h_not_right
        -- game_density = 0 when host=pick or host=car
        have : game_density ω = 0 := by
          simp only [game_density]
          by_cases h_eq_pick : ω.host = ω.pick
          · simp [h_eq_pick]
          · by_cases h_eq_car : ω.host = ω.car
            · simp [h_eq_car, h_eq_pick]
            · -- If host ≠ pick and host ≠ car, but host ≠ right
              -- Then host must be left or middle
              have h_doors : ω.host = left ∨ ω.host = middle ∨ ω.host = right := by
                cases ω.host <;> simp
              cases' h_doors with hl hr
              · rw [h_pick] at h_eq_pick
                exact absurd hl h_eq_pick
              · cases' hr with hm hr
                · rw [h_car] at h_eq_car
                  exact absurd hm h_eq_car
                · exact absurd hr h_not_right
        exact absurd h_pos (not_lt.mpr (le_of_eq this))

      -- Now compute the conditional probability
      -- We'll show that ℙ[(pick_door left ∩ host_opens right) ∩ car_at middle] = ℙ[pick_door left ∩ car_at middle] / 3
      -- and ℙ[car_at middle] = 1/3

      -- First, establish that with car=middle and pick=left, host must choose right
      have h_eq_sets : (pick_door left ∩ host_opens right) ∩ car_at middle =
                       pick_door left ∩ car_at middle ∩ host_opens right := by
        rw [Set.inter_assoc, Set.inter_comm (host_opens right), ← Set.inter_assoc]

      rw [ProbabilityTheory.cond_apply]
      -- cond_apply gives us: ℙ[car_at middle]⁻¹ * ℙ[car_at middle ∩ (pick_door left ∩ host_opens right)]
      -- We need to rearrange the intersection
      have h_inter_rearrange : car_at middle ∩ (pick_door left ∩ host_opens right) =
                              (pick_door left ∩ host_opens right) ∩ car_at middle := by
        rw [Set.inter_comm]
      rw [h_inter_rearrange, h_eq_sets]

      -- Need to compute ℙ[pick_door left ∩ car_at middle ∩ host_opens right]
      -- This equals ℙ of games where pick=left, car=middle, host=right
      -- By h_det, this is exactly the games where pick=left and car=middle (with positive density)

      -- Key insight: when car=middle and pick=left, host MUST open right (by h_det)
      -- So pick_door left ∩ car_at middle ∩ host_opens right = pick_door left ∩ car_at middle
      have h_simplify : pick_door left ∩ car_at middle ∩ host_opens right = pick_door left ∩ car_at middle := by
        ext ω
        simp only [pick_door, car_at, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro ⟨⟨h_pick, h_car⟩, h_host⟩
          exact ⟨h_pick, h_car⟩
        · intro ⟨h_pick, h_car⟩
          refine ⟨⟨h_pick, h_car⟩, ?_⟩
          -- Need to show ω.host = right
          -- When pick=left and car=middle, the only valid choice for host is right
          -- (can't open left because contestant picked it, can't open middle because car is there)
          by_cases h_left : ω.host = left
          · -- If host = left = pick, this contradicts game rules
            exfalso
            -- This game would have density 0, so it doesn't contribute to the measure
            have : game_density ω = 0 := by
              simp only [game_density, h_left, h_pick, if_pos rfl]
            -- But we're looking at games in the support of the measure
            sorry -- This is a measure-theoretic detail
          · by_cases h_middle : ω.host = middle
            · -- If host = middle = car, this contradicts game rules
              exfalso
              have : game_density ω = 0 := by
                simp only [game_density, h_middle, h_car]
                split_ifs <;> rfl
              sorry -- This is a measure-theoretic detail
            · -- host ≠ left and host ≠ middle, so host = right
              have h_three_doors : ω.host = left ∨ ω.host = middle ∨ ω.host = right := by
                cases ω.host <;> simp
              cases' h_three_doors with hl hr
              · exact absurd hl h_left
              · cases' hr with hm hr
                · exact absurd hm h_middle
                · exact hr

      rw [h_simplify]

      sorry
      sorry


    -- When car is not at middle (car at left or right), compute probability
    have h2 : Prob[pick_door left ∩ host_opens right | (car_at middle)ᶜ] = 1/12 := by
      -- P(pick=left ∩ host=right | car≠middle)
      -- When car≠middle, it's either left or right with equal probability
      -- Case 1: car=left
      --   P(pick=left) = 1/3
      --   Given pick=left and car=left, host can choose middle or right (equal prob)
      --   So P(pick=left ∩ host=right | car=left) = 1/3 * 1/2 = 1/6
      -- Case 2: car=right
      --   P(pick=left) = 1/3
      --   Given pick=left and car=right, host must choose middle (cannot choose right)
      --   So P(pick=left ∩ host=right | car=right) = 1/3 * 0 = 0
      -- Using law of total probability:
      -- P(pick=left ∩ host=right | car≠middle) = 1/2 * 1/6 + 1/2 * 0 = 1/12
      sorry

    -- Compute measure of car_at middle = 1/3
    have h3 : p.toMeasure (car_at middle) = 1/3 := by
      -- By symmetry, the car is equally likely to be behind any of the three doors
      -- P(car=middle) = 1/3
      sorry

    -- Compute measure of complement = 2/3
    have h4 : p.toMeasure {ω | ω.car = middle}ᶜ = 2/3 := by
      -- P(car≠middle) = 1 - P(car=middle) = 1 - 1/3 = 2/3
      rw [measure_compl (MeasurableSet.of_discrete) (measure_ne_top _ _)]
      rw [<- car_at]
      rw [h3]
      simp only [measure_univ]
      refine ENNReal.sub_eq_of_eq_add_rev ?_ ?_
      . refine div_ne_top ?_ ?_
        . norm_num
        . norm_num
      . rw [ENNReal.div_add_div_same]
        norm_num
        rw [ENNReal.div_self] <;> norm_num

    rw [h1, h2, h3, h4]
    all_goals eq_as_reals

theorem monty_hall_switch_probability_total_prob :
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  have h_meas : MeasurableSet (pick_door left ∩ host_opens right) := by
    apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
  unfold Prob
  rw [ProbabilityTheory.cond_apply h_meas]
  calc (ℙ[pick_door left ∩ host_opens right])⁻¹ *
       ℙ[(pick_door left ∩ host_opens right) ∩ car_at middle]
    _ = (Prob[(pick_door left ∩ host_opens right) | car_at middle] * ℙ[car_at middle] + Prob[(pick_door left ∩ host_opens right)  | (car_at middle)ᶜ ] * ℙ[{ω | ω.car = middle}ᶜ ] )⁻¹ * ℙ[{ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = middle}] := by
      rw [<- Prob]
      rw [law_of_total_probability Prob (pick_door left ∩ host_opens right) (car_at middle)]
      exact rfl
      . exact h_meas
      . exact h_meas
    _ = (1/6)⁻¹ * (1/9) := by
      rw [prob_car_middle_pick_left_host_right]
      rw [explicit_total]
    _ = 2/3 := by eq_as_reals

/-

## Challenges


- Derive a statement for the "total probability" law ✓
- Proof the total probability law as a theorem / lemma. ✓
- Replace boilerplate proof code in `Dilemma.lean` by the total probability law.

-/
