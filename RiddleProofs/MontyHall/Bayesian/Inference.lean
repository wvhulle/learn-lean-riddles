import RiddleProofs.MontyHall.Basic
import RiddleProofs.MontyHall.Bayesian.Model
open Door ProbabilityTheory MeasureTheory ENNRealArith



-- Corresponds mathematically to: P(game) = ∑_{car} P(car) × P(game | car)
noncomputable def monty_joint : PMF Game :=
  car_prior.bind (fun car =>
    (monty_likelihood car).map (fun (pick, host) => ⟨car, pick, host⟩))

-- Measure of singleton for joint distribution
lemma prob_game_joint_measure (g : Game) : monty_joint.toMeasure {g} =
    car_prior g.car * raw_likelihood g.car g.pick g.host := by
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
  -- Decompose the event by car position
  have h_decomp : pick_door left ∩ host_opens right =
    {⟨left, left, right⟩} ∪ {⟨middle, left, right⟩} ∪ {⟨right, left, right⟩} := by
    ext g
    simp only [pick_door, host_opens, Set.mem_inter_iff, Set.mem_setOf_eq,
               Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro ⟨hp, hh⟩
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
    simp only [car_prior, PMF.ofFintype_apply, raw_likelihood]
    norm_num

  -- Rewrite the union and use disjointness
  rw [Set.union_assoc]
  have h_disj1 : Disjoint ({⟨left, left, right⟩} : Set Game)
                         ({⟨middle, left, right⟩} ∪ {⟨right, left, right⟩}) := by
    simp [Set.disjoint_singleton_left]
  have h_disj2 : Disjoint ({⟨middle, left, right⟩} : Set Game) ({⟨right, left, right⟩} : Set Game) := by
    simp
  rw [measure_union h_disj1, measure_union h_disj2]
  rw [h_zero, add_zero]
  -- Calculate each probability
  rw [prob_game_joint_measure, prob_game_joint_measure]
  simp only [car_prior, PMF.ofFintype_apply, raw_likelihood]
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
  simp only [car_prior, PMF.ofFintype_apply, raw_likelihood]
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
  simp only [car_prior, PMF.ofFintype_apply, raw_likelihood]
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
