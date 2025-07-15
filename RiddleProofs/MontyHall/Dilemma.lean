import RiddleProofs.MontyHall.Measure
import RiddleProofs.MontyHall.Enumeration
import RiddleProofs.MontyHall.Statement
import ENNRealArith
import Mathlib.Probability.Notation

/-!
# Monty Hall Problem: The main result

This file proves the famous Monty Hall result using rigorous probability theory.

**The main theorems**:
- `monty_hall_stay_probability`: If you stay with your original choice,
  you win with probability 1/3
- `monty_hall_switch_probability`: If you switch to the other door,
  you win with probability 2/3

**Mathematical approach**:
We use conditional probability: P(car at door | contestant picked door A, host opened door B)
This requires careful measure theory to ensure all the calculations are rigorous.

**Key insight**: The asymmetry comes from the host's knowledge and constraints.
The host can't open the door with the car, so their choice gives information
about where the car is likely to be.

**Learning goals**:
- Understand conditional probability in measure theory
- Learn about measurable sets and probability measures
- See how to prove probabilistic statements rigorously
- Practice with ENNReal arithmetic
-/

open ProbabilityTheory ENNReal Door ENNRealArith


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

-- **THE MAIN RESULT**: Probability of winning if you stay with your original choice
-- P(car at left | picked left, host opened right) = 1/3
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

-- **THE MAIN RESULT**: Probability of winning if you switch to the other door
-- P(car at middle | picked left, host opened right) = 2/3
-- This proves that switching is the better strategy!
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
