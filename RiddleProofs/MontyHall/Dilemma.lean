import RiddleProofs.MontyHall.Measure
import RiddleProofs.MontyHall.Enumeration
import RiddleProofs.MontyHall.Statement
import ENNRealArith
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
  prob_density {car := car, pick := pick, host := host} = (1 : ENNReal) / 18 := by
  unfold prob_density real_density
  rw [total_weight_value]
  unfold game_weight
  simp [h_eq, h_valid.1]
  ennreal_arith

lemma prob_density_car_ne_pick (car pick host : Door) (h_ne : car ≠ pick) (h_valid : host ≠ pick ∧ host ≠ car) :
  prob_density {car := car, pick := pick, host := host} = (2 : ENNReal) / 18 := by
  unfold prob_density real_density
  rw [total_weight_value]
  unfold game_weight
  simp [h_ne, h_valid.1, h_valid.2]
  ennreal_arith

lemma prob_density_left_left_right :
  prob_density {car := left, pick := left, host := right} = 1/18 := by
  simp [prob_density_car_eq_pick]

lemma prob_density_middle_left_right :
  prob_density {car := middle, pick := left, host := right} = 2/18 := by
  simp [prob_density_car_ne_pick]

lemma prob_density_right_left_right :
  prob_density {car := right, pick := left, host := right} = 0 := by
  simp [prob_density, real_density, game_weight]

lemma prob_pick_left_host_right :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right}) = 1/6 := by
  have h_inter_eq : ({ω : Game | ω.pick = left} ∩ {ω : Game | ω.host = right}) =
                    {ω : Game | ω.pick = left ∧ ω.host = right} := by
    ext ω; simp [Set.mem_inter_iff]
  rw [h_inter_eq]
  have h_filter_eq : {ω : Game | ω.pick = left ∧ ω.host = right} =
    ↑(game_enumeration.filter (fun ω => ω.pick = left ∧ ω.host = right)) := by
      rw [← equivalence_game_repr]; ext ω; simp
  rw [h_filter_eq, PMF.toMeasure_apply_finset]
  have h_filter_explicit :
    game_enumeration.filter (fun ω => ω.pick = left ∧ ω.host = right) =
    {({car := left, pick := left, host := right} : Game),
     ({car := middle, pick := left, host := right} : Game),
     ({car := right, pick := left, host := right} : Game)} := by
    simp [game_enumeration]; decide
  rw [h_filter_explicit]
  unfold p
  simp only [PMF.ofFinset_apply]
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · rw [prob_density_left_left_right, prob_density_middle_left_right, prob_density_right_left_right]
    ennreal_arith
  · ennreal_arith
  · ennreal_arith

lemma prob_car_at_given_pick_host (car : Door) :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = car}) =
  prob_density {car := car, pick := left, host := right} := by
  have h_inter_eq : {ω : Game | ω.pick = left} ∩ {ω : Game | ω.host = right} ∩ {ω : Game | ω.car = car} =
                    {ω : Game | ω.pick = left ∧ ω.host = right ∧ ω.car = car} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · intro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  have h_singleton := unique_game_set car left right
  rw [h_inter_eq, h_singleton]
  rw [PMF.toMeasure_apply_singleton]; rfl
  exact MeasurableSet.singleton _

lemma prob_car_left_pick_left_host_right :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = left}) = 1/18 := by
  rw [prob_car_at_given_pick_host, prob_density_left_left_right]

lemma prob_car_middle_pick_left_host_right :
  p.toMeasure ({ω | ω.pick = left} ∩ {ω | ω.host = right} ∩ {ω | ω.car = middle}) = 2/18 := by
  rw [prob_car_at_given_pick_host, prob_density_middle_left_right]

theorem monty_hall_stay_probability:
  Prob[car_at left | pick_door left ∩ host_opens right] = 1/3 := by
  unfold Prob car_at pick_door host_opens
  rw [ProbabilityTheory.cond_apply]
  · rw [prob_car_left_pick_left_host_right, prob_pick_left_host_right]
    ennreal_arith
  · apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete

theorem monty_hall_switch_probability:
  Prob[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
  unfold Prob car_at pick_door host_opens
  rw [ProbabilityTheory.cond_apply]
  · rw [prob_car_middle_pick_left_host_right, prob_pick_left_host_right]
    ennreal_arith
  · apply MeasurableSet.inter <;> exact MeasurableSet.of_discrete
