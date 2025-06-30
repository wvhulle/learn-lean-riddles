import RiddleProofs.MontyHall.Statement

open Door


-- Door enumeration lemma - used everywhere Door universes appear
theorem Door.univ_eq : (Finset.univ : Finset Door) = {Door.left, Door.middle, Door.right} := by
  ext d; cases d <;> simp

-- Generic finite sum expansion for any function on Door
theorem Door.sum_eq (f : Door → α) [AddCommMonoid α] :
  ∑ d : Door, f d = f left + f middle + f right := by
  rw [Door.univ_eq, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · rw [add_assoc]
  · simp [Door.left, Door.middle, Door.right]
  · simp [Door.left, Door.middle, Door.right]


-- General likelihood function for any scenario
noncomputable def general_likelihood (player_door host_door car_door : Door) : ℝ :=
  if host_door = player_door then 0  -- Invalid: host never opens player's door
  else if host_door = car_door then 0  -- Host never opens car door
  else if car_door = player_door then 1/2  -- Host has 2 choices
  else 1  -- Host forced to open this door

-- Prior: Each door equally likely to have the car
noncomputable def car_prior : Door → ℝ := fun _ => 1/3

-- Car prior simplification lemmas
@[simp] theorem car_prior_eval (d : Door) : car_prior d = 1/3 := rfl



-- General evidence function
noncomputable def general_evidence (player_door host_door : Door) : ℝ :=
  car_prior left * general_likelihood player_door host_door left +
  car_prior middle * general_likelihood player_door host_door middle +
  car_prior right * general_likelihood player_door host_door right


-- General posterior via Bayes' theorem
noncomputable def general_posterior (player_door host_door car_door : Door) : ℝ :=
  if general_evidence player_door host_door = 0 then 0
  else car_prior car_door * general_likelihood player_door host_door car_door / general_evidence player_door host_door

-- Helper function to determine the switch door
def switch_door (player_door host_door : Door) : Door :=
  if player_door ≠ left ∧ host_door ≠ left then left
  else if player_door ≠ middle ∧ host_door ≠ middle then middle
  else right
