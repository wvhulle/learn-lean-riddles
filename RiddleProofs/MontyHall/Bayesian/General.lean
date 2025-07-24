import RiddleProofs.MontyHall.Bayesian.Inference
import RiddleProofs.MontyHall.Basic
import RiddleProofs.MontyHall.Bayesian.Model
open Door ProbabilityTheory MeasureTheory ENNRealArith



lemma prob_stay_wins (pick host: Door) (diff: pick ≠ host):
  (monty_joint.toMeasure)[car_at pick | pick_door pick ∩ host_opens host] = 1/3 := by

    sorry


lemma exists_third_door (pick host: Door) (h: pick ≠ host): ∃ door, door ≠ pick ∧ door ≠ host := by
  -- We use the pigeonhole principle: with 3 doors and 2 taken, there must be a third
  have : ∃ door : Door, door ∉ ({pick, host} : Finset Door) := by
    by_contra h_contra
    push_neg at h_contra
    -- If every door is in {pick, host}, then Door ⊆ {pick, host}
    have : Finset.univ ⊆ ({pick, host} : Finset Door) := by
      intro door _
      exact h_contra door
    -- But {pick, host} has at most 2 elements
    have card_le : Finset.card ({pick, host} : Finset Door) ≤ 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp [Finset.card_singleton]
      · simp only [Finset.mem_singleton]
        exact h
    -- And Door has exactly 3 elements
    have card_eq : Finset.card (Finset.univ : Finset Door) = 3 := by
      simp [door_card]
    -- This gives us 3 ≤ 2, which is a contradiction
    have : 3 ≤ 2 := by
      calc 3 = Finset.card (Finset.univ : Finset Door) := card_eq.symm
           _ ≤ Finset.card ({pick, host} : Finset Door) := Finset.card_mono this
           _ ≤ 2 := card_le
    norm_num at this
  obtain ⟨door, hdoor⟩ := this
  use door
  simp at hdoor
  exact hdoor


lemma prob_switch_wins :
  (monty_joint.toMeasure)[car_at middle | pick_door left ∩ host_opens right] = 2/3 := by
    sorry
