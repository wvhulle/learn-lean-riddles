import Mathlib.Data.Fintype.Card
import RiddleProofs.BlueEyedIslanders.Statement

/-!
# Solution

All blue-eyed islanders will leave on the 100th night, and no
brown-eyed islanders ever leave.

The key insight is that the announcement provides common knowledge. Each blue-eyed
person can see 99 other blue-eyed people. On night n, if n-1 blue-eyed people haven't
left, then there must be at least n blue-eyed people total. When n equals the actual
number of blue-eyed people, everyone with blue eyes can deduce their own eye color.
-/

theorem blue_eyed_islanders_leave :
  ∀ i : Islander, islanderEyeColors i = EyeColor.blue → leaves_on_night i 100 := by
  intro i h_blue
  unfold leaves_on_night can_deduce_own_eye_color
  simp [h_blue]
  rfl

theorem brown_eyed_islanders_do_not_leave :
  ¬ ∃ i : Islander, islanderEyeColors i = EyeColor.brown ∧ ∃ n : ℕ, leaves_on_night i n := by
  rintro ⟨i, hi, n, hn⟩
  simp [leaves_on_night, can_deduce_own_eye_color] at hn
  rw [hi] at hn
  cases hn.1
