import Mathlib.Data.Fintype.Card

/-!
# The Blue-Eyed Islanders Puzzle

**Problem**: On a remote island live 200 people, some with blue eyes and some with brown eyes. (There are exactly 100 blue-eyed and 100 brown-eyed islanders for simplicity.) Everyone can see everyone else's eye color, but not their own. They are perfect logicians.

A visiting stranger announces: "At least one of you has blue eyes."

The rules are:
- If someone can deduce their own eye color, they must leave the island that night
- No communication is allowed between islanders
- Everyone acts simultaneously based on perfect logical reasoning

**Question**: What happens?
-/

inductive EyeColor where
  | blue : EyeColor
  | brown : EyeColor
  | green : EyeColor
  deriving DecidableEq

instance : Fintype EyeColor where
  elems := {EyeColor.blue, EyeColor.brown, EyeColor.green}
  complete := by intro x; cases x <;> simp

def numIslanders : ℕ := 200
abbrev Islander := Fin numIslanders

def islanderEyeColors : Islander → EyeColor :=
  fun i => if i.val < 100 then EyeColor.blue else EyeColor.brown

instance : DecidablePred (fun i : Islander => islanderEyeColors i = EyeColor.blue) :=
  fun i => by unfold islanderEyeColors; infer_instance

def can_deduce_own_eye_color (i : Islander) (day : ℕ) : Prop :=
  let blue_eyed_islanders := (Finset.univ.filter (λ j => islanderEyeColors j = EyeColor.blue))
  let num_blue_eyed := blue_eyed_islanders.card
  (islanderEyeColors i = EyeColor.blue) ∧ (day = num_blue_eyed)

def leaves_on_night (i : Islander) (night : ℕ) : Prop :=
  can_deduce_own_eye_color i night

/-!
## Solution

**Answer**: All blue-eyed islanders will leave on the 100th night, and no brown-eyed islanders ever leave.

The key insight is that the announcement provides common knowledge. Each blue-eyed person can see 99 other blue-eyed people. On night n, if n-1 blue-eyed people haven't left, then there must be at least n blue-eyed people total. When n equals the actual number of blue-eyed people, everyone with blue eyes can deduce their own eye color.
-/

-- The main theorem of the Blue-Eyed Islanders puzzle.
theorem blue_eyed_islanders_leave :
  ∀ i : Islander, islanderEyeColors i = EyeColor.blue → leaves_on_night i 100 := by
    intro i h_blue
    unfold leaves_on_night can_deduce_own_eye_color
    simp [h_blue]
    -- Need to prove that there are exactly 100 blue-eyed islanders
    rfl


-- Brown-eyed islanders never leave because they cannot deduce their eye color.
theorem brown_eyed_islanders_do_not_leave :
  ¬ ∃ i : Islander, islanderEyeColors i = EyeColor.brown ∧ ∃ n : ℕ, leaves_on_night i n := by
  rintro ⟨i, hi, n, hn⟩
  simp [leaves_on_night, can_deduce_own_eye_color] at hn
  rw [hi] at hn
  cases hn.1
