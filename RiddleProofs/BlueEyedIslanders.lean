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

**Learning goals for this formalization**

- Understand inductive reasoning and common knowledge in logic
- Learn how to work with finite types and cardinality
- Practice modeling logical reasoning problems
- See how `decidable` instances work in Lean

**Key insight**: The announcement creates "common knowledge" which is different from
everyone just knowing the fact individually. This common knowledge is what enables
the logical deduction that leads to the blue-eyed islanders eventually leaving.

## Epistemic Logic: The Science of Knowledge and Belief

This puzzle is a classic example of **epistemic logic** - the formal study of knowledge,
belief, and reasoning about what others know. Let's break down the key concepts:

### Levels of Knowledge

1. **Individual Knowledge**: "I know that at least one person has blue eyes"
   - Each islander could see this before the announcement
   
2. **Mutual Knowledge**: "I know that you know that at least one person has blue eyes"
   - Before the announcement, this wasn't guaranteed
   
3. **Common Knowledge**: "I know that you know that I know that... (infinitely) at least one person has blue eyes"
   - This is what the public announcement creates!

### Why Common Knowledge Matters

**Before the announcement**: Each blue-eyed person sees 99 blue-eyed others and thinks:
- "Maybe I have brown eyes, and there are exactly 99 blue-eyed people"
- "If so, those 99 can't deduce their eye color (they each see only 98 others)"
- "So no one will leave tonight"

**After the announcement**: The same person now knows:
- "Everyone knows there's at least one blue-eyed person"
- "If there were only 1 blue-eyed person, they'd see 0 others and leave immediately"
- "If there were 2, they'd each see 1 other, realize they must have blue eyes after the first night, and leave on night 2"
- "By induction, if there are N blue-eyed people, they'll all leave on night N"

### The Inductive Reasoning Process

For a blue-eyed islander observing 99 others with blue eyes:

**Day 1**: "If there were only 1 blue-eyed person (me), they'd leave tonight"
**Day 2**: "If there were only 2 blue-eyed people (me + 1 other), we'd both leave tonight"
...
**Day 100**: "If there were only 100 blue-eyed people (me + 99 others), we'd all leave tonight"

When no one leaves on nights 1-99, each blue-eyed person learns there are at least 100.
Since they can see exactly 99 others, they deduce: "I must be the 100th!"
-/

inductive EyeColor where
  | blue : EyeColor
  | brown : EyeColor
  | green : EyeColor  -- included for completeness, but not used in our specific problem
  deriving DecidableEq

instance : Fintype EyeColor where
  elems := {EyeColor.blue, EyeColor.brown, EyeColor.green}
  complete := by intro x; cases x <;> simp

def numIslanders : ℕ := 200

abbrev Islander := Fin numIslanders

-- First 100 islanders (indices 0-99) have blue eyes
-- Last 100 islanders (indices 100-199) have brown eyes
def islanderEyeColors : Islander → EyeColor :=
  fun i => if i.val < 100 then EyeColor.blue else EyeColor.brown

instance : DecidablePred (fun i : Islander => islanderEyeColors i = EyeColor.blue) :=
  fun i => by unfold islanderEyeColors; infer_instance

/-- Models what an islander can deduce about their own eye color based on:
    - The observed eye colors of others
    - The fact that someone would leave if they knew they had blue eyes  
    - Common knowledge accumulated over days
    
    **The deduction logic**: On day N, a blue-eyed islander who observes (N-1) other
    blue-eyed people can reason: "If there were only (N-1) blue-eyed people total,
    they would have all left by now. Since they haven't, there must be at least N.
    Since I see exactly (N-1), I must be the Nth one!"
    
    **Implementation**: An islander can deduce their eye color on day D if and only if:
    1. They actually have blue eyes, AND
    2. D equals the total number of blue-eyed people on the island -/
def can_deduce_own_eye_color (i : Islander) (day : ℕ) : Prop :=
  let blue_eyed_islanders := (Finset.univ.filter (λ j => islanderEyeColors j = EyeColor.blue))
  let num_blue_eyed := blue_eyed_islanders.card
  (islanderEyeColors i = EyeColor.blue) ∧ (day = num_blue_eyed)

def leaves_on_night (i : Islander) (night : ℕ) : Prop :=
  can_deduce_own_eye_color i night

def count_blue_eyed : ℕ :=
  (Finset.univ.filter (λ i : Islander => islanderEyeColors i = EyeColor.blue)).card



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
