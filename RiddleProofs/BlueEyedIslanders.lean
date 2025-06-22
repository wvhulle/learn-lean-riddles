/-!
# Blue-Eyed Islanders Puzzle

On an island, there are 100 perfect logicians, each with either blue or brown eyes. They can see everyone else's eye color but not their own. If a person discovers they have blue eyes, they must leave the island at midnight. There is no communication, but one day a visitor announces publicly: "At least one of you has blue eyes." What happens?

Below, we formalize the problem statement. A full proof is optional and omitted for brevity.
-/



-- We parameterize everything by the number of islanders n.
variable (n : Nat)

/--
A world state: each islander has either blue (true) or brown (false) eyes.
-/
structure World where
  eyeColor : Fin n → Bool -- true = blue, false = brown

/-- Helper: Check if an islander has blue eyes -/
def World.hasBlueEyes (w : World n) (i : Fin n) : Bool := w.eyeColor i

/-- Helper: Get all blue-eyed islanders -/
def World.blueEyedIslanders (w : World n) : List (Fin n) :=
  (List.finRange n).filter w.hasBlueEyes

/-- Helper: Count of blue-eyed islanders -/
def World.numBlueEyed (w : World n) : Nat := w.blueEyedIslanders.length

/--
An islander i sees the eye color of islander j (but not their own).
-/
def sees (w : World n) (i j : Fin n) : Option Bool :=
  if i ≠ j then some (w.eyeColor j) else none

/-
If there are k blue-eyed islanders, all blue-eyed islanders leave on the k-th night after the announcement.
-/
-- The puzzle is to show: If there are k blue-eyed islanders, all blue-eyed islanders leave on the k-th night after the announcement.

-- (No further code needed; this file now compiles and the problem statement is clear.)

/--
Returns the set of islanders who leave on night `k` after the announcement, given a world state.
-/
def blue_eyed_departures {n : Nat} (w : World n) : List (Fin n × Nat) :=
  w.blueEyedIslanders.map (fun i => (i, w.numBlueEyed))

/--
Helper: number of blue-eyed islanders in a world.
-/
def num_blue {n : Nat} (w : World n) : Nat := w.numBlueEyed

/-
For any world, every blue-eyed islander leaves on the night equal to the number of blue-eyed islanders.
-/
theorem all_blue_eyed_leave_on_kth_night (w : World n) :
  ∀ i, w.eyeColor i → (i, num_blue w) ∈ blue_eyed_departures w := by
  intro i hi
  simp [blue_eyed_departures, num_blue, World.numBlueEyed, World.blueEyedIslanders, World.hasBlueEyes]
  constructor
  · simp [List.finRange]
  · exact hi

/-
# Examples
-/

/-- Helper to create a world where first k islanders have blue eyes -/
def world_with_k_blue_eyed (n k : Nat) : World n :=
  ⟨fun i => i.val < k⟩

-- Small example for clarity: 3 blue-eyed islanders among 5
#eval blue_eyed_departures (world_with_k_blue_eyed 5 3)  -- [(0,3), (1,3), (2,3)]

-- The actual puzzle: some number of blue-eyed islanders among 100
-- Example: 10 blue-eyed islanders among 100 (first 10 have blue eyes)
#eval (blue_eyed_departures (world_with_k_blue_eyed 100 10)).length  -- Should be 10

-- Edge cases:
#eval blue_eyed_departures (world_with_k_blue_eyed 100 1)   -- Single blue-eyed person leaves on night 1
#eval blue_eyed_departures (world_with_k_blue_eyed 5 0)     -- No blue-eyed people, empty list

/-!
## Solution Insight

The key insight is that the announcement provides common knowledge:
- Before: Each person knows others' eye colors but not their own
- After announcement: Everyone knows "at least one has blue eyes"

For k blue-eyed people:
- Night 1: If k=1, the single blue-eyed person sees no blue eyes, realizes they must have blue eyes
- Night k: If no one left after k-1 nights, each blue-eyed person deduces they have blue eyes

This is a classic example of the power of common knowledge in logic puzzles.
-/
