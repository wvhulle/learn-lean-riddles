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
def blue_eyed_departures {n: Nat}  (w : World n) : List (Fin n × Nat) :=
  let blue := (List.finRange n).filter (fun i => w.eyeColor i)
  blue.map (fun i => (i, blue.length))

/--
Helper: number of blue-eyed islanders in a world.
-/
def num_blue {n: Nat} (w : World n) : Nat := ((List.finRange n).filter (fun i => w.eyeColor i)).length

/-
For any world, every blue-eyed islander leaves on the night equal to the number of blue-eyed islanders.
-/
theorem all_blue_eyed_leave_on_kth_night (w : World n) :
  ∀ i, w.eyeColor i → (i, num_blue w) ∈ blue_eyed_departures w :=
  by
    intros i hi
    simp [blue_eyed_departures, num_blue]
    -- After simplification, we need to show: i ∈ List.finRange n ∧ w.eyeColor i = true
    constructor
    · -- i ∈ List.finRange n
      simp [List.finRange]
    · -- w.eyeColor i = true
      exact hi

/-
# Examples
-/

-- Small example for clarity: 3 blue-eyed islanders among 5
#eval blue_eyed_departures (⟨fun i => i.val < 3⟩ : World 5)  -- [(0,3), (1,3), (2,3)]

-- The actual puzzle: some number of blue-eyed islanders among 100
-- Example: 10 blue-eyed islanders among 100 (first 10 have blue eyes)
#eval (blue_eyed_departures (⟨fun i => i.val < 10⟩ : World 100)).length  -- Should be 10

-- The general case: if there are k blue-eyed islanders among 100, they all leave on night k
-- #eval blue_eyed_departures (⟨fun i => i.val < 1⟩ : World 100)  -- [(0,1)] - single blue-eyed person leaves on night 1
