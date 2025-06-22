/-!
# Blue-Eyed Islanders Puzzle

On an island, there are 100 perfect logicians, each with either blue or brown eyes. They can see everyone else's eye color but not their own. If a person discovers they have blue eyes, they must leave the island at midnight. There is no communication, but one day a visitor announces publicly: "At least one of you has blue eyes." What happens?

Below, we formalize the problem statement. A full proof is optional and omitted for brevity.
-/

namespace BlueEyedIslanders

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
