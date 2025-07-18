import Init.WF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import RiddleProofs.RiverCrossing.Common

namespace RiverCrossing.Husbands

open RiverBank

/-!
# Problem statement: The jealous husbands puzzle

```
Left Bank                    River                    Right Bank
-----------------------------------------------------------------
H₁ W₁ H₂ W₂ H₃ W₃    [=======🚤======]               (empty)
```

Three husbands (H₁, H₂, H₃) and their wives (W₁, W₂, W₃) must cross a river using a small boat.

## The rules (constraints)

1. **Boat capacity**: The boat can carry at most 2 people at a time
2. **Boat operation**: The boat cannot cross the river by itself (someone must operate it)
3. **Jealousy constraint**: A wife cannot be alone with another husband unless her own husband is present

The **jealousy constraint** is the key challenge. For example:
- ❌ W₁ and H₂ cannot be together without H₁ present
- ✅ W₁, H₁, and H₂ can be together (H₁ protects his wife)
- ✅ H₁ and H₂ can be alone together (no wives involved)


## Challenges

- Can you generalize to N couples?
- What about more than 2 people in a boat?
- Can you optimize my BFS in `Search.lean`?
- Like `JealousMathematician.lean`, can you write a version for "cannibals and missionaries"?

-/

/-- Number of couples in the puzzle -/
def num_couples : Nat := 3

open RiverBank

/-- A person is either a husband or wife, identified by their couple index.
    For example: `husband ⟨0, _⟩` represents the first husband (H₀). -/
inductive Person
| husband (i : Fin num_couples)
| wife (i : Fin num_couples)
deriving DecidableEq, Repr

instance : ToString Person where
  toString p := match p with
  | .husband i => s!"H{i.val}"
  | .wife i => s!"W{i.val}"

notation "H" n => Person.husband ⟨n, by decide⟩
notation "W" n => Person.wife ⟨n, by decide⟩

@[app_unexpander Person.husband]
def unexpandHusband : Lean.PrettyPrinter.Unexpander
  | `($_ ⟨$n, $_⟩) => `(H $n)
  | _ => throw ()

@[app_unexpander Person.wife]
def unexpandWife : Lean.PrettyPrinter.Unexpander
  | `($_ ⟨$n, $_⟩) => `(W $n)
  | _ => throw ()

/-- Extract the couple identifier from a person.
    Both husband and wife of couple i have couple_id = i. -/
def Person.couple_id : Person → Fin num_couples
| .husband i => i
| .wife i => i

/-- The complete state of the puzzle: boat location + position of all people.

    Example state representation:
    - `boat = left`: The boat is on the left bank
    - `husbands = [left, right, left]`: H₀ and H₂ on left, H₁ on right
    - `wives = [left, left, right]`: W₀ and W₁ on left, W₂ on right -/
abbrev JealousHusbandsState := RiverCrossingState Person Person num_couples

instance : BEq JealousHusbandsState where
  beq s1 s2 := s1.boat == s2.boat &&
               s1.entities_a.toList == s2.entities_a.toList &&
               s1.entities_b.toList == s2.entities_b.toList

/-- Get the current bank location of a person in the given state. -/
def Person.bank (p : Person) (s : JealousHusbandsState) : RiverBank :=
match p with
| .husband i => s.entities_a.get i
| .wife i => s.entities_b.get i

/-- Helper function to check if a wife is alone with another husband.
    Returns true if wife i is on the same bank as husband j, but husband i is not. -/
def wife_alone_with_other_husband (s : JealousHusbandsState) (wife_i : Fin num_couples) (husband_j : Fin num_couples) : Bool :=
  let wife_bank := s.entities_b[wife_i]!
  let other_husband_bank := s.entities_a[husband_j]!
  let own_husband_bank := s.entities_a[wife_i]!
  wife_bank = other_husband_bank && own_husband_bank ≠ other_husband_bank

/-- Checks if a state satisfies the jealousy constraint.-/
def bank_safe (s : JealousHusbandsState) : Bool :=
  let pairs : List (Fin num_couples) := List.finRange num_couples
  pairs.all (fun wife_i =>
    pairs.all (fun husband_j =>
      wife_i = husband_j || !wife_alone_with_other_husband s wife_i husband_j))

def state_safe_prop (s : JealousHusbandsState) : Prop := bank_safe s = true

instance : DecidablePred state_safe_prop := by
  unfold state_safe_prop
  infer_instance

def jealous_husbands_initial_state : JealousHusbandsState :=
  initial_state Person Person num_couples

def jealous_husbands_final_state : JealousHusbandsState :=
  final_state Person Person num_couples

theorem final_safe : bank_safe jealous_husbands_final_state = true := by
  unfold bank_safe jealous_husbands_final_state
  decide

instance (n : Nat) : OfNat (Fin num_couples) n where
  ofNat := ⟨n % num_couples, Nat.mod_lt n (by decide)⟩

end RiverCrossing.Husbands
