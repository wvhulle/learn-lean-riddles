import Init.WF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

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

## Mathematical modeling

We represent this as a **state space search problem**:
- **RiverCrossingState**: Position of each person (left/right bank) + boat location
- **Actions**: Valid moves respecting all constraints
- **Goal**: All people and boat on the right bank
- **Safety predicate**: No jealousy violations at any intermediate state

This encoding demonstrates how **social constraints** become **logical predicates**
that can be automatically verified by the computer.
-/

/-- Number of couples in the puzzle. Fixed at 3 for the classic version. -/
def num_couples: Nat := 3

/-- The two sides of the river. The boat can be on either side. -/
inductive RiverBank
| left
| right
deriving DecidableEq, Repr, Inhabited, BEq

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
structure RiverCrossingState where
  boat : RiverBank
  husbands : Vector RiverBank num_couples
  wives : Vector RiverBank num_couples
deriving DecidableEq

instance : BEq RiverCrossingState where
  beq s1 s2 := s1.boat == s2.boat &&
               s1.husbands.toList == s2.husbands.toList &&
               s1.wives.toList == s2.wives.toList

/-- Get the current bank location of a person in the given state. -/
def Person.bank (p : Person) (s : RiverCrossingState) : RiverBank :=
match p with
| .husband i => s.husbands.get i
| .wife i => s.wives.get i

/-- Checks if a state satisfies the jealousy constraint.

    **The jealousy rule**: A wife cannot be on the same bank with another husband
    unless her own husband is also present on that bank.

    **Logic breakdown**:
    - For each wife i and each different husband j (where i ≠ j)
    - For each bank (left or right)
    - Check: NOT (wife_i is on bank AND husband_j is on bank AND husband_i is NOT on bank)

    **Example violations**:
    - W₀ and H₁ alone on left bank (H₀ is on right bank) → unsafe
    - W₀, H₀, and H₁ all on left bank → safe (H₀ protects W₀)
    - H₀ and H₁ alone on left bank → safe (no wives involved) -/
def bank_safe (s : RiverCrossingState) : Bool :=
  let couples := #[0, 1, 2]
  let banks := #[RiverBank.left, RiverBank.right]
  couples.all fun i =>
    couples.all fun j =>
      if i = j then true
      else
        banks.all fun bank =>
          !(s.wives[i]! = bank && s.husbands[j]! = bank && s.husbands[i]! ≠ bank)

def state_safe (s : RiverCrossingState) : Bool := bank_safe s

def state_safe_prop (s : RiverCrossingState) : Prop := state_safe s = true

instance : DecidablePred state_safe_prop := by
  unfold state_safe_prop
  infer_instance

def initial_state : RiverCrossingState :=
  { boat := left, husbands := Vector.replicate 3 left, wives := Vector.replicate 3 left }

def final_state : RiverCrossingState :=
  { boat := right, husbands := Vector.replicate 3 right, wives := Vector.replicate 3 right }

theorem final_safe: state_safe final_state = true := by
  unfold state_safe bank_safe final_state
  native_decide

instance : OfNat (Fin num_couples) n where
  ofNat := ⟨n % num_couples, Nat.mod_lt n (by decide)⟩

def n_transfers : Nat := 11
def n_states := n_transfers + 1
