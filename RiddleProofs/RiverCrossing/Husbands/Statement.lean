import Init.WF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import RiddleProofs.RiverCrossing.Basic

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



-/

def num_couples : Nat := 3

open RiverBank

inductive Person
| husband (i : Fin num_couples)
| wife (i : Fin num_couples)
deriving DecidableEq, Repr


def Person.couple_id : Person → Fin num_couples
| .husband i => i
| .wife i => i

abbrev JealousHusbandsState := RiverCrossingState Person Person num_couples


/-- Get the current bank location of a person in the given state. -/
def Person.bank (p : Person) (s : JealousHusbandsState) : RiverBank :=
match p with
| .husband i => s.owner_bank.get i
| .wife i => s.possession_bank.get i

/-- Helper function to check if a wife is alone with another husband.
    Returns true if wife i is on the same bank as husband j, but husband i is not. -/
def wife_safe (s : JealousHusbandsState) : Bool :=
  decide (∀ (wife_couple_idx : Fin num_couples) (husband_couple_idx : Fin num_couples),
  let wife_bank := s.possession_bank[wife_couple_idx]!
  let other_husband_bank := s.owner_bank[husband_couple_idx]!
  let husband_bank := s.owner_bank[wife_couple_idx]!
  wife_bank = other_husband_bank -> husband_bank = other_husband_bank)



theorem final_safe : wife_safe final_state  := by
  unfold wife_safe
  decide

instance {n: Nat} : OfNat (Fin num_couples) n := mkFinOfNat num_couples (by decide)

end RiverCrossing.Husbands
