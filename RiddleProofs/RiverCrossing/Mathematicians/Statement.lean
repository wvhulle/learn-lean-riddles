import RiddleProofs.RiverCrossing.Basic

/-!
# River crossing puzzle:

Three jealous mathematicians and their three secret notebooks must cross a river.
- The boat carries at most two items (people or notebooks).
- No mathematician may be left alone with another's notebook unless the owner is present.

## Problem

Can they all get across safely?
-/

def num_mathematicians: Nat := 3

namespace RiverCrossing.Mathematicians

open RiverBank

abbrev MathematicianState := RiverCrossingState Unit Unit num_mathematicians


def notebook_safe (s : MathematicianState) : Bool :=
  decide (∀ (owner : Fin num_mathematicians),
    let notebook_bank := s.entities_type_b[owner]!
    let owner_bank := s.entities_type_a[owner]!
    -- If notebook is on boat, then owner must be on boat too
    (notebook_bank = s.boat_bank → owner_bank = s.boat_bank) ∧
    -- Owner must be with their notebook, OR no other mathematician can access it
    ((notebook_bank = owner_bank) ∨ 
     (∀ (other : Fin num_mathematicians), other ≠ owner → s.entities_type_a[other]! ≠ notebook_bank)))

-- SafetyConstraint instance for MathematicianState
instance : SafetyConstraint Unit Unit num_mathematicians where
  is_safe := notebook_safe
  is_safe_decidable := by infer_instance

/-
## Decidability

Whether a property is decidable depends on how it is defined. If it is built from decidable operations and quantifies only over finite/enumerable types, Lean can often infer it (with infer_instance), but it cannot always do so automatically without being told to try.
 -/

-- Everyone and everything on the left bank
def mathematicians_initial_state : MathematicianState :=
  initial_state Unit Unit num_mathematicians

-- Everyone and everything on the right bank
def mathematicians_final_state : MathematicianState :=
  final_state Unit Unit num_mathematicians

theorem final_safe: notebook_safe mathematicians_final_state = true := by
  unfold notebook_safe mathematicians_final_state final_state
  simp

theorem fly_safe :
  ∃ (path : List MathematicianState),
    path.head? = some  mathematicians_initial_state ∧
    path.getLast? = some mathematicians_final_state ∧
    True :=
  ⟨[mathematicians_initial_state, mathematicians_final_state], rfl, rfl, trivial⟩

-- To be able to use numerals like 4 for creating terms of type `Fin 4`, we have to implement a procedure to automatically determine `4 < num_mathematicians`. In this case it is just `decide`.
instance {n: Nat} : OfNat (Fin num_mathematicians) n := mkFinOfNat num_mathematicians (by decide)


end RiverCrossing.Mathematicians
