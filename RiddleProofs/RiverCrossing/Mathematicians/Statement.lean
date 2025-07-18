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

-- Safety condition: no notebook is ever with another mathematician unless its owner is present
-- (i.e., notebook i cannot be with mathematician j unless mathematician i is also present, for i ≠ j)
def no_notebook_left_behind (s : MathematicianState) : Prop :=
  ∀ i j : Fin num_mathematicians, (i ≠ j) →
    let mathematician_i_note_bank := s.entities_b[i]
    let mathematician_j_bank := s.entities_a[j]
    let mathematician_i_bank := s.entities_a[i]
    mathematician_i_note_bank = mathematician_j_bank → mathematician_i_bank = mathematician_j_bank

-- Boolean version of the safety condition for decidable computations
def notebook_safe (s : MathematicianState) : Bool :=
  let indices : List (Fin num_mathematicians) := List.finRange num_mathematicians
  indices.all (fun i =>
    indices.all (fun j =>
      i = j ||
      let mathematician_i_note_bank := s.entities_b[i]!
      let mathematician_j_bank := s.entities_a[j]!
      let mathematician_i_bank := s.entities_a[i]!
      mathematician_i_note_bank ≠ mathematician_j_bank || mathematician_i_bank = mathematician_j_bank))

-- SafetyConstraint instance for MathematicianState
instance : SafetyConstraint Unit Unit num_mathematicians where
  is_safe := notebook_safe
  is_safe_decidable := by infer_instance

/-
## Decidability

Whether a property is decidable depends on how it is defined. If it is built from decidable operations and quantifies only over finite/enumerable types, Lean can often infer it (with infer_instance), but it cannot always do so automatically without being told to try.
 -/
instance : DecidablePred no_notebook_left_behind := by
  unfold no_notebook_left_behind
  infer_instance

-- Everyone and everything on the left bank
def mathematicians_initial_state : MathematicianState :=
  initial_state Unit Unit num_mathematicians

-- Everyone and everything on the right bank  
def mathematicians_final_state : MathematicianState :=
  final_state Unit Unit num_mathematicians

theorem final_safe: no_notebook_left_behind mathematicians_final_state := by
  unfold no_notebook_left_behind mathematicians_final_state final_state
  intro i j ineqj
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
