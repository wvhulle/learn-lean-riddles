import Init.WF
import RiddleProofs.RiverCrossing.Common

/-!
# River crossing puzzle:

Three jealous mathematicians and their three secret notebooks must cross a river.
- The boat carries at most two items (people or notebooks).
- No mathematician may be left alone with another’s notebook unless the owner is present.

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

/-
## Decidability

Whether a property is decidable depends on how it is defined. If it is built from decidable operations and quantifies only over finite/enumerable types, Lean can often infer it (with infer_instance), but it cannot always do so automatically without being told to try.
 -/
instance : DecidablePred no_notebook_left_behind := by
  unfold no_notebook_left_behind
  infer_instance

-- Everyone and everything on the left bank
def initial_state : MathematicianState :=
  { boat := left, entities_a := Vector.replicate 3 left, entities_b := Vector.replicate 3 left }

-- Everyone and everything on the right bank
def final_state : MathematicianState :=
  { boat := right, entities_a := Vector.replicate 3 right, entities_b := Vector.replicate 3 right }

theorem final_safe: no_notebook_left_behind (final_state):= by
  unfold no_notebook_left_behind
  intro i j ineqj
  unfold final_state
  simp

theorem fly_safe :
  ∃ (path : List MathematicianState),
    path.head? = some  initial_state ∧
    path.getLast? = some final_state ∧
    True :=
  ⟨[initial_state, final_state], rfl, rfl, trivial⟩

section Helpers



def move_mathematician (n : Fin num_mathematicians) (b : RiverBank) (s : MathematicianState) : MathematicianState :=
{ s with entities_a := s.entities_a.set n b }

def move_notebook (n : Fin num_mathematicians) (b : RiverBank) (s : MathematicianState) : MathematicianState :=
{ s with entities_b := s.entities_b.set n b }

def move_boat (b : RiverBank) (s : MathematicianState) : MathematicianState :=
{ s with boat := b }

-- To be able to use numerals like 4 for creating terms of type `Fin 4`, we have to implement a procedure to automatically determine `4 < num_mathematicians`. In this case it is just `decide`.
instance {n: Nat} : OfNat (Fin num_mathematicians) n where
  ofNat := ⟨n % num_mathematicians, Nat.mod_lt n (by decide)⟩

end Helpers

section Solution

private def n_transfers : Nat := 11
private def n_states := n_transfers + 1

/-
## Obtaining solution

In each step we will transfer a mathematician or a notebook across the river.

This problem is similar to the "jealous husbands" riddle. The solution is identical.
See [Wikipedia](https://en.wikipedia.org/wiki/Missionaries_and_cannibals_problem).
 -/

def transfers : Vector (MathematicianState → MathematicianState) n_states :=
  Vector.ofFn (fun ⟨ k, _ ⟩  => match k with
    | 0 => move_boat right ∘ move_notebook 0  right ∘ move_mathematician 0 right
    | 1 => move_boat left ∘ move_notebook 0 left ∘ move_mathematician 0 left
    | 2 => move_boat right ∘ move_notebook 1 right ∘ move_mathematician 1 right
    | 3 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right
    | 4 => move_boat right ∘ move_notebook 2 right ∘ move_mathematician 2 right
    | 5 => move_boat left ∘ move_notebook 0 left ∘ move_mathematician 0 left
    | 6 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right
    | 7 => move_boat left ∘ move_notebook 1 left ∘ move_mathematician 1 left
    | 8 => move_boat right ∘ move_notebook 1 right ∘ move_mathematician 1 right
    | 9 => move_boat left ∘ move_notebook 0 left ∘ move_mathematician 0 left
    | 10 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right
    | _ => id)

end Solution

namespace StructuralRecursion

/-
## Structural recursion

A kind of recursion that is easy to check for termination. Termination can be checked by Lean automatically because the argument visibly and syntactically "erodes" (or shrinks) in the recursive call.

In the following, the size of the argument changes `n + 1` -> `n` in the recursive call at the end of the recursive function body.
-/

def intermediate_states_structural_rec : (n: Nat) -> n < n_states → MathematicianState
  | 0, _ => initial_state
  | n + 1, h =>
    let prev := intermediate_states_structural_rec n (Nat.lt_of_succ_lt h)
    (transfers.get ⟨n, Nat.lt_of_succ_lt h⟩) prev

def intermediate_states_structural : Fin n_states → MathematicianState := (fun n =>  intermediate_states_structural_rec n.val n.isLt)

end StructuralRecursion

/-
## Well-founded recusion

Some types of recursion may lead to infinite loops. Well-founded recursion is a recursive closure with a proof that the recursive closure terminates.

The result of `measure` allows argument j := <n+1,_> to fix to be compared against the recursive argument i:= <n,_> by mapping these arguments to the natural numbers.
-/

noncomputable def intermediate_states : Fin n_states → MathematicianState :=
  WellFounded.fix (measure (fun (i : Fin n_states) => i.val)).wf
    (fun i rec => match i with
      | ⟨0, _⟩ => initial_state
      | ⟨n + 1, h⟩ =>
        let prev := rec ⟨n, Nat.lt_of_succ_lt h⟩ (Nat.lt_succ_self n)
        (transfers.get ⟨n, Nat.lt_of_succ_lt h⟩) prev
    )
-- `noncomputable` exempts a definition from certain types of checks


-- Verify the start and end point are as expected.
example : intermediate_states ⟨0, by decide⟩ = initial_state := by
  decide

example : intermediate_states ⟨n_states - 1, by decide⟩ = final_state := by
  decide

-- We implemented decidability for `no_notebook_left_behind`, so we can use `decide`
theorem all_states_safe : ∀ i : Fin n_states, no_notebook_left_behind (intermediate_states  i) := by
  decide

end RiverCrossing.Mathematicians
