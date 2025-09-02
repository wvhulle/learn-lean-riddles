import Init.WF
import RiddleProofs.RiverCrossing.Mathematicians.Statement

/-!
# Solution to the Jealous Mathematicians River Crossing Puzzle

This module provides the actual solution to the jealous mathematicians puzzle,
including the step-by-step transfers and verification that all intermediate
states are safe.
-/

namespace RiverCrossing.Mathematicians

open RiverBank

section Solution

/-- Number of transfers needed for the standard 3-couple solution -/
def n_transfers : Nat := 11

/-- Number of states in the solution path -/
def n_states : Nat := n_transfers + 1

-- OfNat instance for Fin n_states
instance {n: Nat} : OfNat (Fin n_states) n := mkFinOfNat n_states (by decide)

/-
## Obtaining solution

In each step we will transfer a mathematician and a notebook across the river.

 -/

open RiverCrossing (move_boat move_entity_a move_entity_b)

def transfers : Vector (MathematicianState → MathematicianState) n_states :=
  Vector.ofFn (fun ⟨ k, _ ⟩  => match k with
    | 0 => move_boat right ∘ move_entity_b 0 right ∘ move_entity_a 0 right
    | 1 => move_boat left ∘ move_entity_b 0 left ∘ move_entity_a 0 left
    | 2 => move_boat right ∘ move_entity_b 1 right ∘ move_entity_a 1 right
    | 3 => move_boat right ∘ move_entity_b 0 right ∘ move_entity_a 0 right
    | 4 => move_boat right ∘ move_entity_b 2 right ∘ move_entity_a 2 right
    | 5 => move_boat left ∘ move_entity_b 0 left ∘ move_entity_a 0 left
    | 6 => move_boat right ∘ move_entity_b 0 right ∘ move_entity_a 0 right
    | 7 => move_boat left ∘ move_entity_b 1 left ∘ move_entity_a 1 left
    | 8 => move_boat right ∘ move_entity_b 1 right ∘ move_entity_a 1 right
    | 9 => move_boat left ∘ move_entity_b 0 left ∘ move_entity_a 0 left
    | 10 => move_boat right ∘ move_entity_b 0 right ∘ move_entity_a 0 right
    | _ => id)

end Solution

namespace StructuralRecursion

/-
## Structural recursion

A kind of recursion that is easy to check for termination. Termination can be checked by Lean automatically because the argument visibly and syntactically "erodes" (or shrinks) in the recursive call.

In the following, the size of the argument changes `n + 1` -> `n` in the recursive call at the end of the recursive function body.
-/

def intermediate_states_structural_rec : (n: Nat) -> n < n_states → MathematicianState
  | 0, _ => mathematicians_initial_state
  | n + 1, h =>
    let prev := intermediate_states_structural_rec n (Nat.lt_of_succ_lt h)
    (transfers.get ⟨n, Nat.lt_of_succ_lt h⟩) prev

def intermediate_states_structural : Fin n_states → MathematicianState := (fun n =>  intermediate_states_structural_rec n.val n.isLt)

end StructuralRecursion

/-
## Well-founded recursion

Some types of recursion may lead to infinite loops. Well-founded recursion is a recursive closure with a proof that the recursive closure terminates.

The result of `measure` allows argument j := <n+1,_> to fix to be compared against the recursive argument i:= <n,_> by mapping these arguments to the natural numbers.
-/

noncomputable def intermediate_states : Fin n_states → MathematicianState :=
  WellFounded.fix (measure (fun (i : Fin n_states) => i.val)).wf
    (fun i rec => match i with
      | ⟨0, _⟩ => mathematicians_initial_state
      | ⟨n + 1, h⟩ =>
        let prev := rec ⟨n, Nat.lt_of_succ_lt h⟩ (Nat.lt_succ_self n)
        (transfers.get ⟨n, Nat.lt_of_succ_lt h⟩) prev
    )
-- `noncomputable` exempts a definition from certain types of checks


-- Verify the start and end point are as expected.
example : intermediate_states 0 = mathematicians_initial_state := by
  decide

example : intermediate_states ⟨n_states - 1, by decide⟩ = mathematicians_final_state := by
  decide

theorem all_states_safe : ∀ i : Fin n_states, notebook_safe (intermediate_states i) = true := by
  decide

end RiverCrossing.Mathematicians
