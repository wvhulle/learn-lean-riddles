import Init.WF

/-!
# River crossing puzzle:

Three jealous mathematicians and their three secret notebooks must cross a river.
- The boat carries at most two items (people or notebooks).
- No mathematician may be left alone with another’s notebook unless the owner is present.

Can they all get across safely?
-/

def num_mathematicians: Nat := 3

inductive RiverBank
| left
| right
deriving DecidableEq, Repr, Inhabited


open RiverBank

structure State where
  boat : RiverBank
  mathematicians : Vector RiverBank num_mathematicians
  notebooks : Vector  RiverBank num_mathematicians
  deriving Repr, DecidableEq

-- Safety condition: no notebook is ever with another mathematician unless its owner is present
-- (i.e., notebook i cannot be with mathematician j unless mathematician i is also present, for i ≠ j)
def no_notebook_left_behind (s : State) : Prop :=
  ∀ i j : Fin num_mathematicians, (i ≠ j) →
    let mathematician_i_note_bank := s.notebooks[i]
    let mathematician_j_bank := s.mathematicians[j]
    let mathematician_i_bank := s.mathematicians[i]
    mathematician_i_note_bank = mathematician_j_bank → mathematician_i_bank = mathematician_j_bank

/-
## Decidability

Whether a property is decidable depends on how it is defined. If it is built from decidable operations and quantifies only over finite/enumerable types, Lean can often infer it (with infer_instance), but it cannot always do so automatically without being told to try.
 -/
instance : DecidablePred no_notebook_left_behind := by
  unfold no_notebook_left_behind
  infer_instance
-- unfold ...; infer_instance works if and only if the unfolded definition is built from decidable pieces and quantifies only over finite/enumerable types.

-- Initial state: everyone and everything on the left bank
def initial_state : State :=
  { boat := left, mathematicians := Vector.replicate 3 left, notebooks := Vector.replicate 3 left }
-- Goal state: everyone and everything on the right bank

def final_state : State :=
  { boat := right, mathematicians := Vector.replicate 3 right, notebooks := Vector.replicate 3 right }

theorem final_safe: no_notebook_left_behind (final_state):= by
  unfold no_notebook_left_behind
  intro i j ineqj
  unfold final_state
  simp

-- If we drop the constraint temporarily that all transfers have to happen step-wise and just look at the initial and final state, we should be able to prove that the two-state path is safe.
theorem impossible_path_safe :
  ∃ (path : List State),
    path.head? = some  initial_state ∧
    path.getLast? = some final_state ∧
    True :=
  ⟨[initial_state, final_state], rfl, rfl, trivial⟩

section Helpers

/-
## Helpers / abstractions

Let's model the way items or people travel across the river.
 -/

def move_mathematician (n : Fin num_mathematicians) (b : RiverBank) (s : State) : State :=
{ s with mathematicians := s.mathematicians.set n b }

def move_notebook (n : Fin num_mathematicians) (b : RiverBank) (s : State) : State :=
{ s with notebooks := s.notebooks.set n b }

def move_boat (b : RiverBank) (s : State) : State :=
{ s with boat := b }

-- To be able to use numerals like 4 for creating terms of type `Fin 4`, we have to implement a procedure to automatically determine `4 < num_mathematicians`. In this case it is just `decide`.
instance : OfNat (Fin num_mathematicians) n where
  ofNat := ⟨n % num_mathematicians, Nat.mod_lt n (by decide)⟩

end Helpers

section Solution
/-
**Warning!**: Do not read this section before you have made a few attempts.
 -/

def n_transfers : Nat := 11
def n_states := n_transfers + 1

/-
## Obtaining solution

In each step we will transfer a mathematician or a notebook across the river.

This problem is similar to the "jealous husbands" riddle. The solution is identical.
See [Wikipedia](https://en.wikipedia.org/wiki/Missionaries_and_cannibals_problem).
 -/

def transfers : Vector (State → State) n_states :=
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

In the following `n + 1` -> `n` in the recursive call at the end of the recursive function body.
-/

def intermediate_states_structural_rec : (n: Nat) -> n < n_states → State
  | 0, _ => initial_state
  | n + 1, h =>
    let prev := intermediate_states_structural_rec n (Nat.lt_of_succ_lt h)
    (transfers.get ⟨n, Nat.lt_of_succ_lt h⟩) prev

def intermediate_states_structural : Fin n_states → State := (fun n =>  intermediate_states_structural_rec n.val n.isLt)

end StructuralRecursion

/-
## Well-founded recusion

Some types of recursion may lead to infinite loops. Well-founded recursion is a recursive closure with a proof that the recursive closure terminates.

The result of `measure` allows argument j := <n+1,_> to fix to be compared against the recursive argument i:= <n,_> by mapping these arguments to the natural numbers.
-/

noncomputable def intermediate_states : Fin n_states → State :=
  WellFounded.fix (measure (fun (i : Fin n_states) => i.val)).wf
    (fun i rec => match i with
      | ⟨0, _⟩ => initial_state
      | ⟨n + 1, h⟩ =>
        let prev := rec ⟨n, Nat.lt_of_succ_lt h⟩ (Nat.lt_succ_self n)
        (transfers.get ⟨n, Nat.lt_of_succ_lt h⟩) prev
    )
-- `noncomputable` exempts a definition from compilation


-- Verify the start and end point are as expected.
example : intermediate_states ⟨0, by decide⟩ = initial_state := by
  decide

example : intermediate_states ⟨n_states - 1, by decide⟩ = final_state := by
  decide

/-
# Correctness of solution

The main correctness theorem can be verified with `decide` because all involved functions are decidable.

If you prefer a manual approach, you can use a more verbose forward or backward proof.
 -/

theorem all_states_safe : ∀ i : Fin n_states, no_notebook_left_behind (intermediate_states  i) := by
  decide
