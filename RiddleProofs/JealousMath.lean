import Init.WF

/-!
# River crossing puzzle:

Three jealous mathematicians (A, B, C) and their three secret notebooks (a, b, c) must cross a river.
The boat carries at most two items (people or notebooks).
No mathematician may be left alone with another’s notebook unless the owner is present.

Can they all get across safely?
-/


inductive RiverBank
| left | right
  deriving DecidableEq, Repr, Inhabited

open RiverBank

structure State where
  boat : RiverBank  -- Boat position
  mathematicians : Vector RiverBank 3
  notebooks : Vector  RiverBank 3
  deriving Repr, DecidableEq

-- Safety condition: no notebook is ever with another mathematician unless its owner is present
-- (i.e., notebook i cannot be with mathematician j unless mathematician i is also present, for i ≠ j)
def no_notebook_left_behind (s : State) : Prop :=
  ∀ i j : Fin 3, (i ≠ j) →
    let Ni := s.notebooks[i]
    let Mj := s.mathematicians[j]
    let Mi := s.mathematicians[i]
    Ni = Mj → Mi = Mj

-- Whether a property is decidable depends on how it is defined. If it is built from decidable operations and quantifies only over finite/enumerable types, Lean can often infer it (with infer_instance), but it cannot always do so automatically without being told to try.

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
  rw [no_notebook_left_behind]
  intro i j ineqj
  rw [final_state]
  simp

-- There exists a sequence of states from initial to goal (trivial version)
theorem impossible_path_safe :
  ∃ (path : List State),
    path.head? = some  initial_state ∧
    path.getLast? = some final_state ∧
    True :=
  ⟨[initial_state, final_state], rfl, rfl, trivial⟩

section Solution

 def move_mathematician (n : Fin 3) (b : RiverBank) (s : State) : State :=
  { s with mathematicians := s.mathematicians.set n b }

 def move_notebook (n : Fin 3) (b : RiverBank) (s : State) : State :=
  { s with notebooks := s.notebooks.set n b }

 def move_boat (b : RiverBank) (s : State) : State :=
  { s with boat := b }

-- A solution as a vector of crossing functions (State → State)
def intermediate_steps : Vector (State → State) 11 :=
  Vector.ofFn (fun
    | 0 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right
    | 1 => move_boat left ∘ move_notebook 0 left ∘ move_mathematician 0 left
    | 2 => move_boat right ∘ move_notebook 1 right ∘ move_mathematician 1 right
    | 3 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right
    | 4 => move_boat right ∘ move_notebook 2 right ∘ move_mathematician 2 right
    | 5 => move_boat left ∘ move_notebook 0 left ∘ move_mathematician 0 left
    | 6 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right
    | 7 => move_boat left ∘ move_notebook 1 left ∘ move_mathematician 1 left
    | 8 => move_boat right ∘ move_notebook 1 right ∘ move_mathematician 1 right
    | 9 => move_boat left ∘ move_notebook 0 left ∘ move_mathematician 0 left
    | 10 => move_boat right ∘ move_notebook 0 right ∘ move_mathematician 0 right)

end Solution

namespace StructuralRecursion

def intermediate_states_structural_rec : (n: Nat) -> n < 11 → State
  | 0, _ => initial_state
  | n+1, h =>
    let prev := intermediate_states_structural_rec n (Nat.lt_of_succ_lt h)
    (intermediate_steps.get ⟨n, Nat.lt_of_succ_lt h⟩) prev

def intermediate_states_structural : Fin 11 → State := (fun n =>  intermediate_states_structural_rec n.val n.isLt)

end StructuralRecursion


/-
# Well-founded recusion

Some types of recursion may lead to unterminated recursion. Well-founded recursion is a recursion closure together with a proof that a certain recursive definition terminates.

The result of `measure` allows argument j := <n+1,_> to fix to be compared against the recursive argument i:= <n,_> by mapping these arguments to the natural numbers.
-/

noncomputable def intermediate_states : Fin 11 → State :=
  WellFounded.fix (measure (fun (i : Fin 11) => i.val)).wf
    (fun i rec =>
      match i with
      | ⟨0, _⟩ => initial_state
      | ⟨n+1, h⟩ =>
        let prev := rec ⟨n, Nat.lt_of_succ_lt h⟩ (Nat.lt_succ_self n)
        (intermediate_steps.get ⟨n, Nat.lt_of_succ_lt h⟩) prev
    )

-- `noncomputable` means not executable code is compiled

example : intermediate_states 0 = initial_state := by
  decide

example : (intermediate_states  9) = final_state := by
  decide

theorem all_states_safe : ∀ i : Fin 11, no_notebook_left_behind (intermediate_states  i) := by
  decide
