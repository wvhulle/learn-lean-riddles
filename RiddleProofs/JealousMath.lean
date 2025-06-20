import Init.WF

-- River crossing puzzle: Three jealous mathematicians (A, B, C) and their three secret notebooks (a, b, c) must cross a river.
-- The boat carries at most two items (people or notebooks).
-- No mathematician may be left alone with another’s notebook unless the owner is present.
-- Can they all get across safely?

-- The two river banks
inductive RiverBank
| left | right
  deriving DecidableEq, Repr, Inhabited

open RiverBank

-- The full state of the puzzle: positions of boat, mathematicians, and notebooks
structure State where
  boat : RiverBank  -- Boat position
  mathematicians : Vector RiverBank 3
  notebooks : Vector  RiverBank 3
  deriving Repr, DecidableEq

-- Safety condition: no notebook is ever with another mathematician unless its owner is present
-- (i.e., notebook i cannot be with mathematician j unless mathematician i is also present, for i ≠ j)
def safe (s : State) : Prop :=
  ∀ i j : Fin 3, (i ≠ j) →
    let Ni := s.notebooks[i]!
    let Mj := s.mathematicians[j]!
    let Mi := s.mathematicians[i]!
    Ni = Mj → Mi = Mj


instance : DecidablePred safe := by
  unfold safe
  infer_instance

-- Initial state: everyone and everything on the left bank
def initial_state : State :=
  { boat := left, mathematicians := Vector.replicate 3 left, notebooks := Vector.replicate 3 left }

-- Goal state: everyone and everything on the right bank
def final_state : State :=
  { boat := right, mathematicians := Vector.replicate 3 right, notebooks := Vector.replicate 3 right }


theorem final_safe: safe (final_state):= by
  rw [safe]
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



 def safe_cross_seq (path : List State) : Prop := ∀ i : Fin path.length, safe (path.get i)


 def move_mathematician (n : Fin 3) (b : RiverBank) (s : State) : State :=
  { s with mathematicians := s.mathematicians.set n b }

 def move_notebook (n : Fin 3) (b : RiverBank) (s : State) : State :=
  { s with notebooks := s.notebooks.set n b }

 def move_boat (b : RiverBank) (s : State) : State :=
  { s with boat := b }


-- Operator for function composition in the order: f ▷ g = g ∘ f (i.e., do f, then g)
infixl:80 " ▷ " => Function.comp


-- A solution as a vector of crossing functions (State → State)
def intermediate_steps : Vector (State → State) 11 :=
  Vector.ofFn (fun
    | 0 => move_mathematician 0 right ▷ move_notebook 0 right ▷ move_boat right
    | 1 => move_mathematician 0 left ▷ move_notebook 0 left ▷ move_boat left
    | 2 => move_mathematician 1 right ▷ move_notebook 1 right ▷ move_boat right
    | 3 => move_mathematician 0 right ▷ move_notebook 0 right ▷ move_boat right
    | 4 => move_mathematician 2 right ▷ move_notebook 2 right ▷ move_boat right
    | 5 => move_mathematician 0 left ▷ move_notebook 0 left ▷ move_boat left
    | 6 => move_mathematician 0 right ▷ move_notebook 0 right ▷ move_boat right
    | 7 => move_mathematician 1 left ▷ move_notebook 1 left ▷ move_boat left
    | 8 => move_mathematician 1 right ▷ move_notebook 1 right ▷ move_boat right
    | 9 => move_mathematician 0 left ▷ move_notebook 0 left ▷ move_boat left
    | 10 => move_mathematician 0 right ▷ move_notebook 0 right)



noncomputable def intermediate_states : Fin 11 → State :=
  WellFounded.fix (measure (fun (i : Fin 11) => i.val)).wf
    (fun i rec =>
      match i with
      | ⟨0, _⟩ => initial_state
      | ⟨n+1, h⟩ =>
        let prev := rec ⟨n, Nat.lt_of_succ_lt h⟩ (Nat.lt_succ_self n)
        (intermediate_steps.get ⟨n, Nat.lt_of_succ_lt h⟩) prev
    )


example : intermediate_states 0 = initial_state := by
  unfold intermediate_states
  simp [Vector.get, Vector.ofFn]
  rfl


example : (intermediate_states  9) = final_state := by
  repeat
    simp [Vector.get, solution_states, intermediate_states]
    unfold intermediate_states
    simp [Vector.get]
    unfold intermediate_steps
    unfold intermediate_states
    dsimp
    simp [move_mathematician, move_notebook, move_boat]
  congr


theorem all_states_safe : ∀ i : Fin 11, safe (intermediate_states  i) := by
  decide
