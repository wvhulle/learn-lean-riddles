
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

-- A move: either one or two items cross the river, with a proof that the move preserves safety
inductive Move where
| one (f : State → State) (h : ∀ s, safe s → safe (f s))
| two (f : State → State) (h : ∀ s, safe s → safe (f s))

-- Helper to apply a Move to a State
 def applyMove : Move → State → State
| Move.one f _, s => f s
| Move.two f _, s => f s

-- A single step in the puzzle: applying a move to a state, assuming the state is safe
inductive Step : State → State → Prop
| mk (m : Move) (s : State) (h : safe s) : Step s (applyMove m s)

-- Helper to flip a bank (left ↔ right)
def flipBank : RiverBank → RiverBank := fun
| left => right
| right => left


-- Initial state: everyone and everything on the left bank
def all_left : State :=
  { boat := left, mathematicians := Vector.replicate 3 left, notebooks := Vector.replicate 3 left }

-- Goal state: everyone and everything on the right bank
def all_right : State :=
  { boat := right, mathematicians := Vector.replicate 3 right, notebooks := Vector.replicate 3 right }



-- There exists a sequence of states from initial to goal (trivial version)
theorem impossible_path_safe :
  ∃ (path : List State),
    path.head? = some  all_left ∧
    path.getLast? = some all_right ∧
    True :=
  ⟨[all_left, all_right], rfl, rfl, trivial⟩


theorem length_more_one  {α: Type} (list: List α): (list.length > 1) -> (list ≠ []) := by
  intro l
  induction list
  · contradiction
  · simp




-- Property: a path is safe if every state in the path is safe
 def safe_cross_seq (path : List State) : Prop := ∀ i : Fin path.length, safe (path.get i)


-- Move a mathematician to a given bank
 def move_math (n : Fin 3) (b : RiverBank) (s : State) : State :=
  { s with mathematicians := s.mathematicians.set n b }

-- Move a notebook to a given bank
 def move_notebook (n : Fin 3) (b : RiverBank) (s : State) : State :=
  { s with notebooks := s.notebooks.set n b }

-- Move the boat to a given bank
 def move_boat (b : RiverBank) (s : State) : State :=
  { s with boat := b }


-- Operator for function composition in the order: f ▷ g = g ∘ f (i.e., do f, then g)
infixl:80 " ▷ " => Function.comp


-- A solution as a vector of crossing functions (State → State)
def solution_cross_vec : Vector (State → State) 11 :=
  Vector.ofFn (fun
    | 0 => move_math 0 right ▷ move_notebook 0 right ▷ move_boat right
    | 1 => move_math 0 left ▷ move_notebook 0 left ▷ move_boat left
    | 2 => move_math 1 right ▷ move_notebook 1 right ▷ move_boat right
    | 3 => move_math 0 right ▷ move_notebook 0 right ▷ move_boat right
    | 4 => move_math 2 right ▷ move_notebook 2 right ▷ move_boat right
    | 5 => move_math 0 left ▷ move_notebook 0 left ▷ move_boat left
    | 6 => move_math 0 right ▷ move_notebook 0 right ▷ move_boat right
    | 7 => move_math 1 left ▷ move_notebook 1 left ▷ move_boat left
    | 8 => move_math 1 right ▷ move_notebook 1 right ▷ move_boat right
    | 9 => move_math 0 left ▷ move_notebook 0 left ▷ move_boat left
    | 10 => move_math 0 right ▷ move_notebook 0 right)

-- Helper function to compute state at step i
def solution_state_at : Fin 11 → State
| ⟨0, _⟩ => all_left
| ⟨n+1, h⟩ =>
  have n_lt_9 : n < 11 := by
    have : n + 1 < 11 := h
    cases Nat.lt_or_ge n 11 with
    | inl hlt => exact hlt
    | inr hge =>
      exact Nat.lt_of_succ_lt h
  (solution_cross_vec.get ⟨n, n_lt_9⟩) (solution_state_at ⟨n, Nat.lt_of_succ_lt h⟩)

-- Vector of 10 states: initial state, 8 intermediate states, and goal state
def solution_states : Vector State 11 := Vector.ofFn solution_state_at

-- Verify that the first state is all_left
example : solution_states.get 0 = all_left := by
  unfold solution_states
  simp [Vector.get, Vector.ofFn]
  unfold solution_state_at
  rfl


-- Verify that applying all transformations reaches the goal state
example : (solution_states.get 9) = all_right := by
  repeat
    simp [Vector.get, solution_states, solution_state_at]
    unfold solution_state_at
    simp [Vector.get]
    unfold solution_cross_vec
    unfold solution_state_at
    dsimp
    simp [move_math, move_notebook, move_boat]
  congr
  · simp [Vector.get, solution_cross_vec, move_notebook, move_boat]
    unfold solution_state_at
    simp [solution_cross_vec]
    unfold solution_state_at
    decide
  · simp [Vector.get, solution_cross_vec, move_notebook, move_boat]
    unfold solution_state_at
    simp [solution_cross_vec]
    unfold solution_state_at
    decide


-- Helper to examine specific states in the solution
def get_state (i : Nat) (h : i < 11) : State := solution_states.get ⟨i, h⟩

-- Examples of intermediate states
#check get_state 0 (by decide)  -- Initial state
#check get_state 1 (by decide)  -- After first crossing
#check get_state 5 (by decide)  -- Middle state
#check safe (get_state 9 (by decide))   -- Final state


theorem final_safe: safe (all_right):= by
  rw [safe]
  intro i j ineqj
  rw [all_right]
  simp


theorem all_states_safe : ∀ i : Fin 11, safe (solution_states.get i) := by
  sorry
