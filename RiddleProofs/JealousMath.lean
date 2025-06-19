-- River crossing puzzle: Three jealous mathematicians (A, B, C) and their three secret notebooks (a, b, c) must cross a river.
-- The boat carries at most two items (people or notebooks).
-- No mathematician may be left alone with another’s notebook unless the owner is present.
-- Can they all get across safely?

-- The two river banks
inductive Bank
| left | right
  deriving DecidableEq, Repr, Inhabited

open Bank

-- The full state of the puzzle: positions of boat, mathematicians, and notebooks
structure State where
  boat : Bank  -- Boat position
  maths : Vector Bank 3  -- Mathematicians (A, B, C)
  notebooks : Vector  Bank 3  -- Notebooks (a, b, c)
  deriving Repr, DecidableEq

-- Safety condition: no notebook is ever with another mathematician unless its owner is present
-- (i.e., notebook i cannot be with mathematician j unless mathematician i is also present, for i ≠ j)
def safe (s : State) : Prop :=
  ∀ i j : Fin 3, (i ≠ j) →
    let Ni := s.notebooks[i]!
    let Mj := s.maths[j]!
    let Mi := s.maths[i]!
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
def flipBank : Bank → Bank := fun
| left => right
| right => left


-- Initial state: everyone and everything on the left bank
def initial_left : State :=
  { boat := left, maths := Vector.replicate 3 left, notebooks := Vector.replicate 3 left }

-- Goal state: everyone and everything on the right bank
def final_right : State :=
  { boat := right, maths := Vector.replicate 3 right, notebooks := Vector.replicate 3 right }

-- Example: move mathematician 1 (A) alone across
def move_one_mathematician : State → State := fun
  | s => if s = initial_left then { s with maths := s.maths.set 0 right (by simp), notebooks := s.notebooks.set 0 right (by simp) } else s

open Classical


-- Proof that moving m1 alone preserves safety (details omitted)
theorem move_one_m_safe : safe (move_one_mathematician initial_left) := by
  simp [move_one_mathematician, safe]
  intro i j ineqj
  intro h
  rw [<- h]

  apply Or.elim (em (i = 0))
  case left =>
    intro i_one
    rw [i_one]
    exact rfl
  case right =>
    intro i_not_one
    exact rfl

-- There exists a sequence of states from initial to goal (trivial version)
theorem impossible_path_safe :
  ∃ (path : List State),
    path.head? = some  initial_left ∧
    path.getLast? = some final_right ∧
    True :=
  ⟨[initial_left, final_right], rfl, rfl, trivial⟩


theorem length_more_one  {α: Type} (list: List α): (list.length > 1) -> (list ≠ []) := by
  intro l
  induction list
  · contradiction
  · simp


theorem path_is_safe (path : List State)  (h : path.length > 1): ∃ start last, (path.head =  start) ∧ (path.getLast =  last) ∧ (∀ i: Fin path.length, safe (path.get i)) := by
  sorry
