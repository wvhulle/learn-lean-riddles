/-!
# The Wolf, Goat, and Cabbage Puzzle

A farmer must transport a wolf, a goat, and a cabbage across a river. The boat can only carry the farmer and one item. If left alone, the wolf will eat the goat, and the goat will eat the cabbage. Can the farmer get all three items across safely?
-/

inductive Item | wolf | goat | cabbage deriving DecidableEq, Repr
inductive Bank | left | right deriving DecidableEq, Repr

open Item Bank

structure State where
  farmer : Bank
  wolf : Bank
  goat : Bank
  cabbage : Bank
  deriving Repr, DecidableEq

/-- The state is safe if the goat is not left alone with the wolf, and the goat is not left alone with the cabbage, unless the farmer is present. -/
def safe (s : State) : Bool :=
  (s.goat = s.farmer ∨ s.goat ≠ s.wolf) ∧
  (s.goat = s.farmer ∨ s.goat ≠ s.cabbage)

/-- Initial state: everything on the left bank. -/
def initial : State := { farmer := left, wolf := left, goat := left, cabbage := left }
/-- Goal state: everything on the right bank. -/
def goal : State := { farmer := right, wolf := right, goat := right, cabbage := right }

/-- A move is a set of items (at most one) to take with the farmer. -/
def possible_moves (s : State) : List (State) :=
  let move (f : State → State) :=
    let s' := f s; if safe s' then some s' else none
  [ -- Farmer alone
    move (fun s => { s with farmer := if s.farmer = left then right else left }),
    -- Farmer and wolf
    if s.farmer = s.wolf then move (fun s => { s with farmer := if s.farmer = left then right else left, wolf := if s.wolf = left then right else left }) else none,
    -- Farmer and goat
    if s.farmer = s.goat then move (fun s => { s with farmer := if s.farmer = left then right else left, goat := if s.goat = left then right else left }) else none,
    -- Farmer and cabbage
    if s.farmer = s.cabbage then move (fun s => { s with farmer := if s.farmer = left then right else left, cabbage := if s.cabbage = left then right else left }) else none
  ].filterMap id

/- Example: the initial state is safe. -/
#eval safe initial
/- Example: the goal state is safe. -/
#eval safe goal

/- Example: unsafe state (goat alone with wolf, farmer away) -/
#eval safe { farmer := right, wolf := left, goat := left, cabbage := right } -- false

/- Example: unsafe state (goat alone with cabbage, farmer away) -/
#eval safe { farmer := right, wolf := right, goat := left, cabbage := left } -- false

/- Example: safe state (farmer and goat away, wolf and cabbage left) -/
#eval safe { farmer := right, wolf := left, goat := right, cabbage := left } -- true
