/-!
# The Wolf, Goat, and Cabbage Puzzle

A farmer must transport a wolf, a goat, and a cabbage across a river. The boat can only carry the farmer and one item. If left alone, the wolf will eat the goat, and the goat will eat the cabbage. Can the farmer get all three items across safely?
-/

inductive Item | wolf | goat | cabbage deriving DecidableEq, Repr
inductive Bank | left | right deriving DecidableEq, Repr

open Item Bank

/-- Helper to get opposite bank -/
def Bank.opposite : Bank → Bank
  | left => right
  | right => left

structure State where
  farmer : Bank
  wolf : Bank
  goat : Bank
  cabbage : Bank
  deriving Repr, DecidableEq

/-- Get the bank location of a specific item -/
def State.itemBank (s : State) : Item → Bank
  | Item.wolf => s.wolf
  | Item.goat => s.goat
  | Item.cabbage => s.cabbage

/-- Move a specific item to a new bank -/
def State.moveItem (s : State) (item : Item) (bank : Bank) : State :=
  match item with
  | Item.wolf => { s with wolf := bank }
  | Item.goat => { s with goat := bank }
  | Item.cabbage => { s with cabbage := bank }

/-- The state is safe if the goat is not left alone with the wolf, and the goat is not left alone with the cabbage, unless the farmer is present. -/
def safe (s : State) : Bool :=
  (s.goat = s.farmer ∨ s.goat ≠ s.wolf) ∧
  (s.goat = s.farmer ∨ s.goat ≠ s.cabbage)

/-- Initial state: everything on the left bank. -/
def initial : State := { farmer := left, wolf := left, goat := left, cabbage := left }
/-- Goal state: everything on the right bank. -/
def goal : State := { farmer := right, wolf := right, goat := right, cabbage := right }

/-- Helper to create states more readably -/
def mkState (farmer wolf goat cabbage : Bank) : State :=
  { farmer, wolf, goat, cabbage }

/-- A move is the farmer crossing the river, possibly taking one item. -/
def possible_moves (s : State) : List State :=
  let new_bank := s.farmer.opposite
  let try_move (item? : Option Item) : Option State :=
    let s' := match item? with
      | none => { s with farmer := new_bank }
      | some item =>
          if s.farmer = s.itemBank item then
            { s.moveItem item new_bank with farmer := new_bank }
          else
            s  -- Invalid move, will be filtered out by safety check
    if safe s' then some s' else none
  [none, some Item.wolf, some Item.goat, some Item.cabbage].filterMap try_move

/- Example: the initial state is safe. -/
#eval safe initial
/- Example: the goal state is safe. -/
#eval safe goal

/- Example: unsafe state (goat alone with wolf, farmer away) -/
#eval safe (mkState right left left right) -- false

/- Example: unsafe state (goat alone with cabbage, farmer away) -/
#eval safe (mkState right right left left) -- false

/- Example: safe state (farmer and goat together, wolf and cabbage separated) -/
#eval safe (mkState right left right left) -- true

/- Example: possible moves from initial state -/
#eval (possible_moves initial).map (fun s => (s.farmer, s.wolf, s.goat, s.cabbage))

/- Example: possible moves when farmer and goat are on right -/
#eval (possible_moves (mkState right left right left)).map (fun s => (s.farmer, s.wolf, s.goat, s.cabbage))

/-!
## Solution Strategy

The key insight is that the goat is the "problematic" item - it can't be left alone with either
the wolf or the cabbage. The solution involves:

1. Take the goat across first (farmer + goat → right)
2. Come back alone (farmer → left)
3. Take wolf or cabbage across (farmer + wolf/cabbage → right)
4. Bring goat back to prevent it from being alone with wolf/cabbage (farmer + goat → left)
5. Leave goat, take the other item across (farmer + cabbage/wolf → right)
6. Come back alone for the goat (farmer → left)
7. Take goat across to finish (farmer + goat → right)

This ensures the goat is never left alone with something it shouldn't be with.
-/

/-- Simple breadth-first search to find a solution path -/
partial def find_solution (start : State) (target : State) (visited : List State := []) : Option (List State) :=
  if start = target then
    some [start]
  else if start ∈ visited then
    none
  else
    let moves := possible_moves start
    let new_visited := start :: visited
    moves.findSome? fun next_state =>
      find_solution next_state target new_visited |>.map (start :: ·)

/-- Find and display a solution to the puzzle -/
def solve_puzzle : Option (List State) := find_solution initial goal

-- Uncomment to see a solution path:
-- #eval solve_puzzle.map (·.map (fun s => (s.farmer, s.wolf, s.goat, s.cabbage)))
