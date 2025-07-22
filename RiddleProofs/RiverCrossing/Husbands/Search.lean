import RiddleProofs.RiverCrossing.Husbands.Notation
import RiddleProofs.RiverCrossing.Husbands.Validate
import RiddleProofs.RiverCrossing.Search


open RiverCrossing.Husbands




def generate_single_person_moves (direction : Direction) (couples : List (Fin num_couples)) : List Move :=
  couples.flatMap fun i =>
    if direction == Direction.toRight then
      [R {Person.husband i}, R {Person.wife i}]
    else
      [L {Person.husband i}, L {Person.wife i}]

def generate_pair_moves (direction : Direction) (couples : List (Fin num_couples)) : List Move :=
  couples.flatMap fun i =>
    couples.flatMap fun j =>
      if h : i.val < j.val then
        let ne_proof : i ≠ j := Fin.ne_of_lt h
        if direction == Direction.toRight then
          [pair (Person.husband i) (Person.husband j) Direction.toRight (by simp [ne_proof]),
           pair (Person.wife i) (Person.wife j) Direction.toRight (by simp [ne_proof])]
        else
          [pair (Person.husband i) (Person.husband j) Direction.toLeft (by simp [ne_proof]),
           pair (Person.wife i) (Person.wife j) Direction.toLeft (by simp [ne_proof])]
      else []

def generate_couple_moves (direction : Direction) (couples : List (Fin num_couples)) : List Move :=
  couples.map fun i =>
    if direction == Direction.toRight then
      R {Person.husband i, Person.wife i}
    else
      L {Person.husband i, Person.wife i}

def generate_valid_moves (s : JealousHusbandsState) : List Move :=
  let couples : List (Fin num_couples) := [0, 1, 2]
  let direction := if s.boat == RiverBank.left then Direction.toRight else Direction.toLeft

  let single_moves := generate_single_person_moves direction couples
  let pair_moves := generate_pair_moves direction couples
  let couple_moves := generate_couple_moves direction couples

  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)


def is_goal_state (state : JealousHusbandsState) : Bool :=
  state == jealous_husbands_final_state

partial def solve_with_bfs (max_depth : Nat := 15) : Option (List Move) :=
  RiverCrossing.genericBFS {
    initialState := jealous_husbands_initial_state
    isGoal := is_goal_state
    generateMoves := generate_valid_moves
    applyMove := apply_simple_move
    isValidState := bank_safe
    maxDepth := max_depth
  }

def search_solution : Option (List Move) := solve_with_bfs 15


-- #reduce computes by definitional unfolding (slow but works in proofs)
-- #reduce search_solution
-- #eval uses compiled bytecode for efficiency (fast but not usable in proofs)
#eval search_solution
