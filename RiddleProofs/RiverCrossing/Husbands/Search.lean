import RiddleProofs.RiverCrossing.Husbands.Notation
import RiddleProofs.RiverCrossing.Husbands.Validate


open RiverCrossing.Husbands




def get_direction (boat_position : RiverBank) : Direction :=
  if boat_position == RiverBank.left then Direction.toRight else Direction.toLeft

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
  let direction := get_direction s.boat

  let single_moves := generate_single_person_moves direction couples
  let pair_moves := generate_pair_moves direction couples
  let couple_moves := generate_couple_moves direction couples

  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)


structure SearchConfig (State Move : Type) [BEq State] where
  initial_state : State
  is_goal : State → Bool
  generate_moves : State → List Move
  apply_move : Move → State → State
  is_valid_state : State → Bool
  max_depth : Nat := 15

partial def generic_bfs {State Move : Type} [BEq State]
    (config : SearchConfig State Move) : Option (List Move) :=
  let rec bfs (queue : List (State × List Move))
              (visited : List State) : Option (List Move) :=
    match queue with
    | [] => none
    | (current_state, path) :: rest =>
      if path.length > config.max_depth then
        bfs rest visited
      else if config.is_goal current_state then
        some path.reverse
      else if visited.contains current_state then
        bfs rest visited
      else
        let new_visited := current_state :: visited
        let next_states := (config.generate_moves current_state).filterMap fun move => do
          let new_state := config.apply_move move current_state
          guard (config.is_valid_state new_state && !new_visited.contains new_state)
          pure (new_state, move :: path)
        bfs (rest ++ next_states) new_visited

  bfs [(config.initial_state, [])] []

def is_goal_state (state : JealousHusbandsState) : Bool :=
  state == jealous_husbands_final_state

partial def solve_with_bfs (max_depth : Nat := 15) : Option (List Move) :=
  generic_bfs {
    initial_state := jealous_husbands_initial_state
    is_goal := is_goal_state
    generate_moves := generate_valid_moves
    apply_move := apply_simple_move
    is_valid_state := bank_safe
    max_depth := max_depth
  }

def search_solution : Option (List Move) := solve_with_bfs 15


-- #reduce computes by definitional unfolding (slow but works in proofs)
-- #reduce search_solution
-- #eval uses compiled bytecode for efficiency (fast but not usable in proofs)
#eval search_solution
