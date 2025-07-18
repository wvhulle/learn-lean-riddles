import RiddleProofs.RiverCrossing.Husbands.Notation
import RiddleProofs.RiverCrossing.Husbands.Validate


open RiverCrossing.Husbands




def generate_valid_moves (s : JealousHusbandsState) : List Move :=
  let couples : List (Fin num_couples) := [0, 1, 2]
  let direction := if s.boat == RiverBank.left then Direction.toRight else Direction.toLeft

  let single_moves :=
    couples.flatMap fun i =>
      if direction == Direction.toRight then
        [R {Person.husband i}, R {Person.wife i}]
      else
        [L {Person.husband i}, L {Person.wife i}]

  let pair_moves :=
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

  let couple_moves :=
    couples.map fun i =>
      if direction == Direction.toRight then
        R {Person.husband i, Person.wife i}
      else
        L {Person.husband i, Person.wife i}

  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)


partial def solve_with_bfs (max_depth : Nat := 15) : Option (List Move) :=
  let rec bfs (queue : List (JealousHusbandsState × List Move))
      (visited : List JealousHusbandsState) : Option (List Move) :=
    match queue with
    | [] => none
    | (current_state, moves) :: rest =>
      if moves.length > max_depth then
        bfs rest visited
      else if current_state == jealous_husbands_final_state then
        some moves.reverse
      else if visited.contains current_state then
        bfs rest visited
      else
        let new_visited := current_state :: visited
        let transitions := (generate_valid_moves current_state).filterMap (fun move =>
          let new_state := apply_simple_move move current_state
          if bank_safe new_state then
            if !new_visited.contains new_state then
              some (new_state, move :: moves)
            else none
          else none)
        bfs (rest ++ transitions) new_visited

  bfs [(jealous_husbands_initial_state, [])] []

def search_solution : Option (List Move) := solve_with_bfs 15


-- #reduce computes by definitional unfolding (slow but works in proofs)
#reduce search_solution
-- #eval uses compiled bytecode for efficiency (fast but not usable in proofs)
#eval search_solution
