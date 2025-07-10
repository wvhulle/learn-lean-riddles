import RiddleProofs.JealousHusbands.Moves

instance : DecidableEq RiverCrossingState := by infer_instance

partial def solve_with_bfs (max_depth : Nat := 15) : Option (List Move) :=
  let rec bfs (queue : List (RiverCrossingState × List Move)) (visited : List RiverCrossingState) : Option (List Move) :=
    match queue with
    | [] => none
    | (current_state, moves) :: rest =>
      if moves.length > max_depth then
        bfs rest visited
      else if current_state == final_state then
        some moves.reverse
      else if visited.contains current_state then
        bfs rest visited
      else
        let new_visited := current_state :: visited
        let transitions := (generate_valid_moves current_state).filterMap (fun move =>
          let new_state := apply_simple_move move current_state
          if state_safe new_state then
            if !new_visited.contains new_state then
              some (new_state, move :: moves)
            else none
          else none)
        bfs (rest ++ transitions) new_visited

  bfs [(initial_state, [])] []

def search_solution : Option (List Move) := solve_with_bfs 15

axiom search_solution_correct: ∀ sol, search_solution = some sol → validate_solution sol = true

-- Uncomment to see an internal representation of the solution found
-- Cannot be reduced fully because of partiality
-- #reduce search_solution.get!
-- Eval cannot evaluate it because the output (and Move) does not implement `Repr` yet
-- #eval search_solution.get!
