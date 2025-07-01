import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves

/-!
# Search Algorithms for the Jealous Husbands Problem

This file contains breadth-first search algorithms to find solutions to the jealous husbands problem.
-/

-- BFS search state for the robust solver
structure SearchState where
  current : State
  path : List SimpleMove
  depth : Nat
deriving Repr

-- Check if two states are equal (for visited set)
def states_equal (s1 s2 : State) : Bool :=
  s1 = s2

-- Original BFS search for solutions
partial def search_solution (max_depth : Nat) : Option (List Move) :=
  let rec bfs (queue : List (State × List Move)) (visited : List State) : Option (List Move) :=
    match queue with
    | [] => none
    | (current_state, moves) :: rest =>
      -- Check depth limit based on actual move count
      if moves.length > max_depth then
        bfs rest visited
      else if current_state = final_state then
        some moves.reverse
      else if current_state ∈ visited then
        bfs rest visited
      else
        let new_visited := current_state :: visited
        let valid_moves := (possible_moves current_state).filter (fun move =>
          let new_state := apply_move move current_state
          state_safe new_state && new_state ∉ new_visited)
        let new_queue := rest ++ valid_moves.map (fun move =>
          (apply_move move current_state, move :: moves))
        bfs new_queue new_visited
  bfs [(initial_state, [])] []

-- Robust BFS solver with proper termination
partial def robust_bfs_solver (max_depth : Nat := 20) : Option (List SimpleMove) :=
  let rec bfs_loop (queue : List SearchState) (visited : List State) (iterations : Nat) : Option (List SimpleMove) :=
    -- Safety check: max iterations to prevent infinite loops
    if iterations > 1000 then none
    else
      match queue with
      | [] => none -- No solution found
      | search_state :: rest =>
        let current := search_state.current
        let path := search_state.path
        let depth := search_state.depth

        -- Check if we've reached the goal
        if current = final_state then
          some path.reverse
        -- Check depth limit
        else if depth >= max_depth then
          bfs_loop rest visited (iterations + 1)
        -- Check if we've seen this state before
        else if visited.any (states_equal current) then
          bfs_loop rest visited (iterations + 1)
        else
          -- Generate new states
          let new_visited := current :: visited
          let valid_moves := generate_valid_moves current
          let new_states := valid_moves.filterMap (fun move =>
            let new_state := apply_simple_move move current
            if state_safe new_state && ¬new_visited.any (states_equal new_state) then
              some { current := new_state, path := move :: path, depth := depth + 1 }
            else none)
          bfs_loop (rest ++ new_states) new_visited (iterations + 1)

  -- Start BFS from initial state
  if state_safe initial_state then
    bfs_loop [{ current := initial_state, path := [], depth := 0 }] [] 0
  else none

-- Find solution with reasonable depth limit
def found_solution : Option (List Move) := search_solution 15

-- Find the robust solution
def robust_solution : Option (List SimpleMove) := robust_bfs_solver 15
