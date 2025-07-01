import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Solution
import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves

-- Simple BFS solver
partial def solve_with_bfs (max_depth : Nat := 15) : Option (List Move) :=
  let rec bfs (queue : List (State × List Move)) (visited : List State) : Option (List Move) :=
    match queue with
    | [] => none
    | (current_state, moves) :: rest =>
      if moves.length > max_depth then
        bfs rest visited
      else if current_state = final_state then
        some moves.reverse
      else if current_state ∈ visited then
        bfs rest visited
      else
        let new_visited := current_state :: visited
        let transitions := (generate_valid_moves current_state).filterMap (fun move =>
          let new_state := apply_simple_move move current_state
          if state_safe new_state ∧ new_state ∉ new_visited then
            some (new_state, move :: moves)
          else none)
        bfs (rest ++ transitions) new_visited

  bfs [(initial_state, [])] []

-- Main solution function
def search_solution : Option (List Move) := solve_with_bfs 15


-- The solution to the problem
def solution : List Move := optimal_solution

-- Get solution from search if preferred
def search_based_solution : Option (List Move) := search_solution

-- Choose the best available solution (prefer search result if valid, otherwise use known solution)
def best_solution : List Move :=
  match search_based_solution with
  | some moves => if validate_solution moves then moves else solution
  | none => solution

-- Verify the solution is correct
theorem solution_correct : validate_solution solution = true := by
  decide


-- Convert simple solution to readable format
def format_simple_solution (moves : List Move) : List String :=
  moves.map fun move => match move with
  | Move.single_husband i => s!"Husband {i.val} crosses"
  | Move.single_wife i => s!"Wife {i.val} crosses"
  | Move.two_husbands i j => s!"Husbands {i.val} and {j.val} cross"
  | Move.two_wives i j => s!"Wives {i.val} and {j.val} cross"
  | Move.married_couple i => s!"Couple {i.val} crosses"


-- Display the complete solution step by step
def display_solution : List String :=
  [s!"Jealous Husbands Problem - Solution ({best_solution.length} moves):"] ++
  format_simple_solution best_solution

-- The final answer
def solve_jealous_husbands : List String := display_solution

-- #eval display_solution
