import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves

/-!
# Solution Validation for the Jealous Husbands Problem

This file contains functions to validate solutions and check if they are correct.
-/

-- Apply a sequence of moves to see the resulting states
def trace_moves (moves : List Move) : List State :=
  moves.foldl (fun states move => (apply_move move states.head!) :: states) [initial_state] |>.reverse

-- Check if a sequence of moves is completely safe
def moves_safe (moves : List Move) : Bool :=
  (trace_moves moves).all state_safe

-- Validate a solution by checking all states are safe and reach final state
def validate_solution (moves : List SimpleMove) : Bool :=
  let rec check_moves (s : State) (ms : List SimpleMove) : Bool :=
    match ms with
    | [] => s = final_state
    | m :: rest =>
      if simple_move_valid m s then
        let new_state := apply_simple_move m s
        if state_safe new_state then
          check_moves new_state rest
        else false
      else false
  check_moves initial_state moves

-- Test if a Move solution is safe and reaches the final state
def solution_safe (moves : Option (List Move)) : Bool :=
  match moves with
  | none => false
  | some moves => moves_safe moves && (moves.foldl (fun state move => apply_move move state) initial_state = final_state)

-- Test if a SimpleMove solution is safe and reaches the final state
def simple_solution_safe (moves : Option (List SimpleMove)) : Bool :=
  match moves with
  | none => false
  | some moves => validate_solution moves

-- Helper to display states in a readable format
def state_to_string (s : State) : String :=
  let h_left := (List.range num_couples).filter fun i => s.husbands[i]! = RiverBank.left
  let h_right := (List.range num_couples).filter fun i => s.husbands[i]! = RiverBank.right
  let w_left := (List.range num_couples).filter fun i => s.wives[i]! = RiverBank.left
  let w_right := (List.range num_couples).filter fun i => s.wives[i]! = RiverBank.right
  s!"Left: H{h_left} W{w_left}, Right: H{h_right} W{w_right}, Boat: {s.boat}"

-- Apply moves and display each step with safety check
def trace_moves_with_safety (moves : List Move) : List String :=
  let rec apply_moves (s : State) (ms : List Move) : List String :=
    match ms with
    | [] => [state_to_string s]
    | m :: rest =>
      let new_state := apply_move m s
      let safe := state_safe new_state
      (state_to_string new_state ++ s!" (safe: {safe})") :: apply_moves new_state rest
  apply_moves initial_state moves
