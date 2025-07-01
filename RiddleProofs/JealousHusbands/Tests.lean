import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves
import RiddleProofs.JealousHusbands.SearchAlgorithms
import RiddleProofs.JealousHusbands.Validation
import RiddleProofs.JealousHusbands.KnownSolutions

/-!
# Tests for the Jealous Husbands Problem

This file contains test functions and evaluation commands to verify the solutions work correctly.
-/

-- Test and display the found solution
def display_solution : List String :=
  match found_solution with
  | none => ["No solution found"]
  | some moves => format_solution moves

-- Test the first few moves correctly
def test_first_moves : List String :=
  let moves := [
    Move.wife_pair 0 1,  -- Two wives cross
    Move.wife 0,         -- One wife returns
    Move.wife_pair 0 2,  -- Two wives cross
    Move.wife 1          -- One wife returns
  ]
  trace_moves_with_safety moves

-- Convert the found solution to transfers (for compatibility)
def solution_to_transfers (moves : List Move) : Option (Vector (State → State) n_states) :=
  if moves.length + 1 ≠ n_states then none
  else
    let convert_move (move : Move) : State → State :=
      fun s => apply_move move s
    some (Vector.ofFn (fun ⟨k, _⟩ =>
      if k = 0 then id
      else convert_move (moves[k-1]!)))

-- Test our found solution with transfers
def working_transfers : Option (Vector (State → State) n_states) :=
  match found_solution with
  | none => none
  | some moves => solution_to_transfers moves

-- Test if all corrected states are safe
def test_all_safe : Option Bool :=
  match working_transfers with
  | none => none
  | some transfers_vec =>
    let test_states : Fin n_states → State := fun ⟨n, h⟩ =>
      let rec apply_n (i : Nat) (hi : i ≤ n) (s : State) : State :=
        if hi' : i = 0 then s
        else
          have : i - 1 < n_states := by
            have i_pos : i > 0 := Nat.pos_of_ne_zero hi'
            have i_le_n : i ≤ n := hi
            have n_lt : n < n_states := h
            omega
          let prev := apply_n (i-1) (Nat.le_trans (Nat.sub_le i 1) hi) s
          (transfers_vec.get ⟨i-1, by omega⟩) prev
      apply_n n (Nat.le_refl n) initial_state
    some ((List.range n_states).all fun i =>
      if hi : i < n_states then
        state_safe (test_states ⟨i, hi⟩)
      else true)

-- Display the robust solution
def display_robust_solution : List String :=
  match robust_solution with
  | none => ["No solution found with robust solver"]
  | some moves =>
    if validate_solution moves then
      "Solution found and validated:" :: format_simple_solution moves
    else
      ["Solution found but validation failed"]

-- =============================================
-- EVALUATION COMMANDS
-- =============================================

-- Test the original solver
-- #eval found_solution
-- #eval display_solution
-- #eval solution_safe (some found_solution.get!)
-- #eval verify_classic_solution
-- #eval test_first_moves
-- #eval working_transfers.isSome

-- Test the robust solver
-- #eval robust_solution
-- #eval simple_solution_safe robust_solution
-- #eval display_robust_solution
-- #eval verify_optimal_solution
-- #eval display_optimal_solution
