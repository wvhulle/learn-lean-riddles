import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves
import RiddleProofs.JealousHusbands.Validation

/-!
# Known Solutions for the Jealous Husbands Problem

This file contains hardcoded solution patterns that are known to work.
-/

-- Classic solution pattern using Move type
def classic_move_solution : List Move := [
  Move.wife_pair 0 1,      -- Step 1: W0, W1 cross
  Move.wife 0,             -- Step 2: W0 returns
  Move.wife_pair 0 2,      -- Step 3: W0, W2 cross
  Move.wife 1,             -- Step 4: W1 returns
  Move.husband_pair 0 1,   -- Step 5: H0, H1 cross
  Move.couple 1,           -- Step 6: H1, W1 return
  Move.husband_pair 1 2,   -- Step 7: H1, H2 cross
  Move.wife 2,             -- Step 8: W2 returns
  Move.wife_pair 1 2,      -- Step 9: W1, W2 cross
  Move.husband 0,          -- Step 10: H0 returns
  Move.couple 0            -- Step 11: H0, W0 cross
]

-- Optimal solution pattern using SimpleMove type
def optimal_solution_pattern : List SimpleMove := [
  SimpleMove.two_wives 0 1,           -- Step 1: W0, W1 cross
  SimpleMove.single_wife 0,           -- Step 2: W0 returns
  SimpleMove.two_wives 0 2,           -- Step 3: W0, W2 cross
  SimpleMove.single_wife 0,           -- Step 4: W0 returns
  SimpleMove.two_husbands 1 2,        -- Step 5: H1, H2 cross
  SimpleMove.married_couple 1,        -- Step 6: H1, W1 return
  SimpleMove.two_husbands 0 1,        -- Step 7: H0, H1 cross
  SimpleMove.single_wife 2,           -- Step 8: W2 returns
  SimpleMove.two_wives 0 1,           -- Step 9: W0, W1 cross
  SimpleMove.single_wife 0,           -- Step 10: W0 returns
  SimpleMove.two_wives 0 2            -- Step 11: W0, W2 cross
]

-- Verify the classic solution works
def verify_classic_solution : Bool :=
  let final_check := classic_move_solution.foldl (fun state move => apply_move move state) initial_state
  final_check = final_state && moves_safe classic_move_solution

-- Verify the optimal solution works
def verify_optimal_solution : Bool := validate_solution optimal_solution_pattern

-- Get the best working solution
def get_best_solution : Option (List SimpleMove) :=
  if verify_optimal_solution then some optimal_solution_pattern
  else none

-- Display the optimal solution in readable format
def display_optimal_solution : List String :=
  match get_best_solution with
  | none => ["No verified solution available"]
  | some moves =>
    ("Optimal solution with " ++ toString moves.length ++ " moves:") ::
    format_simple_solution moves
