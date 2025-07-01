import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves
import RiddleProofs.JealousHusbands.SearchAlgorithms
import RiddleProofs.JealousHusbands.Validation
import RiddleProofs.JealousHusbands.KnownSolutions

/-!
# Solution to the Jealous Husbands Problem

This file provides the main solution interface, showing the fastest and shortest solution
to the jealous husbands river crossing problem.

## Problem Statement
Three married couples must cross a river using a boat that holds at most two people.
The constraint is that no woman can be in the presence of another man unless her husband
is also present (to prevent jealousy).

## Solution
The optimal solution requires exactly 11 moves and ensures all safety constraints are met.
-/

-- The shortest known solution (11 moves)
def shortest_solution : List SimpleMove := optimal_solution_pattern

-- Verify the solution is correct
def solution_is_valid : Bool := verify_optimal_solution

-- Get solution length
def solution_length : Nat := shortest_solution.length

-- Display the complete solution step by step
def solution_steps : List String := format_simple_solution shortest_solution

-- Verify all intermediate states are safe
def all_states_safe : Bool := validate_solution shortest_solution

-- Summary of the solution
def solution_summary : List String := [
  s!"Jealous Husbands Problem - Optimal Solution",
  s!"======================================",
  s!"Number of moves: {solution_length}",
  s!"Solution valid: {solution_is_valid}",
  s!"All states safe: {all_states_safe}",
  s!"",
  s!"Solution steps:"
] ++ solution_steps

-- Alternative: get solution from search algorithm if preferred
def algorithmic_solution : Option (List SimpleMove) := robust_solution

-- Choose the best available solution
def best_solution : List SimpleMove :=
  match algorithmic_solution with
  | some moves => if validate_solution moves then moves else shortest_solution
  | none => shortest_solution

-- Final answer - the definitive solution to the problem
def final_solution : List String := [
  s!"SOLUTION TO THE JEALOUS HUSBANDS PROBLEM",
  s!"==========================================",
  s!"",
  s!"The problem can be solved in exactly {best_solution.length} moves:",
  s!""
] ++ format_simple_solution best_solution ++ [
  s!"",
  s!"This solution ensures that at every step, no wife is alone with",
  s!"a man other than her husband, thus satisfying the jealousy constraint.",
  s!"",
  s!"Verification: {validate_solution best_solution}"
]

-- Quick verification that the solution works
theorem solution_correct : validate_solution shortest_solution = true := by
  decide

-- Export the solution for easy access
def solve_jealous_husbands : List String := final_solution

-- =============================================
-- EVALUATION - The Final Answer
-- =============================================

-- #eval solve_jealous_husbands
