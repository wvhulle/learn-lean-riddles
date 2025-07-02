import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves

open Move

/-!
# Known Solution for the Jealous Husbands Problem

This file contains the optimal 11-move solution to the problem.
-/

-- The optimal solution (11 moves) with explicit directions
def hardwired_solution : List Move := [
  R {W 0, W 1},      -- Step 1: R {W 0, W 1} cross
  L {W 0},           -- Step 2: L {W 0} returns
  R {W 0, W 2},      -- Step 3: R {W 0, W 2} cross
  L {W 0},           -- Step 4: L {W 0} returns
  R {H 1, H 2},      -- Step 5: R {H 1, H 2} cross
  L {H 1, W 1},      -- Step 6: L {H 1, W 1} return
  R {H 0, H 1},      -- Step 7: R {H 0, H 1} cross
  L {W 2},           -- Step 8: L {W 2} returns
  R {W 0, W 1},      -- Step 9: R {W 0, W 1} cross
  L {W 0},           -- Step 10: L {W 0} returns
  R {W 0, W 2}       -- Step 11: R {W 0, W 2} cross
]


-- Verify the solution is correct (statement only, proof would require manual work)
theorem hardwired_solution_correct : validate_solution hardwired_solution = true := by decide
