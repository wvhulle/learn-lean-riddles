import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves

open Move

/-!
# Known Solution for the Jealous Husbands Problem

This file contains the optimal 11-move solution to the problem.
-/

-- The optimal solution (11 moves) with explicit directions
def hardwired_solution : List Move := [
  R {W 0, W 1},
  L {W 0},
  R {W 0, W 2},
  L {W 0},
  R {H 1, H 2},
  L {H 1, W 1},
  R {H 0, H 1},
  L {W 2},
  R {W 0, W 1},
  L {W 0},
  R {W 0, W 2}
]


theorem hardwired_solution_correct : validate_solution hardwired_solution = true := by decide
