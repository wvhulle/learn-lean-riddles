import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves

/-!
# Known Solution for the Jealous Husbands Problem

This file contains the optimal 11-move solution to the problem.
-/

-- The optimal solution (11 moves)
def hardwired_solution : List Move := [
  Move.two_wives 0 1,           -- Step 1: W0, W1 cross
  Move.single_wife 0,           -- Step 2: W0 returns
  Move.two_wives 0 2,           -- Step 3: W0, W2 cross
  Move.single_wife 0,           -- Step 4: W0 returns
  Move.two_husbands 1 2,        -- Step 5: H1, H2 cross
  Move.married_couple 1,        -- Step 6: H1, W1 return
  Move.two_husbands 0 1,        -- Step 7: H0, H1 cross
  Move.single_wife 2,           -- Step 8: W2 returns
  Move.two_wives 0 1,           -- Step 9: W0, W1 cross
  Move.single_wife 0,           -- Step 10: W0 returns
  Move.two_wives 0 2            -- Step 11: W0, W2 cross
]


-- Verify the solution is correct
theorem hardwired_solution_correct : validate_solution hardwired_solution = true := by
  decide
