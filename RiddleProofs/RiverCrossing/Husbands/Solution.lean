import RiddleProofs.RiverCrossing.Husbands.Moves

open Move

-- One known solution to the Jealous Husbands riddle
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
