import Claude

def print_states_and_safety : IO Unit :=
  let moves := Claude.correct_solution_moves
  let states := List.scanl Claude.apply_move Claude.initial_state moves
  let safe := states.map Claude.is_safe_state
  let zipped := List.zip (List.range states.length) (List.zip states safe)
  for (i, (st, ok)) in zipped do
    IO.println s!"Step {i}: safe = {ok}, state = {st}"

def main : IO Unit := print_states_and_safety

#eval print_states_and_safety
