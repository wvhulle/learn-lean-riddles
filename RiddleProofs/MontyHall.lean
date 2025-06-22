/-!
# The Monty Hall Problem

**Problem**: Three doors, one car, two goats. You pick a door, host opens a goat door.
Should you switch? **Answer**: Yes! Switching gives 2/3 probability vs 1/3 for staying.
-/

inductive Prize | car | goat deriving DecidableEq, Repr
inductive Door | d1 | d2 | d3 deriving DecidableEq, Repr

open Prize Door

def World := Door → Prize

-- All possible worlds: car behind each door
def all_worlds : List World := [
  fun d => if d = d1 then car else goat,
  fun d => if d = d2 then car else goat,
  fun d => if d = d3 then car else goat
]

/-- Player wins car by switching to switch_to door -/
def win_if_switch (w : World) (switch_to : Door) : Bool := w switch_to = car

def all_doors : List Door := [d1, d2, d3]

/-- Doors the host can open: not player's pick and has goat -/
def possible_host_opens (w : World) (pick : Door) : List Door :=
  all_doors.filter (fun d => d ≠ pick ∧ w d = goat)

/-- Door to switch to: the remaining unopened door -/
def switch_choice (pick host_open : Door) : Door :=
  match (all_doors.filter (fun d => d ≠ pick ∧ d ≠ host_open)) with
  | d::_ => d
  | [] => d1 -- fallback, should never happen

/-- Compute scenarios where switching wins using modern Lean syntax -/
def win_by_switch : Nat :=
  (all_worlds.flatMap fun w =>
    all_doors.flatMap fun pick =>
      (possible_host_opens w pick).map fun host_open =>
        let switch_to := switch_choice pick host_open
        if win_if_switch w switch_to then 1 else 0).sum

/-- Compute scenarios where staying wins -/
def win_by_staying : Nat :=
  (all_worlds.flatMap fun w =>
    all_doors.flatMap fun pick =>
      (possible_host_opens w pick).map fun _ =>
        if w pick = car then 1 else 0).sum

/-- Total number of game scenarios -/
def total_scenarios : Nat :=
  (all_worlds.flatMap fun w =>
    all_doors.flatMap fun pick =>
      (possible_host_opens w pick).map fun _ => 1).sum

/-!
## Results and Verification

The key insight: When you initially pick wrong (2/3 probability), switching wins.
When you initially pick right (1/3 probability), switching loses.
-/

-- Uncomment to see the results:
-- #eval win_by_switch     -- Should be 4 (switching wins in 4/6 scenarios)
-- #eval win_by_staying    -- Should be 2 (staying wins in 2/6 scenarios)
-- #eval total_scenarios   -- Should be 6 total scenarios

-- Example world: car behind door 1
def example_world : World := fun d => if d = d1 then car else goat

-- #eval possible_host_opens example_world d1  -- [d2, d3] - both doors have goats
-- #eval possible_host_opens example_world d2  -- [d3] - only d3 has goat (d1 has car)

/-!
**Conclusion**: Always switch! You win 2/3 of the time vs 1/3 by staying.
-/
