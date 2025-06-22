/-!
# The Monty Hall Problem

You are on a game show with three doors, one hiding a car, two hiding goats. After you pick, the host opens a goat door. Should you switch?
-/

inductive Prize | car | goat deriving DecidableEq, Repr
inductive Door | d1 | d2 | d3 deriving DecidableEq, Repr

open Prize Door

def World := Door → Prize

def all_worlds : List World :=
  [ fun d => if d = d1 then car else goat,
    fun d => if d = d2 then car else goat,
    fun d => if d = d3 then car else goat ]

/-- Simulate the game: player picks `pick`, host opens `host_open`, player switches to `switch_to`. Returns true if player wins car. -/
def win_if_switch (w : World) (_pick _host_open switch_to : Door) : Bool :=
  w switch_to = car

/-- For each world, for each initial pick, for each possible host open, check if switching wins. -/
def all_doors : List Door := [d1, d2, d3]

def possible_host_opens (w : World) (pick : Door) : List Door :=
  all_doors.filter (fun d => d ≠ pick ∧ w d = goat)

def switch_choice (pick host_open : Door) : Door :=
  let remaining := all_doors.filter (fun d => d ≠ pick ∧ d ≠ host_open)
  match remaining with
  | d::_ => d
  | [] => d1 -- fallback, should never happen

def flatten {α} : List (List α) → List α
| [] => []
| (x :: xs) => x ++ flatten xs

/-- Compute the probability of winning by switching. -/
def win_by_switch : Nat :=
  flatten (all_worlds.map (fun w =>
    flatten (all_doors.map (fun pick =>
      (possible_host_opens w pick).map (fun host_open =>
        let switch_to := switch_choice pick host_open
        if win_if_switch w pick host_open switch_to then 1 else 0)))))
  |>.sum

/- Out of 6 possible scenarios, switching wins 6 - 2 = 4 times. -/
-- #eval win_by_switch -- Should print 6 (switching always wins except when initial pick is car)
