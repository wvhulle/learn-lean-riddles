import RiddleProofs.RiverCrossing.Husbands.Statement
import RiddleProofs.RiverCrossing.Safety
import Mathlib.Data.Finset.Card

open RiverCrossing.Husbands

/-- SafetyConstraint instance for JealousHusbandsState -/
instance : SafetyConstraint Person Person num_couples where
  is_safe := bank_safe
  is_safe_prop := state_safe_prop
  is_safe_decidable := by infer_instance
  is_safe_coherent := by simp [state_safe_prop]


/-- Direction the boat travels. The boat must shuttle back and forth. -/
inductive Direction
| toRight  -- From left bank to right bank
| toLeft   -- From right bank to left bank
deriving DecidableEq, Repr


structure Move where
  /-- A move consists of 1-2 people traveling in a specific direction. -/
  people : Finset Person
  direction : Direction
  /-- Constraint ensures:
    - At least 1 person (boat can't travel empty)
    - At most 2 people (boat capacity limit)-/
  valid_size : people.card ≤ 2 ∧ people.card > 0
deriving DecidableEq



/-- Create a move with a single person traveling in the given direction. -/
def single (p : Person) (dir : Direction) : Move :=
  ⟨{p}, dir, by simp [Finset.card_singleton]⟩

/-- Create a move with two people traveling together in the given direction.
    Requires proof that the two people are different. -/
def pair (p1 p2 : Person) (dir : Direction) (h : p1 ≠ p2) : Move :=
  ⟨{p1, p2}, dir, by
    constructor
    · simp [Finset.card_pair h]
    · simp [Finset.card_pair h]⟩


/-- Custom syntax for readable move notation.

    Examples:
    - `R {H 0}`: Husband 0 moves right (alone)
    - `L {W 1}`: Wife 1 moves left (alone)
    - `R {H 0, W 0}`: Couple 0 moves right (together)
    - `L {H 1, H 2}`: Husbands 1 and 2 move left (together) -/
syntax:50 "R" "{" term "}" : term
syntax:50 "L" "{" term "}" : term
syntax:50 "R" "{" term "," term "}" : term
syntax:50 "L" "{" term "," term "}" : term

macro_rules
  | `(R {$p}) => `(single $p Direction.toRight)
  | `(L {$p}) => `(single $p Direction.toLeft)
  | `(R {$p1, $p2}) => `(pair $p1 $p2 Direction.toRight (by simp))
  | `(L {$p1, $p2}) => `(pair $p1 $p2 Direction.toLeft (by simp))



@[app_unexpander single]
def unexpandSingle : Lean.PrettyPrinter.Unexpander
  | `($_ $p Direction.toRight) =>
      `(R {$p})
  | `($_ $p Direction.toLeft) => `(L {$p})
  | _ => throw ()

@[app_unexpander pair]
def unexpandPair : Lean.PrettyPrinter.Unexpander
  | `($_ $p1 $p2 Direction.toRight $_) => `(R {$p1, $p2})
  | `($_ $p1 $p2 Direction.toLeft $_) => `(L {$p1, $p2})
  | _ => throw ()

-- Output render check
-- #check single (Person.husband ⟨0, by decide⟩) Direction.toLeft
-- #check L {H 0}

instance : Inhabited Move := ⟨single (Person.husband ⟨0, by decide⟩) Direction.toRight⟩

/-- Get the opposite bank from the current one. -/
def opposite_bank : RiverBank → RiverBank
| .left => .right
| .right => .left

/-- Update a single person's position in the state using Safety.lean tools. -/
def update_person_state (p : Person) (new_bank : RiverBank)
    (s : JealousHusbandsState) : JealousHusbandsState :=
  match p with
  | .husband i => move_entity_a i new_bank s
  | .wife i => move_entity_b i new_bank s

/-- List of all people in the puzzle for iteration purposes. -/
def all_people : List Person := [
  Person.husband ⟨0, by decide⟩, Person.husband ⟨1, by decide⟩,
  Person.husband ⟨2, by decide⟩,
  Person.wife ⟨0, by decide⟩, Person.wife ⟨1, by decide⟩, Person.wife ⟨2, by decide⟩
]

/-- Update person's position only if they're part of the move. -/
def update_if_present (p : Person) (people : Finset Person) (new_bank : RiverBank)
    (s : JealousHusbandsState) : JealousHusbandsState :=
  if p ∈ people then update_person_state p new_bank s else s

/--
Apply a move to a state, producing the new state after the move.
1. The boat travels to the opposite bank
2. All people in the move travel with the boat to the new bank
3. People not in the move stay where they are -/
def apply_simple_move (m : Move) (s : JealousHusbandsState) : JealousHusbandsState :=
  let new_boat := opposite_bank s.boat
  let base_state := move_boat new_boat s
  let people := m.people
  all_people.foldl (fun acc_state p => update_if_present p people new_boat acc_state)
    base_state

/-- Check if a person is on the same bank as the boat (boarding requirement). -/
def person_on_boat_side (p : Person) (people : Finset Person) (s : JealousHusbandsState) : Bool :=
  if p ∈ people then Person.bank p s == s.boat else true

/--

Validate whether a move is legal in the current state:
1. **Boarding rule**: All people in the move must be on the same bank as the boat
2. **Travel rule**: If 2 people travel together, they must be either:
  - A married couple (same couple_id), OR
  - Two people of the same gender (two husbands or two wives)
-/
def simple_move_valid (m : Move) (s : JealousHusbandsState) : Bool :=
  let people := m.people
  let all_on_boat := all_people.all (person_on_boat_side · people s)
  let pair_valid := if people.card = 2 then
    all_people.any (fun p1 =>
      all_people.any (fun p2 =>
        p1 ≠ p2 && people = {p1, p2} &&
        (p1.couple_id = p2.couple_id ||
         (match p1, p2 with
         | .husband _, .husband _ => true
         | .wife _, .wife _ => true
         | _, _ => false))))
  else true
  all_on_boat && pair_valid



def validate_solution (moves : List Move) : Bool :=
  let rec check_moves (s : JealousHusbandsState) (ms : List Move) : Bool :=
    match ms with
    | [] => s == jealous_husbands_final_state
    | m :: rest =>
      if simple_move_valid m s then
        let new_state := apply_simple_move m s
        if bank_safe new_state then
          check_moves new_state rest
        else false
      else false
  check_moves jealous_husbands_initial_state moves

def generate_valid_moves (s : JealousHusbandsState) : List Move :=
  let couples : List (Fin num_couples) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]
  let direction := if s.boat == RiverBank.left then Direction.toRight else Direction.toLeft

  let single_moves :=
    couples.flatMap fun i =>
      if direction == Direction.toRight then
        [R {Person.husband i}, R {Person.wife i}]
      else
        [L {Person.husband i}, L {Person.wife i}]

  let pair_moves :=
    couples.flatMap fun i =>
      couples.flatMap fun j =>
        if h : i.val < j.val then
          let ne_proof : i ≠ j := Fin.ne_of_lt h
          if direction == Direction.toRight then
            [pair (Person.husband i) (Person.husband j) Direction.toRight (by simp [ne_proof]),
             pair (Person.wife i) (Person.wife j) Direction.toRight (by simp [ne_proof])]
          else
            [pair (Person.husband i) (Person.husband j) Direction.toLeft (by simp [ne_proof]),
             pair (Person.wife i) (Person.wife j) Direction.toLeft (by simp [ne_proof])]
        else []

  let couple_moves :=
    couples.map fun i =>
      if direction == Direction.toRight then
        R {Person.husband i, Person.wife i}
      else
        L {Person.husband i, Person.wife i}

  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)

-- Test that the refactored functions work correctly
example : update_person_state (H 0) RiverBank.right jealous_husbands_initial_state =
  move_entity_a ⟨0, by decide⟩ RiverBank.right jealous_husbands_initial_state := by
  rfl

example : apply_simple_move (R {H 0}) jealous_husbands_initial_state =
  move_boat RiverBank.right (move_entity_a ⟨0, by decide⟩ RiverBank.right jealous_husbands_initial_state) := by
  rfl
