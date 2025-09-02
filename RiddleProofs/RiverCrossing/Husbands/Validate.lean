import RiddleProofs.RiverCrossing.Husbands.Notation

open RiverCrossing.Husbands



def opposite_bank : RiverBank → RiverBank
| .left => .right
| .right => .left

def update_person_state (p : Person) (new_bank : RiverBank)
    (s : JealousHusbandsState) : JealousHusbandsState :=
  match p with
  | .husband i => RiverCrossing.move_owner i new_bank s
  | .wife i => RiverCrossing.move_possession i new_bank s

/-- List of all people in the puzzle for iteration purposes. -/
def all_people : List Person := [
  Person.husband 0, Person.husband 1, Person.husband 2,
  Person.wife 0, Person.wife 1, Person.wife 2
]

/-- Update person's position only if they're part of the move. -/
def update_if_present (p : Person) (people : Finset Person) (new_bank : RiverBank)
    (s : JealousHusbandsState) : JealousHusbandsState :=
  if p ∈ people then update_person_state p new_bank s else s



/-- Check if a person is on the same bank as the boat (boarding requirement). -/
def person_on_boat_side (p : Person) (people : Finset Person) (s : JealousHusbandsState) : Bool :=
  if p ∈ people then Person.bank p s == s.boat_bank else true



/--
Apply a move to a state, producing the new state after the move.
1. The boat travels to the opposite bank
2. All people in the move travel with the boat to the new bank
3. People not in the move stay where they are -/
def apply_simple_move (m : Move) (s : JealousHusbandsState) : JealousHusbandsState :=
  let new_boat := opposite_bank s.boat_bank
  let base_state := RiverCrossing.move_boat new_boat s
  let people := m.people_in_boat
  all_people.foldl (fun acc_state p => update_if_present p people new_boat acc_state)
    base_state


/--

Validate whether a move is legal in the current state:
1. **Boarding rule**: All people in the move must be on the same bank as the boat
2. **Travel rule**: If 2 people travel together, they must be either:
  - A married couple (same couple_id), OR
  - Two people of the same gender (two husbands or two wives)
-/
def simple_move_valid (m : Move) (s : JealousHusbandsState) : Bool :=
  let people := m.people_in_boat
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
    | [] => s == final_state
    | m :: rest =>
      if simple_move_valid m s then
        let new_state := apply_simple_move m s
        if wife_safe new_state then
          check_moves new_state rest
        else false
      else false
  check_moves initial_state moves
