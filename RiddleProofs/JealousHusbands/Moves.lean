import RiddleProofs.JealousHusbands.Statement
import Mathlib.Data.Finset.Card

inductive Direction
| toRight
| toLeft
deriving DecidableEq, Repr

structure Move where
  people : Finset Person
  direction : Direction
  valid_size : people.card ≤ 2 ∧ people.card > 0
deriving DecidableEq



def single (p : Person) (dir : Direction) : Move :=
  ⟨{p}, dir, by simp [Finset.card_singleton]⟩

def pair (p1 p2 : Person) (dir : Direction) (h : p1 ≠ p2) : Move :=
  ⟨{p1, p2}, dir, by
    constructor
    · simp [Finset.card_pair h]
    · simp [Finset.card_pair h]⟩


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

def opposite_bank : RiverBank → RiverBank
| .left => .right
| .right => .left

def update_person_state (p : Person) (new_bank : RiverBank) (s : State) : State :=
  match p with
  | .husband i => {s with husbands := s.husbands.set i new_bank}
  | .wife i => {s with wives := s.wives.set i new_bank}

def all_people : List Person := [
  Person.husband ⟨0, by decide⟩, Person.husband ⟨1, by decide⟩, Person.husband ⟨2, by decide⟩,
  Person.wife ⟨0, by decide⟩, Person.wife ⟨1, by decide⟩, Person.wife ⟨2, by decide⟩
]

def update_if_present (p : Person) (people : Finset Person) (new_bank : RiverBank) (s : State) : State :=
  if p ∈ people then update_person_state p new_bank s else s

def apply_simple_move (m : Move) (s : State) : State :=
  let new_boat := opposite_bank s.boat
  let base_state := {s with boat := new_boat}
  let people := m.people
  all_people.foldl (fun acc_state p => update_if_present p people new_boat acc_state) base_state

def person_on_boat_side (p : Person) (people : Finset Person) (s : State) : Bool :=
  if p ∈ people then Person.bank p s == s.boat else true

def simple_move_valid (m : Move) (s : State) : Bool :=
  let people := m.people
  let all_on_boat := all_people.all (person_on_boat_side · people s)
  let pair_valid := if people.card = 2 then
    all_people.any (fun p1 =>
      all_people.any (fun p2 =>
        p1 ≠ p2 && people = {p1, p2} &&
        (p1.couple_id = p2.couple_id ||
         (match p1, p2 with | .husband _, .husband _ => true | .wife _, .wife _ => true | _, _ => false))))
  else true
  all_on_boat && pair_valid



def validate_solution (moves : List Move) : Bool :=
  let rec check_moves (s : State) (ms : List Move) : Bool :=
    match ms with
    | [] => s == final_state
    | m :: rest =>
      if simple_move_valid m s then
        let new_state := apply_simple_move m s
        if state_safe new_state then
          check_moves new_state rest
        else false
      else false
  check_moves initial_state moves

def generate_valid_moves (s : State) : List Move :=
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
