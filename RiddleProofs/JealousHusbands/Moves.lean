import RiddleProofs.JealousHusbands.Statement
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Lean.ToExpr

/-!
# Move Definitions for the Jealous Husbands Problem

This file defines moves using a directional approach where moves are represented
as finite sets of people crossing the river with explicit direction information.
-/

-- Direction of movement
inductive Direction
| toRight  -- Moving from left to right
| toLeft   -- Moving from right to left
deriving DecidableEq, Repr

instance : ToString Direction where
  toString
  | .toRight => "R"
  | .toLeft => "L"

-- Move as a finite set of people with direction (at most 2, at least 1)
structure Move where
  people : Finset Person
  direction : Direction
  valid_size : people.card ≤ 2 ∧ people.card > 0
deriving DecidableEq

-- Clean display function that shows moves in our notation format
def display_move (m : Move) : String :=
  let people := m.people
  let people_str :=
    if Person.husband ⟨0, by decide⟩ ∈ people ∧ people.card = 1 then "H 0"
    else if Person.husband ⟨1, by decide⟩ ∈ people ∧ people.card = 1 then "H 1"
    else if Person.husband ⟨2, by decide⟩ ∈ people ∧ people.card = 1 then "H 2"
    else if Person.wife ⟨0, by decide⟩ ∈ people ∧ people.card = 1 then "W 0"
    else if Person.wife ⟨1, by decide⟩ ∈ people ∧ people.card = 1 then "W 1"
    else if Person.wife ⟨2, by decide⟩ ∈ people ∧ people.card = 1 then "W 2"
    else if people = {Person.husband ⟨0, by decide⟩, Person.wife ⟨0, by decide⟩} then "H 0, W 0"
    else if people = {Person.husband ⟨1, by decide⟩, Person.wife ⟨1, by decide⟩} then "H 1, W 1"
    else if people = {Person.husband ⟨2, by decide⟩, Person.wife ⟨2, by decide⟩} then "H 2, W 2"
    else if people = {Person.husband ⟨0, by decide⟩, Person.husband ⟨1, by decide⟩} then "H 0, H 1"
    else if people = {Person.husband ⟨0, by decide⟩, Person.husband ⟨2, by decide⟩} then "H 0, H 2"
    else if people = {Person.husband ⟨1, by decide⟩, Person.husband ⟨2, by decide⟩} then "H 1, H 2"
    else if people = {Person.wife ⟨0, by decide⟩, Person.wife ⟨1, by decide⟩} then "W 0, W 1"
    else if people = {Person.wife ⟨0, by decide⟩, Person.wife ⟨2, by decide⟩} then "W 0, W 2"
    else if people = {Person.wife ⟨1, by decide⟩, Person.wife ⟨2, by decide⟩} then "W 1, W 2"
    else "?"
  (toString m.direction) ++ " {" ++ people_str ++ "}"

-- Display function for lists of moves
def display_moves (moves : List Move) : List String :=
  moves.map display_move


namespace Move

-- Constructor helpers for creating moves
def single (p : Person) (dir : Direction) : Move :=
  ⟨{p}, dir, by simp [Finset.card_singleton]⟩

def pair (p1 p2 : Person) (dir : Direction) (h : p1 ≠ p2) : Move :=
  ⟨{p1, p2}, dir, by
    constructor
    · simp [Finset.card_pair h]
    · simp [Finset.card_pair h]⟩

-- Convenience constructors for the original move types with direction
def single_husband (i : Fin num_couples) (dir : Direction) : Move :=
  single (Person.husband i) dir

def single_wife (i : Fin num_couples) (dir : Direction) : Move :=
  single (Person.wife i) dir

def two_husbands (i j : Fin num_couples) (dir : Direction) (h : i ≠ j) : Move :=
  pair (Person.husband i) (Person.husband j) dir (by simp [h])

def two_wives (i j : Fin num_couples) (dir : Direction) (h : i ≠ j) : Move :=
  pair (Person.wife i) (Person.wife j) dir (by simp [h])

def married_couple (i : Fin num_couples) (dir : Direction) : Move :=
  pair (Person.husband i) (Person.wife i) dir (by simp)

end Move

-- Notation for creating moves with nice syntax
-- Single person notation: R {W0} or L {H1}
syntax:50 "R" "{" term "}" : term
syntax:50 "L" "{" term "}" : term

-- Two person notation: R {W0, W1} or L {H1, W1}
syntax:50 "R" "{" term "," term "}" : term
syntax:50 "L" "{" term "," term "}" : term

-- Macro implementations
macro_rules
  | `(R {$p}) => `(Move.single $p Direction.toRight)
  | `(L {$p}) => `(Move.single $p Direction.toLeft)
  | `(R {$p1, $p2}) => `(Move.pair $p1 $p2 Direction.toRight (by simp))
  | `(L {$p1, $p2}) => `(Move.pair $p1 $p2 Direction.toLeft (by simp))

instance : Inhabited Move := ⟨Move.single (Person.husband ⟨0, by decide⟩) Direction.toRight⟩

def opposite_bank : RiverBank → RiverBank
| .left => .right
| .right => .left

-- Helper function to update state based on person
def update_person_state (p : Person) (new_bank : RiverBank) (s : State) : State :=
  match p with
  | .husband i => {s with husbands := s.husbands.set i new_bank}
  | .wife i => {s with wives := s.wives.set i new_bank}

-- Constants for optimization
def all_people : List Person := [
  Person.husband ⟨0, by decide⟩, Person.husband ⟨1, by decide⟩, Person.husband ⟨2, by decide⟩,
  Person.wife ⟨0, by decide⟩, Person.wife ⟨1, by decide⟩, Person.wife ⟨2, by decide⟩
]

-- Helper function to check if person is in move and apply state update
def update_if_present (p : Person) (people : Finset Person) (new_bank : RiverBank) (s : State) : State :=
  if p ∈ people then update_person_state p new_bank s else s

-- Apply a move to a state - using helper function to reduce duplication
def apply_simple_move (m : Move) (s : State) : State :=
  let new_boat := opposite_bank s.boat
  let base_state := {s with boat := new_boat}
  let people := m.people

  -- Apply updates for all people that are present in the move
  all_people.foldl (fun acc_state p => update_if_present p people new_boat acc_state) base_state

-- Helper function to check if person is on correct side
def person_on_boat_side (p : Person) (people : Finset Person) (s : State) : Bool :=
  if p ∈ people then Person.bank p s == s.boat else true

-- Check if a move is valid - using helper functions to reduce duplication
def simple_move_valid (m : Move) (s : State) : Bool :=
  let people := m.people

  -- Check all people are on boat's current side
  let all_on_boat := all_people.all (person_on_boat_side · people s)

  -- For exactly 2 people, check if it's a valid pairing
  let pair_valid := if people.card = 2 then
    -- Check all valid 2-person combinations using explicit sets
    let valid_pairs := [
      {Person.husband ⟨0, by decide⟩, Person.wife ⟨0, by decide⟩},      -- couple 0
      {Person.husband ⟨1, by decide⟩, Person.wife ⟨1, by decide⟩},      -- couple 1
      {Person.husband ⟨2, by decide⟩, Person.wife ⟨2, by decide⟩},      -- couple 2
      {Person.husband ⟨0, by decide⟩, Person.husband ⟨1, by decide⟩},   -- husbands 0,1
      {Person.husband ⟨0, by decide⟩, Person.husband ⟨2, by decide⟩},   -- husbands 0,2
      {Person.husband ⟨1, by decide⟩, Person.husband ⟨2, by decide⟩},   -- husbands 1,2
      {Person.wife ⟨0, by decide⟩, Person.wife ⟨1, by decide⟩},         -- wives 0,1
      {Person.wife ⟨0, by decide⟩, Person.wife ⟨2, by decide⟩},         -- wives 0,2
      {Person.wife ⟨1, by decide⟩, Person.wife ⟨2, by decide⟩}          -- wives 1,2
    ]
    valid_pairs.any (· = people)
  else true

  all_on_boat && pair_valid

-- Validate a solution by checking all states are safe and reach final state
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

-- Modern approach: Generate all valid simple moves using more idiomatic patterns
def generate_valid_moves (s : State) : List Move :=
  -- Use explicit Fin construction for type safety
  let couples : List (Fin num_couples) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

  -- Determine direction based on boat position
  let direction := if s.boat == RiverBank.left then Direction.toRight else Direction.toLeft

  -- Single moves - using List.flatMap with modern lambda syntax
  let single_moves :=
    couples.flatMap fun i =>
      [Move.single_husband i direction, Move.single_wife i direction]

  -- Pair moves - using more efficient nested iteration with simplified proofs
  let pair_moves :=
    couples.flatMap fun i =>
      couples.flatMap fun j =>
        if h : i.val < j.val then  -- More explicit comparison
          [Move.two_husbands i j direction (Fin.ne_of_lt h),
           Move.two_wives i j direction (Fin.ne_of_lt h)]
        else []

  -- Couple moves - direct mapping with modern syntax
  let couple_moves := couples.map (Move.married_couple · direction)

  -- Filter using modern syntax and better composition
  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)
