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

-- Move as a finite set of people with direction (at most 2, at least 1)
structure Move where
  people : Finset Person
  direction : Direction
  valid_size : people.card ≤ 2 ∧ people.card > 0
deriving DecidableEq


namespace Move

-- Constructor helpers for creating moves
def single (p : Person) (dir : Direction) : Move :=
  ⟨{p}, dir, by simp [Finset.card_singleton]⟩

def pair (p1 p2 : Person) (dir : Direction) (h : p1 ≠ p2) : Move :=
  ⟨{p1, p2}, dir, by
    constructor
    · simp [Finset.card_pair h]
    · simp [Finset.card_pair h]⟩

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
    -- Valid pairs: married couples or same-gender pairs
    -- Check if it's a couple (same couple_id) or same gender
    all_people.any (fun p1 =>
      all_people.any (fun p2 =>
        p1 ≠ p2 && people = {p1, p2} &&
        (p1.couple_id = p2.couple_id || (p1.is_husband && p2.is_husband) || (p1.is_wife && p2.is_wife))))
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

  -- Single moves - using clean notation
  let single_moves :=
    couples.flatMap fun i =>
      if direction == Direction.toRight then
        [R {Person.husband i}, R {Person.wife i}]
      else
        [L {Person.husband i}, L {Person.wife i}]

  -- Pair moves - using clean notation with explicit proofs
  let pair_moves :=
    couples.flatMap fun i =>
      couples.flatMap fun j =>
        if h : i.val < j.val then
          let ne_proof : i ≠ j := Fin.ne_of_lt h
          if direction == Direction.toRight then
            [Move.pair (Person.husband i) (Person.husband j) Direction.toRight (by simp [ne_proof]),
             Move.pair (Person.wife i) (Person.wife j) Direction.toRight (by simp [ne_proof])]
          else
            [Move.pair (Person.husband i) (Person.husband j) Direction.toLeft (by simp [ne_proof]),
             Move.pair (Person.wife i) (Person.wife j) Direction.toLeft (by simp [ne_proof])]
        else []

  -- Couple moves - using clean notation
  let couple_moves :=
    couples.map fun i =>
      if direction == Direction.toRight then
        R {Person.husband i, Person.wife i}
      else
        L {Person.husband i, Person.wife i}

  -- Filter using modern syntax and better composition
  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)
