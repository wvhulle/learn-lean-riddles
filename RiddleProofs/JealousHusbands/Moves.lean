import RiddleProofs.JealousHusbands.Statement

/-!
# Move Definitions for the Jealous Husbands Problem

This file defines the different types of moves that can be made in the jealous husbands problem,
along with functions to validate and apply these moves.
-/

-- Represent a move as the people who cross the river
inductive Move
| single_husband (i : Fin num_couples)
| single_wife (i : Fin num_couples)
| two_husbands (i j : Fin num_couples)
| two_wives (i j : Fin num_couples)
| married_couple (i : Fin num_couples)
deriving DecidableEq, Repr

instance : Inhabited Move := ⟨Move.single_husband 0⟩

def opposite_bank : RiverBank → RiverBank
| RiverBank.left => RiverBank.right
| RiverBank.right => RiverBank.left

-- Apply a move to a state
def apply_simple_move (sm : Move) (s : State) : State :=
  let new_boat := opposite_bank s.boat
  match sm with
  | Move.single_husband i =>
    { s with boat := new_boat, husbands := s.husbands.set i new_boat }
  | Move.single_wife i =>
    { s with boat := new_boat, wives := s.wives.set i new_boat }
  | Move.two_husbands i j =>
    { s with boat := new_boat,
             husbands := s.husbands.set i new_boat |>.set j new_boat }
  | Move.two_wives i j =>
    { s with boat := new_boat,
             wives := s.wives.set i new_boat |>.set j new_boat }
  | Move.married_couple i =>
    { s with boat := new_boat,
             husbands := s.husbands.set i new_boat,
             wives := s.wives.set i new_boat }

-- Check if a move is valid (people are on the boat's current side)
def simple_move_valid (sm : Move) (s : State) : Bool :=
  match sm with
  | Move.single_husband i => s.husbands[i]! = s.boat
  | Move.single_wife i => s.wives[i]! = s.boat
  | Move.two_husbands i j =>
    i ≠ j && s.husbands[i]! = s.boat && s.husbands[j]! = s.boat
  | Move.two_wives i j =>
    i ≠ j && s.wives[i]! = s.boat && s.wives[j]! = s.boat
  | Move.married_couple i =>
    s.husbands[i]! = s.boat && s.wives[i]! = s.boat

-- Validate a solution by checking all states are safe and reach final state
def validate_solution (moves : List Move) : Bool :=
  let rec check_moves (s : State) (ms : List Move) : Bool :=
    match ms with
    | [] => s = final_state
    | m :: rest =>
      if simple_move_valid m s then
        let new_state := apply_simple_move m s
        if state_safe new_state then
          check_moves new_state rest
        else false
      else false
  check_moves initial_state moves

-- Generate all valid simple moves from a state
def generate_valid_moves (s : State) : List Move :=
  let single_moves :=
    (List.range num_couples).flatMap (fun i =>
      let hi := ⟨i % num_couples, Nat.mod_lt i (by decide)⟩
      [Move.single_husband hi, Move.single_wife hi])

  let pair_moves :=
    (List.range num_couples).flatMap (fun i =>
      (List.range num_couples).flatMap (fun j =>
        if i < j then
          let hi := ⟨i % num_couples, Nat.mod_lt i (by decide)⟩
          let hj := ⟨j % num_couples, Nat.mod_lt j (by decide)⟩
          [Move.two_husbands hi hj, Move.two_wives hi hj]
        else []))

  let couple_moves :=
    (List.range num_couples).map (fun i =>
      Move.married_couple ⟨i % num_couples, Nat.mod_lt i (by decide)⟩)

  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)
