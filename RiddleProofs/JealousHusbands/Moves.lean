import RiddleProofs.JealousHusbands.Statement

/-!
# Move Definitions for the Jealous Husbands Problem

This file defines the different types of moves that can be made in the jealous husbands problem,
along with functions to validate and apply these moves.
-/

-- Represent a move as the people who cross the river
inductive Move
| husband (i : Fin num_couples)
| wife (i : Fin num_couples)
| husband_pair (i j : Fin num_couples)
| wife_pair (i j : Fin num_couples)
| couple (i : Fin num_couples)
| husband_wife (i j : Fin num_couples) -- husband i with wife j (only if i = j)
deriving DecidableEq, Repr

instance : Inhabited Move := ⟨Move.husband 0⟩

-- Simplified move representation for easier reasoning
inductive SimpleMove
| single_husband (i : Fin num_couples)
| single_wife (i : Fin num_couples)
| two_husbands (i j : Fin num_couples)
| two_wives (i j : Fin num_couples)
| married_couple (i : Fin num_couples)
deriving DecidableEq, Repr

instance : Inhabited SimpleMove := ⟨SimpleMove.single_husband 0⟩

def opposite_bank : RiverBank → RiverBank
| RiverBank.left => RiverBank.right
| RiverBank.right => RiverBank.left

-- Apply a move to a state
def apply_move (move : Move) (s : State) : State :=
  let new_boat := opposite_bank s.boat
  match move with
  | Move.husband i =>
    { s with boat := new_boat, husbands := s.husbands.set i new_boat }
  | Move.wife i =>
    { s with boat := new_boat, wives := s.wives.set i new_boat }
  | Move.husband_pair i j =>
    { s with boat := new_boat,
             husbands := s.husbands.set i new_boat |>.set j new_boat }
  | Move.wife_pair i j =>
    { s with boat := new_boat,
             wives := s.wives.set i new_boat |>.set j new_boat }
  | Move.couple i =>
    { s with boat := new_boat,
             husbands := s.husbands.set i new_boat,
             wives := s.wives.set i new_boat }
  | Move.husband_wife i j =>
    if i = j then
      { s with boat := new_boat,
               husbands := s.husbands.set i new_boat,
               wives := s.wives.set j new_boat }
    else s -- Invalid move

-- Check if a move is valid (people are on the boat's current side)
def move_valid (move : Move) (s : State) : Bool :=
  match move with
  | Move.husband i => s.husbands[i]! = s.boat
  | Move.wife i => s.wives[i]! = s.boat
  | Move.husband_pair i j =>
    i ≠ j && s.husbands[i]! = s.boat && s.husbands[j]! = s.boat
  | Move.wife_pair i j =>
    i ≠ j && s.wives[i]! = s.boat && s.wives[j]! = s.boat
  | Move.couple i =>
    s.husbands[i]! = s.boat && s.wives[i]! = s.boat
  | Move.husband_wife i j =>
    i = j && s.husbands[i]! = s.boat && s.wives[j]! = s.boat

-- Convert SimpleMove to Move type
def simple_to_move (sm : SimpleMove) : Move :=
  match sm with
  | SimpleMove.single_husband i => Move.husband i
  | SimpleMove.single_wife i => Move.wife i
  | SimpleMove.two_husbands i j => Move.husband_pair i j
  | SimpleMove.two_wives i j => Move.wife_pair i j
  | SimpleMove.married_couple i => Move.couple i

-- Check if a simple move is valid
def simple_move_valid (sm : SimpleMove) (s : State) : Bool :=
  match sm with
  | SimpleMove.single_husband i => s.husbands[i]! = s.boat
  | SimpleMove.single_wife i => s.wives[i]! = s.boat
  | SimpleMove.two_husbands i j =>
    i ≠ j && s.husbands[i]! = s.boat && s.husbands[j]! = s.boat
  | SimpleMove.two_wives i j =>
    i ≠ j && s.wives[i]! = s.boat && s.wives[j]! = s.boat
  | SimpleMove.married_couple i =>
    s.husbands[i]! = s.boat && s.wives[i]! = s.boat

-- Apply a simple move to get a new state
def apply_simple_move (sm : SimpleMove) (s : State) : State :=
  apply_move (simple_to_move sm) s

-- Generate all possible moves from a state
def possible_moves (s : State) : List Move :=
  let individuals :=
    (List.range num_couples).flatMap (fun i =>
      [Move.husband ⟨i % num_couples, Nat.mod_lt i (by decide)⟩,
       Move.wife ⟨i % num_couples, Nat.mod_lt i (by decide)⟩]) |>.filter (move_valid · s)
  let pairs :=
    (List.range num_couples).flatMap (fun i =>
      (List.range num_couples).flatMap (fun j =>
        if i < j then
          [Move.husband_pair ⟨i % num_couples, Nat.mod_lt i (by decide)⟩
                            ⟨j % num_couples, Nat.mod_lt j (by decide)⟩,
           Move.wife_pair ⟨i % num_couples, Nat.mod_lt i (by decide)⟩
                         ⟨j % num_couples, Nat.mod_lt j (by decide)⟩]
        else [])) |>.filter (move_valid · s)
  let couples :=
    (List.range num_couples).map (fun i =>
      Move.couple ⟨i % num_couples, Nat.mod_lt i (by decide)⟩) |>.filter (move_valid · s)
  individuals ++ pairs ++ couples

-- Generate all valid simple moves from a state
def generate_valid_moves (s : State) : List SimpleMove :=
  let single_moves :=
    (List.range num_couples).flatMap (fun i =>
      let hi := ⟨i % num_couples, Nat.mod_lt i (by decide)⟩
      [SimpleMove.single_husband hi, SimpleMove.single_wife hi])

  let pair_moves :=
    (List.range num_couples).flatMap (fun i =>
      (List.range num_couples).flatMap (fun j =>
        if i < j then
          let hi := ⟨i % num_couples, Nat.mod_lt i (by decide)⟩
          let hj := ⟨j % num_couples, Nat.mod_lt j (by decide)⟩
          [SimpleMove.two_husbands hi hj, SimpleMove.two_wives hi hj]
        else []))

  let couple_moves :=
    (List.range num_couples).map (fun i =>
      SimpleMove.married_couple ⟨i % num_couples, Nat.mod_lt i (by decide)⟩)

  (single_moves ++ pair_moves ++ couple_moves).filter (simple_move_valid · s)

-- Helper to convert a solution to a readable format
def format_solution (moves : List Move) : List String :=
  moves.map fun move => match move with
  | Move.husband i => s!"Husband {i.val} crosses"
  | Move.wife i => s!"Wife {i.val} crosses"
  | Move.husband_pair i j => s!"Husbands {i.val} and {j.val} cross"
  | Move.wife_pair i j => s!"Wives {i.val} and {j.val} cross"
  | Move.couple i => s!"Couple {i.val} crosses"
  | Move.husband_wife i j => s!"Husband {i.val} and Wife {j.val} cross"

-- Convert simple solution to readable format
def format_simple_solution (moves : List SimpleMove) : List String :=
  moves.map fun move => match move with
  | SimpleMove.single_husband i => s!"Husband {i.val} crosses"
  | SimpleMove.single_wife i => s!"Wife {i.val} crosses"
  | SimpleMove.two_husbands i j => s!"Husbands {i.val} and {j.val} cross"
  | SimpleMove.two_wives i j => s!"Wives {i.val} and {j.val} cross"
  | SimpleMove.married_couple i => s!"Couple {i.val} crosses"
