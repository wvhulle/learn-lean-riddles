import Init.WF

/-!
# Jealous Husbands River Crossing Puzzle:

Three husbands (m1, m2, m3) and their respective wives (w1, w2, w3) must cross a river.
- The boat carries at most two people at a time.
- A man and a woman cannot be in the boat together unless they are married.
- A woman cannot remain on the same side of the river with a man unless her husband is also present.
- The boat must always return to the other side to pick up the remaining passengers.
- The goal is to ensure all six individuals and the boat reach the right bank.
-/

def num_couples: Nat := 3

inductive RiverBank
| left
| right
deriving DecidableEq, Repr, Inhabited

instance : ToString RiverBank where
  toString
  | RiverBank.left => "left"
  | RiverBank.right => "right"

open RiverBank

structure State where
  boat : RiverBank
  husbands : Vector RiverBank num_couples
  wives : Vector RiverBank num_couples
  deriving Repr, DecidableEq, Inhabited

-- Safety condition for boat: no unmarried man and woman together
def boat_safe (passengers : List (Fin num_couples × Bool)) : Prop :=
  passengers.length ≤ 2 ∧
  ∀ (i j : Fin num_couples), (i ≠ j) →
    ¬((i, false) ∈ passengers ∧ (j, true) ∈ passengers)
  -- (i, false) means husband i, (j, true) means wife j

-- Safety condition for banks: no woman with a man unless her husband is present
def bank_safe (s : State) : Bool :=
  (List.range num_couples).all fun i =>
    (List.range num_couples).all fun j =>
      if i = j then true
      else
        -- For each bank, check the safety condition
        (List.map (fun bank : RiverBank =>
          -- If wife i and husband j are on this bank, then husband i must also be there
          !(s.wives[i]! = bank && s.husbands[j]! = bank && s.husbands[i]! ≠ bank)
        ) [left, right]).all id

-- Combined safety condition (now returns Bool for decidability)
def state_safe (s : State) : Bool := bank_safe s

-- Convert Bool to Prop for theorem statements
def state_safe_prop (s : State) : Prop := state_safe s = true

instance : DecidablePred state_safe_prop := by
  unfold state_safe_prop
  infer_instance

-- Initial state: everyone on the left bank
def initial_state : State :=
  { boat := left, husbands := Vector.replicate 3 left, wives := Vector.replicate 3 left }

-- Goal state: everyone on the right bank
def final_state : State :=
  { boat := right, husbands := Vector.replicate 3 right, wives := Vector.replicate 3 right }

theorem final_safe: state_safe final_state = true := by
  unfold state_safe bank_safe final_state
  simp [List.all]
  decide

-- Helper functions for moving people
def move_husband (n : Fin num_couples) (b : RiverBank) (s : State) : State :=
{ s with husbands := s.husbands.set n b }

def move_wife (n : Fin num_couples) (b : RiverBank) (s : State) : State :=
{ s with wives := s.wives.set n b }

def move_boat (b : RiverBank) (s : State) : State :=
{ s with boat := b }

instance : OfNat (Fin num_couples) n where
  ofNat := ⟨n % num_couples, Nat.mod_lt n (by decide)⟩

-- Number of transfers and states for the solution
def n_transfers : Nat := 11
def n_states := n_transfers + 1
