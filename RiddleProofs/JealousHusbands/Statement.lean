import Init.WF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Jealous Husbands River Crossing Puzzle:

Three husbands (m1, m2, m3) and their respective wives (w1, w2, w3) must cross a river.
- The boat carries at most two people at a time.
- A man and a woman cannot be in the boat together unless they are married.
- A woman cannot remain on the same side of the river with a man unless her husband is present.
- The boat must always return to the other side to pick up the remaining passengers.
- The goal is to ensure all six individuals and the boat reach the right bank.
-/

def num_couples: Nat := 3

inductive RiverBank
| left
| right
deriving DecidableEq, Repr, Inhabited, BEq

instance : ToString RiverBank where
  toString
  | .left => "left"
  | .right => "right"

open RiverBank

-- Unified person type combining husbands and wives
inductive Person
| husband (i : Fin num_couples)
| wife (i : Fin num_couples)
deriving DecidableEq, Repr

instance : ToString Person where
  toString p := match p with
  | .husband i => s!"H{i.val}"
  | .wife i => s!"W{i.val}"

-- Convenient notation for people (available throughout the module)
notation "H" n => Person.husband ⟨n, by decide⟩
notation "W" n => Person.wife ⟨n, by decide⟩

-- Forward declarations for Direction type (will be defined in Moves)
-- Notation for directions and moves (will use Move type from Moves module)
-- These will be available after importing Moves

-- Helper functions for person operations
def Person.couple_id : Person → Fin num_couples
| .husband i => i
| .wife i => i

def Person.is_husband : Person → Bool
| .husband _ => true
| .wife _ => false

def Person.is_wife : Person → Bool
| .husband _ => false
| .wife _ => true

structure State where
  boat : RiverBank
  husbands : Vector RiverBank num_couples
  wives : Vector RiverBank num_couples
deriving DecidableEq

instance : BEq State where
  beq s1 s2 := s1.boat == s2.boat &&
               s1.husbands.toList == s2.husbands.toList &&
               s1.wives.toList == s2.wives.toList

def Person.bank (p : Person) (s : State) : RiverBank :=
match p with
| .husband i => s.husbands.get i
| .wife i => s.wives.get i

-- These functions are no longer used in the new person-based approach

-- Safety condition for banks: no woman with a man unless her husband is present
-- Using idiomatic Array operations for better performance
def bank_safe (s : State) : Bool :=
  let couples := #[0, 1, 2]  -- Using proper OfNat instance now
  let banks := #[RiverBank.left, RiverBank.right]

  couples.all fun i =>
    couples.all fun j =>
      if i = j then true
      else
        banks.all fun bank =>
          -- If wife i and husband j are on this bank, then husband i must also be there
          !(s.wives[i]! = bank && s.husbands[j]! = bank && s.husbands[i]! ≠ bank)

-- Combined safety condition
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
  native_decide

-- To be able to use numerals like 0, 1, 2 for creating terms of type `Fin num_couples`,
-- we need to implement an OfNat instance
instance : OfNat (Fin num_couples) n where
  ofNat := ⟨n % num_couples, Nat.mod_lt n (by decide)⟩

-- Number of transfers and states for the solution
def n_transfers : Nat := 11
def n_states := n_transfers + 1
