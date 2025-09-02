import Mathlib.Data.Vector.Basic

/-!
# Basic types and safety framework for river crossing puzzles

This module provides shared types, constants, and safety constraint framework used across
different river crossing puzzles like the jealous husbands problem and the jealous
mathematicians problem.
-/

/-- Two sides of the river -/
inductive RiverBank
| left
| right
deriving DecidableEq, Repr, Inhabited, BEq

/-- Generic river crossing state with two types of entities -/
structure RiverCrossingState (α β : Type) (n : Nat) where
  boat_bank : RiverBank
  owner_bank : Vector RiverBank n
  possession_bank : Vector RiverBank n
deriving DecidableEq, Repr


/-- Generic OfNat instance creator for Fin types -/
def mkFinOfNat (n : Nat) (h : 0 < n) : OfNat (Fin n) k :=
  ⟨⟨k % n, Nat.mod_lt k h⟩⟩

/-- Create initial state with all entities on the left bank -/
abbrev initial_state {α β : Type} {n : Nat} : RiverCrossingState α β n :=
  { boat_bank := RiverBank.left,
    owner_bank := Vector.replicate n RiverBank.left,
    possession_bank := Vector.replicate n RiverBank.left }

/-- Create final state with all entities on the right bank -/
abbrev final_state {α β : Type} {n : Nat} : RiverCrossingState α β n :=
  { boat_bank := RiverBank.right,
    owner_bank := Vector.replicate n RiverBank.right,
    possession_bank := Vector.replicate n RiverBank.right }

/-- Abstract safety constraint for river crossing puzzles -/
class SafetyConstraint (α β : Type) (n : Nat) where
  /-- Check if a state satisfies the safety constraint -/
  is_safe : RiverCrossingState α β n → Bool

  /-- Instance showing the boolean function is decidable -/
  is_safe_decidable : DecidablePred (fun s => is_safe s = true)



/-
## Decidability

Whether a property is decidable depends on how it is defined. If it is built from decidable operations and quantifies only over finite/enumerable types, Lean can often infer it (with infer_instance), but it cannot always do so automatically without being told to try.
 -/

namespace RiverCrossing

/-- Generic state manipulation functions -/
def move_owner (i : Fin n) (bank : RiverBank) (s : RiverCrossingState α β n) :
  RiverCrossingState α β n :=
  { s with owner_bank := s.owner_bank.set i bank }

def move_possession (i : Fin n) (bank : RiverBank) (s : RiverCrossingState α β n) :
  RiverCrossingState α β n :=
  { s with possession_bank := s.possession_bank.set i bank }

def move_boat (bank : RiverBank) (s : RiverCrossingState α β n) :
  RiverCrossingState α β n :=
  { s with boat_bank := bank }

end RiverCrossing
