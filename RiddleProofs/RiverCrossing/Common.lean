import Mathlib.Data.Vector.Basic

/-!
# Common types and constants for river crossing puzzles

This module provides shared types and constants used across different river crossing puzzles
like the jealous husbands problem and the jealous mathematicians problem.
-/

/-- Two sides of the river -/
inductive RiverBank
| left
| right
deriving DecidableEq, Repr, Inhabited, BEq

/-- Generic river crossing state with two types of entities -/
structure RiverCrossingState (α β : Type) (n : Nat) where
  boat : RiverBank
  entities_a : Vector RiverBank n
  entities_b : Vector RiverBank n
deriving DecidableEq, Repr

/-- Number of transfers needed for the standard 3-couple solution -/
def n_transfers : Nat := 11

/-- Number of states in the solution path -/
def n_states : Nat := n_transfers + 1

/-- Helper to create OfNat instances for Fin types -/
def mkOfNatFin (n : Nat) (h : 0 < n) : OfNat (Fin n) k := 
  ⟨⟨k % n, Nat.mod_lt k h⟩⟩

/-- Create initial state with all entities on the left bank -/
def initial_state (α β : Type) (n : Nat) : RiverCrossingState α β n :=
  { boat := RiverBank.left, 
    entities_a := Vector.replicate n RiverBank.left, 
    entities_b := Vector.replicate n RiverBank.left }

/-- Create final state with all entities on the right bank -/
def final_state (α β : Type) (n : Nat) : RiverCrossingState α β n :=
  { boat := RiverBank.right, 
    entities_a := Vector.replicate n RiverBank.right, 
    entities_b := Vector.replicate n RiverBank.right }