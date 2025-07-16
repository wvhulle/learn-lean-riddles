import Mathlib.Data.Fintype.Card

/-!
# The Blue-Eyed Islanders Puzzle

## Problem

On a remote island live 200 people, some with blue eyes and some with brown eyes. (There are exactly 100 blue-eyed and 100 brown-eyed islanders for simplicity.) Everyone can see everyone else's eye color, but not their own. They are perfect logicians.

A visiting stranger announces: "At least one of you has blue eyes."

The rules are:
- If someone can deduce their own eye color, they must leave the island that night
- No communication is allowed between islanders
- Everyone acts simultaneously based on perfect logical reasoning

## Question

What happens?

-/

inductive EyeColor where
  | blue : EyeColor
  | brown : EyeColor
  | green : EyeColor  -- included for completeness, but not used in our specific problem
  deriving DecidableEq

instance : Fintype EyeColor where
  elems := {EyeColor.blue, EyeColor.brown, EyeColor.green}
  complete := by intro x; cases x <;> simp

def numIslanders : ℕ := 200

abbrev Islander := Fin numIslanders

-- First 100 islanders (indices 0-99) have blue eyes
-- Last 100 islanders (indices 100-199) have brown eyes
def islanderEyeColors : Islander → EyeColor :=
  fun i => if i.val < 100 then EyeColor.blue else EyeColor.brown

instance : DecidablePred (fun i : Islander => islanderEyeColors i = EyeColor.blue) :=
  fun i => by unfold islanderEyeColors; infer_instance

/-- Models what an islander can deduce about their own eye color based on:
    - The observed eye colors of others
    - The fact that someone would leave if they knew they had blue eyes
    - Common knowledge accumulated over days

    **The deduction logic**: On day N, a blue-eyed islander who observes (N-1) other
    blue-eyed people can reason: "If there were only (N-1) blue-eyed people total,
    they would have all left by now. Since they haven't, there must be at least N.
    Since I see exactly (N-1), I must be the Nth one!"

    **Implementation**: An islander can deduce their eye color on day D if and only if:
    1. They actually have blue eyes, AND
    2. D equals the total number of blue-eyed people on the island -/
def can_deduce_own_eye_color (i : Islander) (day : ℕ) : Prop :=
  let blue_eyed_islanders := (Finset.univ.filter (fun j => islanderEyeColors j = EyeColor.blue))
  let num_blue_eyed := blue_eyed_islanders.card
  (islanderEyeColors i = EyeColor.blue) ∧ (day = num_blue_eyed)

def leaves_on_night (i : Islander) (night : ℕ) : Prop :=
  can_deduce_own_eye_color i night

def count_blue_eyed : ℕ :=
  (Finset.univ.filter (fun i : Islander => islanderEyeColors i = EyeColor.blue)).card
