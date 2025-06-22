/-!
# The Monty Hall Problem

**Problem**: You're on a game show with three doors. Behind one door is a car, behind the other two are goats. You pick a door (say door 1). The host, who knows what's behind each door, opens another door (say door 3) revealing a goat. The host then asks: "Do you want to switch to door 2?"

**Question**: Should you switch doors to maximize your chance of winning the car?

**Intuition**: Many people think it doesn't matter (50/50 chance), but switching actually gives you a 2/3 probability of winning versus 1/3 for staying with your original choice.

**Key Insight**: When you first picked, you had a 1/3 chance of being right. The remaining 2/3 probability is concentrated on the other doors. When the host eliminates one losing door, that 2/3 probability transfers entirely to the remaining door.
-/

/-!
## Problem Formalization
-/

inductive Prize | car | goat deriving DecidableEq, Repr
inductive Door | d1 | d2 | d3 deriving DecidableEq, Repr

open Prize Door

def World := Door → Prize

/-- All possible doors -/
def all_doors : List Door := [d1, d2, d3]

/-- All possible worlds: car behind each door -/
def all_worlds : List World :=
  all_doors.map fun car_door =>
    fun d => if d = car_door then car else goat


/-!
### Solution

For each world and player choice, what happens with switching vs staying?
-/

/-- A strategic outcome represents the result of a game situation -/
structure StrategicOutcome where
  car_location : Door
  player_pick : Door
  switching_wins : Bool
  staying_wins : Bool
  deriving Repr

/-- Check if the player initially picked the correct door -/
def StrategicOutcome.picked_correctly (outcome : StrategicOutcome) : Bool :=
  outcome.car_location = outcome.player_pick

-- Generate all strategic outcomes (one per world/pick combination)
def strategic_outcomes : List StrategicOutcome :=
  all_worlds.flatMap fun w =>
    all_doors.map fun pick =>
      let car_location := if w d1 = car then d1 else if w d2 = car then d2 else d3
      let staying_wins := w pick = car
      let switching_wins := ¬staying_wins  -- In Monty Hall, exactly one strategy wins
      { car_location, player_pick := pick, switching_wins, staying_wins }

#eval strategic_outcomes

-- Count strategic wins using readable helper functions
def count_switch_wins (outcomes : List StrategicOutcome) : Nat :=
  outcomes.filter (·.switching_wins) |>.length

def count_stay_wins (outcomes : List StrategicOutcome) : Nat :=
  outcomes.filter (·.staying_wins) |>.length


/-!
### Formal Verification

We can prove that switching is better than staying.
-/

-- Theorem: Switching wins in exactly 6 out of 9 strategic situations
theorem switching_wins_two_thirds : count_switch_wins strategic_outcomes = 6 := by
  decide

-- Theorem: Staying wins in exactly 3 out of 9 strategic situations
theorem staying_wins_one_third : count_stay_wins strategic_outcomes = 3 := by
  decide

-- Theorem: There are exactly 9 strategic situations
theorem total_is_nine : strategic_outcomes.length = 9 := by
  decide

/-!
**Conclusion**: The formal verification confirms that switching wins in 6/9 = 2/3 of cases,
while staying wins in 3/9 = 1/3 of cases. Always switch!

This demonstrates that our intuition about probability can be misleading. The key insight is
understanding that when you initially pick, you have a 1/3 chance of being right. The host's
action of revealing a goat doesn't change the probability of your original choice, but
concentrates the remaining 2/3 probability on the door you can switch to.
-/
