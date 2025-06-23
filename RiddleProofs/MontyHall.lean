import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Basic

open ProbabilityTheory MeasureTheory
open scoped ENNReal
/-!
# The Monty Hall Problem

**Problem**: You're on a game show with three doors. Behind one door is a car, behind the other two are goats. You pick a door (say door 1). The host, who knows what's behind each door, opens another door (say door 3) revealing a goat. The host then asks: "Do you want to switch to door 2?"

**Question**: Should you switch doors to maximize your chance of winning the car?

**Intuition**: Many people think it doesn't matter (50/50 chance), but switching actually gives you a 2/3 probability of winning versus 1/3 for staying with your original choice.

**Key Insight**: When you first picked, you had a 1/3 chance of being right. The remaining 2/3 probability is concentrated on the other doors. When the host eliminates one losing door, that 2/3 probability transfers entirely to the remaining door.
-/

namespace Enumerate

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

end Enumerate

/-!
**Conclusion**: The formal verification confirms that switching wins in 6/9 = 2/3 of cases,
while staying wins in 3/9 = 1/3 of cases. Always switch!

This demonstrates that our intuition about probability can be misleading. The key insight is
understanding that when you initially pick, you have a 1/3 chance of being right. The host's
action of revealing a goat doesn't change the probability of your original choice, but
concentrates the remaining 2/3 probability on the door you can switch to.
-/

open ProbabilityTheory Set
-- The three doors are represented by the finite type `Fin 3`.

section Bayes

-- The three doors are represented by the finite type `Fin 3`.
abbrev Door : Type := Fin 3

-- The sample space Ω represents all possible outcomes.
-- An outcome is a triple: (car location, player's initial pick, door opened by host).
structure MontyOutcome where
  car   : Door
  pick  : Door
  host  : Door
  deriving DecidableEq, Repr

deriving instance Fintype for MontyOutcome
abbrev Ω : Type := MontyOutcome


instance : MeasurableSpace Ω :=
  letI := inferInstanceAs (MeasurableSpace (Door × Door × Door))
  MeasurableSpace.comap (fun (ω : Ω) => (ω.car, ω.pick, ω.host)) inferInstance

noncomputable def monty_hall_pmf (ω : Ω) : ℝ≥0∞ :=
  let p_car_pick : ℝ≥0∞ := (1/3) * (1/3)
  let p_host : ℝ≥0∞ :=
    if ω.host = ω.pick then 0     -- Host never opens the picked door.
    else if ω.host = ω.car then 0 -- Host never opens the car door.
    else
      if ω.car = ω.pick then (1/2) -- Contestant chose the car. Host chooses from 2 doors.
      else 1                 -- Contestant chose a goat. Host is forced to open the only other goat door.
  p_car_pick * p_host


-- To define a probability measure, we first show the PMF sums to 1.
theorem monty_hall_sum_one : HasSum monty_hall_pmf 1 := by
  -- We can split the sum over car, pick, and host choices.
  -- The probability of any specific (car, pick) is 1/9.
  -- We show that for any (car, pick), the sum of host probabilities is 1.
  sorry

open PMF


noncomputable def monty_hall_pmf' : PMF Ω :=
  { val := monty_hall_pmf,
    property := monty_hall_sum_one
  }

noncomputable def μ  := monty_hall_pmf'.toMeasure


-- Define the unique other door to switch to
noncomputable def otherDoor (pick host : Door) : Door :=
  (((Finset.univ.erase pick).erase host).toList.head!)


-- Now define the two events:
def switch_win_event : Set Ω :=
  { ω | otherDoor ω.pick ω.host = ω.car }

def noswitch_win_event : Set Ω :=
  { ω | ω.pick = ω.car }

-- And the final statements of the theorems:
theorem monty_hall_switch_wins :
  μ switch_win_event = (2 : ℝ≥0∞) / 3 := by
  sorry

theorem monty_hall_noswitch_wins :
  μ noswitch_win_event = (1 : ℝ≥0∞) / 3 := by
  sorry
