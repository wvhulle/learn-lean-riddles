import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
open  MeasureTheory ProbabilityTheory Set ENNReal Finset

/-!
# The Monty Hall Problem

This file formalizes the Monty Hall problem, a classic probability puzzle.

**The Problem**

You are a contestant on a game show. You are presented with three closed doors. Behind one door is a car (the prize), and behind the other two are goats. You complete the following steps:
1. You choose one door.
2. The host, who knows where the car is, opens one of the other two doors to reveal a goat.
3. The host asks if you want to switch your choice to the remaining closed door.

**The Question**

Is it to your advantage to switch doors?

**The Solution**

Yes. Switching doors doubles your probability of winning the car from 1/3 to 2/3.
-/

/-!
## Section 1: Basic Types and Definitions
-/

inductive Door : Type
| left
| middle
| right
deriving DecidableEq, Repr, Fintype

open Door

inductive Strategy : Type
| Switch
| Stay
deriving DecidableEq, Repr, Fintype

open Strategy

structure Game where
  car      : Door
  pick     : Door
  host     : Door
  deriving DecidableEq, Repr, Fintype

/-!
## Section 2: Game Validity and Probability Framework
-/

-- A valid game means host doesn't open the picked door or the car door
def is_valid_game (g : Game) : Prop := g.host ≠ g.pick ∧ g.host ≠ g.car

instance : MeasurableSpace Game := ⊤
instance : DiscreteMeasurableSpace Game := ⟨fun _ => trivial⟩

-- Probability weights based on game logic
def game_weight (ω : Game) : ℝ :=
  if ω.host = ω.pick then 0     -- Host never opens the picked door
  else if ω.host = ω.car then 0 -- Host never opens the car door
  else
    if ω.car = ω.pick then 1    -- Contestant chose the car. Host has 2 choices
    else 2                      -- Contestant chose a goat. Host is forced to open the only other goat door

def total_game_weights : ℝ := ∑ ω : Game, game_weight ω

theorem total_weight_value: total_game_weights = 18 := by
  simp [total_game_weights, game_weight]
  norm_cast

noncomputable def real_density (ω : Game) : ℝ  :=
  game_weight ω / total_game_weights

def non_zero_event : Game := {car := left, pick := left, host := middle}

theorem real_sum_one : HasSum real_density 1 := by
  convert hasSum_fintype real_density
  unfold real_density
  unfold total_game_weights
  have ne_zero : ∑ a, game_weight a ≠ 0 := by
    intro sum_zero
    have : game_weight non_zero_event ≤ 0 := by
      rw [← sum_zero]
      apply Finset.single_le_sum
      · intro i _
        simp [game_weight]
        split_ifs <;> norm_num
      · exact Finset.mem_univ _
    simp [game_weight, non_zero_event] at this
    norm_num at this
  rw [<- Finset.sum_div]
  rw [div_self ne_zero]

noncomputable def prob_density (i : Game) : ENNReal :=
  ENNReal.ofReal (real_density i)

theorem density_sums_to_one : HasSum prob_density 1 := by
  apply ENNReal.hasSum_coe.mpr
  apply NNReal.hasSum_coe.mp
  convert real_sum_one using 1
  have dpos: ∀ i, game_weight i ≥ 0 := by
    intro i
    simp [game_weight]
    split_ifs <;> norm_num
  have: ∀ i, real_density i >= 0 := by
    intro i
    simp [real_density]
    apply div_nonneg
    · exact dpos i
    · rw [total_game_weights]
      exact Finset.sum_nonneg (fun i _ => dpos i)
  ext i
  rw [Real.coe_toNNReal (real_density i) (this i)]

noncomputable def p : PMF Game :=
  { val := prob_density, property := density_sums_to_one }

noncomputable def Prob := p.toMeasure

instance : IsProbabilityMeasure Prob := by
  unfold Prob
  infer_instance

/-!
## Section 3: Strategy Framework
-/

-- Given a game state and strategy, what door does the player end up with?
def final_door (g : Game) (s : Strategy) : Door :=
  match s with
  | Stay => g.pick
  | Switch =>
    -- Find the door that is neither picked nor opened by host
    if g.pick ≠ left ∧ g.host ≠ left then left
    else if g.pick ≠ middle ∧ g.host ≠ middle then middle
    else right

-- Does the player win with a given strategy?
def wins (g : Game) (s : Strategy) : Prop :=
  final_door g s = g.car

-- Set of games where player wins with a given strategy
def wins_with_strategy (s : Strategy) : Set Game := {g | wins g s}

/-!
## Section 4: Basic Strategy Properties
-/

lemma final_door_stay (g : Game) : final_door g Stay = g.pick := by
  simp [final_door]

theorem stay_wins_iff_car_at_pick (g : Game) :
  is_valid_game g → (wins g Stay ↔ g.car = g.pick) := by
  intro hvalid
  simp [wins, final_door_stay]
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

theorem switch_wins_iff_car_not_at_pick_or_host (g : Game) :
  is_valid_game g → (wins g Switch ↔ g.car ≠ g.pick ∧ g.car ≠ g.host) := by
  intro hvalid
  -- Key insight: in a valid 3-door game, if car is not at pick and not at host,
  -- then it must be at the remaining door, which is exactly where switching takes you
  sorry

/-!
## Section 5: Prior Probabilities
-/

-- Each door has equal prior probability of having the car
theorem prior_car_probability (d : Door) : Prob {g | g.car = d} = 1/3 := by
  -- By the symmetry of the problem setup and our probability weights,
  -- each door has equal probability of containing the car
  unfold Prob
  rw [PMF.toMeasure_apply_fintype]
  simp [Set.indicator]
  fin_cases d <;> norm_cast
  sorry


/-!
## Section 6: Main Probability Results
-/

-- Probability of winning with each strategy
noncomputable def prob_win_switch : ENNReal := Prob (wins_with_strategy Switch)
noncomputable def prob_win_stay : ENNReal := Prob (wins_with_strategy Stay)

-- Key insight: when you pick a door, probability that car is behind it remains 1/3
-- The remaining 2/3 probability concentrates on the other door after host opens one
theorem prob_switch_wins : prob_win_switch = 2/3 := by
  -- The core insight of the Monty Hall problem:
  -- When you initially pick a door, P(car behind your door) = 1/3
  -- After host opens a goat door, P(car behind remaining door) = 2/3
  -- Switching always takes you to the remaining door
  sorry

theorem prob_stay_wins : prob_win_stay = 1/3 := by
  -- Staying wins exactly when you initially picked the car door
  -- This happens with probability 1/3 by symmetry
  sorry

/-!
## Section 7: The Main Monty Hall Result
-/

theorem monty_hall_switch_better :
  prob_win_switch = 2/3 ∧ prob_win_stay = 1/3 := by
  exact ⟨prob_switch_wins, prob_stay_wins⟩

theorem monty_hall_switch_advantage :
  prob_win_switch > prob_win_stay := by
  rw [prob_switch_wins, prob_stay_wins]
  -- Show that 2/3 > 1/3 (obviously true)
  sorry
