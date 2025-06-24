import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic

open  MeasureTheory ProbabilityMeasure ProbabilityTheory Set ENNReal

/-!
# The Monty Hall Problem

**Problem**: You're on a game show with three doors. Behind one door is a car, behind the other two are goats. You pick a door (say door 1). The host, who knows what's behind each door, opens another door (say door 3) revealing a goat. The host then asks: "Do you want to switch to door 2?"

**Question**: Should you switch doors to maximize your chance of winning the car?

**Intuition**: Many people think it doesn't matter (50/50 chance), but switching actually gives you a 2/3 probability of winning versus 1/3 for staying with your original choice.


See https://brilliant.org/wiki/monty-hall-problem/
-/



inductive Door : Type
| left
| middle
| right
deriving DecidableEq, Repr, Fintype

open Door


-- Basic measurable space instances
instance : MeasurableSpace Door := ⊤
instance : MeasurableSingletonClass Door := by infer_instance

structure ShowOutcome where
  car   : Door
  pick  : Door
  host  : Door
  deriving DecidableEq, Repr
deriving instance Fintype for ShowOutcome

instance  : MeasurableSpace ShowOutcome :=
  letI := inferInstanceAs (MeasurableSpace (Door × Door × Door))
  MeasurableSpace.comap (fun (ω : ShowOutcome) => (ω.car, ω.pick, ω.host)) inferInstance

def outcome_weight (ω : ShowOutcome) : ℕ :=
  if ω.host = ω.pick then 0     -- Host never opens the picked door.
  else if ω.host = ω.car then 0 -- Host never opens the car door.
  else
    if ω.car = ω.pick then 1    -- Contestant chose the car. Host chooses from 2 doors.
    else 2                      -- Contestant chose a goat. Host is forced to open the only other goat door.

def sum_weights : ℝ≥0∞ := ∑ ω : ShowOutcome, outcome_weight ω



theorem sum_weights_concrete : sum_weights = 18 := by
  unfold sum_weights
  norm_cast


noncomputable def density (ω : ShowOutcome) : ℝ≥0∞ :=
  ((outcome_weight ω) : ℝ≥0∞) / sum_weights


theorem density_sums_one : HasSum density 1 := by
  --  I don't know how to compute sums of a normalized measure function. I have tried hundreds of lemmas, but none of them worked.
  sorry


noncomputable def p : PMF ShowOutcome :=
  { val := density,
    property :=  density_sums_one
  }

lemma third_door_available (pick host : Door) : ((Finset.univ.erase pick).erase host).Nonempty := by
  fin_cases pick <;> fin_cases host <;> decide

-- This had to be deterministic.
def remaining_door (pick host : Door) : Door :=
  match pick, host with
  | left, middle => right
  | left, right => middle
  | middle, left => right
  | right, left => middle
  | right, middle => left
  | right, right => left
  | middle, right => left
  | middle, middle => left
  | left, left => right

def switch_win_event : Set ShowOutcome :=
  { ω | remaining_door ω.pick ω.host = ω.car }

def noswitch_win_event : Set ShowOutcome :=
  { ω | ω.pick = ω.car }

 def switch_win_pred (ω : ShowOutcome) : Prop := remaining_door ω.pick ω.host = ω.car
 def no_switch_win_pred (ω : ShowOutcome) : Prop := ω.pick = ω.car

instance : DecidablePred switch_win_pred :=  by
  unfold switch_win_pred
  infer_instance
instance : DecidablePred no_switch_win_pred := by
  unfold no_switch_win_pred
  infer_instance


noncomputable def Prob  := p.toMeasure

instance: IsFiniteMeasure Prob := by
  unfold Prob
  infer_instance

-- Assume that the participant always picks the left door and the host opens the right door.

-- This is the event set that you win if you stay with your original choice.
def H := { ω : ShowOutcome | ω.pick = left ∧ ω.car = left}

-- I need to prove a lot of these probabilities. But I could not find a straightforward calculation of a user-define discrete probability measure.
theorem H_p : Prob H = 1/3 := by
  unfold H
  rw [Prob, p,]
  -- How to reduce this sum over a range to a sum of a finite amount of terms?
  sorry

-- Evidence that the host opened the right door.
def E := { ω : ShowOutcome | ω.pick = left ∧  ω.host = right }

instance H_m : MeasurableSet H := by
  -- This is doable by looking at these sets as the pre-image of measurable element in the outcome space.
  admit

instance : MeasurableSet E := by
  -- Also doable
  admit


theorem total_prob_eq: Prob E = Prob[E|H] * Prob H + Prob[E|Hᶜ] * Prob Hᶜ  := by
  -- I could not find the law of total probability in mathlib, maybe I overlooked it.
  sorry



theorem do_not_switch_eq : Prob[H|E]  = Prob switch_win_pred  := by
  rw [cond_eq_inv_mul_cond_mul]
  · rw [total_prob_eq, H_p]
    sorry
  · sorry
  exact H_m

theorem do_switch_eq : Prob[Hᶜ|E] = Prob no_switch_win_pred := by
  -- It was kind of important for me to use Bayes theorem here, because I want to show the benefit of having Mathlib provided.
  rw [cond_eq_inv_mul_cond_mul]
  · rw [total_prob_eq, H_p]
    sorry
  · sorry
  exact MeasurableSet.compl H_m

-- The official solution to the Monty Hall problem is that switching gives you a 2/3 chance of winning compared to 1/3 for not switching.
theorem monty_hall_solution: Prob switch_win_pred > Prob no_switch_win_pred := by
  have switch_prob: Prob switch_win_pred = 2/3 := by
    rw [<- do_not_switch_eq]
    sorry
  have noswitch_prob: Prob no_switch_win_pred = 1/3 := by
    rw [<- do_switch_eq]
    sorry
  simp [switch_prob, noswitch_prob]
  sorry
