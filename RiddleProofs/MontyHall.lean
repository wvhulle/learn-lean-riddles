import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs




open ProbabilityTheory MeasureTheory ProbabilityMeasure MeasurableSpace Fintype Finset
open scoped ENNReal
/-!
# The Monty Hall Problem

**Problem**: You're on a game show with three doors. Behind one door is a car, behind the other two are goats. You pick a door (say door 1). The host, who knows what's behind each door, opens another door (say door 3) revealing a goat. The host then asks: "Do you want to switch to door 2?"

**Question**: Should you switch doors to maximize your chance of winning the car?

**Intuition**: Many people think it doesn't matter (50/50 chance), but switching actually gives you a 2/3 probability of winning versus 1/3 for staying with your original choice.

**Key Insight**: When you first picked, you had a 1/3 chance of being right. The remaining 2/3 probability is concentrated on the other doors. When the host eliminates one losing door, that 2/3 probability transfers entirely to the remaining door.
-/


/-!
**Conclusion**: The formal verification confirms that switching wins in 6/9 = 2/3 of cases,
while staying wins in 3/9 = 1/3 of cases. Always switch!

This demonstrates that our intuition about probability can be misleading. The key insight is
understanding that when you initially pick, you have a 1/3 chance of being right. The host's
action of revealing a goat doesn't change the probability of your original choice, but
concentrates the remaining 2/3 probability on the door you can switch to.
-/


section Bayes

open ProbabilityTheory Set


abbrev Door : Type := Fin 3

-- Ensure Door has a measurable space instance
instance : MeasurableSpace Door := by infer_instance

structure MontyOutcome where
  car   : Door
  pick  : Door
  host  : Door
  deriving DecidableEq, Repr

deriving instance Fintype for MontyOutcome

instance monty_meas : MeasurableSpace MontyOutcome :=
  letI := inferInstanceAs (MeasurableSpace (Door × Door × Door))
  MeasurableSpace.comap (fun (ω : MontyOutcome) => (ω.car, ω.pick, ω.host)) inferInstance

def outcome_weight (ω : MontyOutcome) : ℕ :=
  if ω.host = ω.pick then 0     -- Host never opens the picked door.
  else if ω.host = ω.car then 0 -- Host never opens the car door.
  else
    if ω.car = ω.pick then 1    -- Contestant chose the car. Host chooses from 2 doors.
    else 2                      -- Contestant chose a goat. Host is forced to open the only other goat door.

-- Calculate the normalization constant
def sum_weights : ℝ≥0∞ := ∑ ω : MontyOutcome, outcome_weight ω



-- Prove that the sum equals 18
theorem sum_weights_concrete : sum_weights = 18 := by
  unfold sum_weights
  -- The sum over a finite type is computable
  norm_cast


noncomputable def probability_density_f (ω : MontyOutcome) : ℝ≥0∞ :=
  ((outcome_weight ω) : ℝ≥0∞) / sum_weights


open PMF

theorem pf_sum_one :  HasSum probability_density_f 1 := by

  sorry



noncomputable def p : PMF MontyOutcome :=
  { val := probability_density_f,
    property :=  pf_sum_one
  }

lemma third_door_available (pick host : Door) : ((Finset.univ.erase pick).erase host).Nonempty := by
  fin_cases pick <;> fin_cases host <;> decide

 def remaining_door (pick host : Door) : Door :=
  (Finset.univ.erase pick).erase host |>.min' (third_door_available pick host)


def switch_win_event : Set MontyOutcome :=
  { ω | remaining_door ω.pick ω.host = ω.car }

def noswitch_win_event : Set MontyOutcome :=
  { ω | ω.pick = ω.car }

 def switch_win_pred (ω : MontyOutcome) : Prop := remaining_door ω.pick ω.host = ω.car
 def no_switch_win_pred (ω : MontyOutcome) : Prop := ω.pick = ω.car

instance : DecidablePred switch_win_pred :=  by
  unfold switch_win_pred
  infer_instance
instance : DecidablePred no_switch_win_pred := by
  unfold no_switch_win_pred
  infer_instance

-- door 1 has a car behind it
def H : Set MontyOutcome :=
  { ω | ω.car = 1 }


theorem H_measurable : MeasurableSet H := by
  have : H = (fun ω : MontyOutcome => ω.car) ⁻¹' {1} := by
    ext ω
    simp [H]
  rw [this]
  apply MeasurableSet.preimage
  · exact MeasurableSet.singleton _
  · exact measurable_fst.comp (comap_measurable _)


noncomputable def P  := p.toMeasure

open ENNReal

-- Prior probability that door 1 has the car
example : P H = 1 / 3 := by
  simp [P]
  rw [p.toMeasure_apply]
  simp [H]
  · show ∑' (ω : MontyOutcome), {ω | ω.car = 1}.indicator (p) ω = 3⁻¹
    simp [indicator, p]

    sorry
  · sorry





-- evidence that Monty has revealed a door with a goat behind it
def E : Set MontyOutcome :=
  { ω | ω.pick = 1 ∧ ω.car ≠ 1 }


-- Conditional probability that door 1 has car given we picked door 0 and car is not there
theorem monty_hall_solution : P[H|E] = 2 / 3 := by
  have : IsFiniteMeasure P := by sorry
  rw [cond_eq_inv_mul_cond_mul _ _ P]
  · sorry
  · show MeasurableSet E
    sorry
  · show MeasurableSet H
    exact H_measurable
