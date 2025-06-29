import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
variables {s t : Set Ω} (hms : MeasurableSet s) (hmt : MeasurableSet t)

#check ProbabilityTheory.cond_eq_inv_mul_cond_mul μ hms hmt
