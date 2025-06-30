import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Notation
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Fintype.Card

open MeasureTheory ProbabilityTheory Set ENNReal Finset

-- Basic test of ENNReal computation
example : (6 : ENNReal) * (18 : ENNReal)⁻¹ = (3 : ENNReal)⁻¹ := by norm_num

example : (6 : ENNReal) * ((2 : ENNReal) / 18) = (2 : ENNReal) / 3 := by norm_num