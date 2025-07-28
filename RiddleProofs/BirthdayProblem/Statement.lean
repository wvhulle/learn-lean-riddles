import Mathlib.Probability.Notation

/-! Written by Eric Rodriguez

-/

set_option warningAsError false

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

In a group of 23 people, what's the probability that at least two people
share the same birthday? (Assume 365 days in a year and ignore leap years.)

**Answer**: More than 50%! The crossover point is between 22 and 23 people.

## Key Mathematical Insights

1. **Combinatorial approach**: Model "everyone has different birthdays" as injective functions
   from people to days. Count using `Fintype.card (α ↪ β)`.

2. **Measure theory approach**: Use uniform probability on the space of all birthday assignments.
   The probability space is `Fin n → Fin m` with counting measure.
-/

-- Local notation for readability
notation "|" x "|" => Finset.card x    -- cardinality of finite sets
notation "‖" x "‖" => Fintype.card x   -- cardinality of finite types

/-!
## Theorem Statements

We provide two equivalent formulations of the birthday problem.
-/

/-- Combinatorial version: comparing cardinalities of injective vs all functions -/
private theorem birthday :
    2 * ‖Fin 23 ↪ Fin 365‖ < ‖Fin 23 → Fin 365‖ ∧ 2 * ‖Fin 22 ↪ Fin 365‖ > ‖Fin 22 → Fin 365‖ := by
  sorry

/-!
## Measure Theory Setup

To prove the probabilistic version, we need to equip our finite types with measure theory structure.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

variable {n m : ℕ}

-- Discrete measurable space where all subsets are measurable
instance : MeasurableSpace (Fin m) := ⊤

instance : MeasurableSingletonClass (Fin m) := ⟨fun _ => trivial⟩

-- Uniform probability measure on function spaces
noncomputable instance measureSpace : MeasureSpace (Fin n → Fin m) :=
  ⟨uniformOn Set.univ⟩

-- Verify it's a probability measure (total measure = 1)
instance : IsProbabilityMeasure (ℙ : Measure (Fin n → Fin (m + 1))) :=
  uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

/-- Helper lemma: probability equals cardinality ratio -/
private theorem FinFin.measure_apply {s : Set <| Fin n → Fin m} :
    ℙ s = |s.toFinite.toFinset| / ‖Fin n → Fin m‖ := by
  sorry

/-- Probabilistic version: probability of all different birthdays < 1/2 -/
private theorem birthday_measure :
    ℙ ({f | Function.Injective f} : Set (Fin 23 → Fin 365)) < 1 / 2 := by
  sorry
