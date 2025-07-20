import Mathlib.Probability.Notation


/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

In a group of 23 people, what's the probability that at least two people share the same birthday? (Assume 365 days in a year and ignore leap years.)
-/





open MeasureTheory ProbabilityTheory

variable {n m : ℕ}

instance : MeasurableSpace (Fin m) := ⊤

instance : MeasurableSingletonClass (Fin m) := ⟨fun _ => trivial⟩

-- Uniform probability measure on function spaces
noncomputable instance measureSpace : MeasureSpace (Fin n → Fin m) :=
  ⟨uniformOn Set.univ⟩

-- Verify it's a probability measure (total measure = 1)
instance : IsProbabilityMeasure (ℙ : Measure (Fin n → Fin (m + 1))) :=
  uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
