/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Probability.UniformOn
import Mathlib.Probability.Notation

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

**The problem**: In a group of 23 people, what's the probability that at least two people 
share the same birthday? (Assume 365 days in a year and ignore leap years.)

**The surprising answer**: More than 50%! Specifically, about 50.7%.

**Mathematical approach**: Instead of calculating the probability directly, we calculate 
the probability that everyone has different birthdays, then subtract from 1.

**Learning goals for this formalization**
- Understand the connection between counting and probability
- Learn about injective functions (embeddings) and their cardinality
- See how measure theory works in Lean for finite probability spaces
- Practice working with decidable computations

**Key insight**: We model "everyone has different birthdays" as an injective function 
from people to days. The number of such functions is counted by `Fintype.card (α ↪ β)`.

As opposed to the standard probabilistic statement, we instead state the birthday problem
in terms of injective functions. The general result about `Fintype.card (α ↪ β)` which this proof
uses is `Fintype.card_embedding_eq`.
-/


namespace Theorems100

-- Local notation to make the formulas more readable
local notation "|" x "|" => Finset.card x    -- cardinality of finite sets
local notation "‖" x "‖" => Fintype.card x   -- cardinality of finite types

/-- **Birthday Problem**: set cardinality interpretation. 
    
This theorem shows that:
- For 23 people: less than half of all birthday assignments have everyone with different birthdays
- For 22 people: more than half of all birthday assignments have everyone with different birthdays
    
The crossover point is between 22 and 23 people! -/
theorem birthday :
    2 * ‖Fin 23 ↪ Fin 365‖ < ‖Fin 23 → Fin 365‖ ∧ 2 * ‖Fin 22 ↪ Fin 365‖ > ‖Fin 22 → Fin 365‖ := by
  -- ‖Fin 23 ↪ Fin 365‖ = number of ways to assign 23 distinct birthdays
  -- ‖Fin 23 → Fin 365‖ = total number of ways to assign 23 birthdays (repetitions allowed)
  -- The first is 365 * 364 * ... * 343 (365 falling factorial 23)
  -- The second is 365^23
  simp only [Fintype.card_fin, Fintype.card_embedding_eq, Fintype.card_fun]
  decide  -- Lean can verify this by direct computation!

section MeasureTheory
/-! 
## Measure Theory Approach

This section proves the birthday problem using measure theory - the rigorous mathematical
foundation for probability. This is more advanced than the combinatorial approach above.

**Key concept**: We model the space of all birthday assignments as a measure space,
where each assignment has equal probability (uniform distribution).
-/

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory ENNReal

variable {n m : ℕ}

-- **Setting up the probability space**
-- We need to tell Lean that our finite types can be equipped with probability measures

/- In order for Lean to understand that we can take probabilities in `Fin 23 → Fin 365`, we must
tell Lean that there is a `MeasurableSpace` structure on the space. Note that this instance
is only for `Fin m` - Lean automatically figures out that the function space `Fin n → Fin m`
is _also_ measurable, by using `MeasurableSpace.pi`, and furthermore that all sets are measurable,
from `MeasurableSingletonClass.pi`. -/
instance : MeasurableSpace (Fin m) :=
  ⊤  -- The discrete measurable space (all subsets are measurable)

instance : MeasurableSingletonClass (Fin m) :=
  ⟨fun _ => trivial⟩  -- Every singleton set is measurable

/- We then endow the space with a canonical measure, which is called ℙ.
We define this to be the uniform counting measure - each birthday assignment
is equally likely. -/
noncomputable instance measureSpace : MeasureSpace (Fin n → Fin m) :=
  ⟨uniformOn Set.univ⟩  -- Uniform distribution over all possible functions

-- The canonical measure on `Fin n → Fin m` is a probability measure (except on an empty space).
-- This tells Lean that our probability space is properly normalized (total probability = 1)
instance : IsProbabilityMeasure (ℙ : Measure (Fin n → Fin (m + 1))) :=
  uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

theorem FinFin.measure_apply {s : Set <| Fin n → Fin m} :
    ℙ s = |s.toFinite.toFinset| / ‖Fin n → Fin m‖ := by
  rw [volume, measureSpace, uniformOn_univ, Measure.count_apply_finite]

/-- **Birthday Problem**: first probabilistic interpretation. -/
theorem birthday_measure :
    ℙ ({f | (Function.Injective f)} : Set ((Fin 23) → (Fin 365))) < 1 / 2 := by
  rw [FinFin.measure_apply]
  generalize_proofs hfin
  have : |hfin.toFinset| = 42200819302092359872395663074908957253749760700776448000000 := by
    trans ‖Fin 23 ↪ Fin 365‖
    · rw [← Fintype.card_coe]
      apply Fintype.card_congr
      rw [Set.Finite.coeSort_toFinset, Set.coe_setOf]
      exact Equiv.subtypeInjectiveEquivEmbedding _ _
    · rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
      rfl
  rw [this, ENNReal.lt_div_iff_mul_lt, mul_comm, mul_div, ENNReal.div_lt_iff]
  all_goals
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    norm_num

end MeasureTheory

end Theorems100
