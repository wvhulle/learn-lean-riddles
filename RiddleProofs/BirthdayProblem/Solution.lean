import RiddleProofs.BirthdayProblem.Statement

/-!
# Solution to birthday paradox

## Question

In a group of 23 people, what's the probability that at least two people
share the same birthday? (Assume 365 days in a year and ignore leap years.)

## Answer

More than 50%! The crossover point is between 22 and 23 people.
-/



notation "|" x "|" => Finset.card x    -- cardinality of finite sets
notation "‖" x "‖" => Fintype.card x   -- cardinality of finite types



theorem birthday :
    2 * ‖Fin 23 ↪ Fin 365‖ < ‖Fin 23 → Fin 365‖ ∧ 2 * ‖Fin 22 ↪ Fin 365‖ > ‖Fin 22 → Fin 365‖ := by
  simp only [Fintype.card_fin, Fintype.card_embedding_eq, Fintype.card_fun]
  decide

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory ENNReal

variable {n m : ℕ}

theorem FinFin.measure_apply {s : Set <| Fin n → Fin m} :
    ℙ s = |s.toFinite.toFinset| / ‖Fin n → Fin m‖ := by
  rw [volume, measureSpace, uniformOn_univ, Measure.count_apply_finite]


lemma total_functions : ‖Fin 23 → Fin 365‖ = 365^23 := by
  calc
    ‖Fin 23 → Fin 365‖ = ∏ (_ : Fin 23), ‖Fin 365‖ := by
      rw [Fintype.card_pi]
    _ = ∏ (_ : Fin 23), 365 := by
      simp only [Fintype.card_fin]
    _ = 365^23 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma total_explicit : (365^23 : ℕ) = 85651679353150321236814267844395152689354622364044189453125 := by
    norm_num

/-- Measure theoretic proof that P(all different birthdays) < 1/2 for 23 people -/
theorem birthday_measure :
    ℙ ({f | (Function.Injective f)} : Set ((Fin 23) → (Fin 365))) < 1 / 2 := by
  rw [FinFin.measure_apply]
  generalize_proofs hfin
  have card_eq : |hfin.toFinset| = 42200819302092359872395663074908957253749760700776448000000 := calc
    |hfin.toFinset| = ‖Fin 23 ↪ Fin 365‖ := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      rw [Set.Finite.coeSort_toFinset, Set.coe_setOf]
      exact Equiv.subtypeInjectiveEquivEmbedding _ _
    _ = Nat.descFactorial 365 23 := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    _ = 42200819302092359872395663074908957253749760700776448000000 := by rfl
  rw [card_eq, ENNReal.lt_div_iff_mul_lt, mul_comm, mul_div, ENNReal.div_lt_iff]
  all_goals
    rw [total_functions, total_explicit]
    norm_num
