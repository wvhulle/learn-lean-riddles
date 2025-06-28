import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.BigOperators.Field
import
Mathlib.Algebra.Order.BigOperators.Group.Finset

structure Thing where
  a : Fin 3
  b : Fin 3
  deriving Repr, DecidableEq, Fintype

def pairs := ({0, 1, 2} ×ˢ {0, 1, 2} : Finset (Fin 3 × Fin 3))
def all_things : Finset Thing :=
  pairs.map ⟨(fun (x : Fin 3 × Fin 3) => (⟨x.1, x.2⟩ : Thing)), by simp [Function.Injective]⟩


theorem univ_eq_allThing : (Finset.univ : Finset Thing) = all_things := by
  ext thing
  simp [all_things]
  use thing.a, thing.b
  simp [pairs]
  omega


noncomputable def density (i : Thing) : ℝ  :=
  match i with
  | {a, b } => a + b

noncomputable def sum_density : ℝ := ∑ i: Thing, density i

noncomputable def normalised_density (i : Thing) : ℝ :=
   density i / sum_density

-- theorem real_sum : sum_density = 18 := by
--     simp [sum_density, density]
--     simp [univ_eq_allThing]
--     simp [all_things, pairs]
--     simp [Finset.sum_product]
--     norm_cast


-- theorem normalised_sums_one : HasSum normalised_density 1 := by
--   have total_sum : HasSum density sum_density := by
--     apply hasSum_fintype
--   unfold normalised_density
--   rw [<- div_self]
--   · apply HasSum.div_const total_sum sum_density
--   · rw [real_sum]
--     linarith

-- open Finset

theorem real_sum_one : HasSum normalised_density 1 := by
  convert hasSum_fintype normalised_density
  unfold normalised_density
  unfold sum_density
  have ne_zero : ∑ a, density a ≠ 0 := by
    intro sum_zero
    have : density ⟨1, 1⟩ ≤ 0 := by
      rw [← sum_zero]
      apply Finset.single_le_sum
      · intro i _
        simp [density]
        exact add_nonneg (Nat.cast_nonneg i.a) (Nat.cast_nonneg i.b)
      · exact Finset.mem_univ _
    simp [density] at this
    norm_num at this
  rw [<- Finset.sum_div]
  rw [div_self ne_zero]


noncomputable def ennreal_normalised_density (i : Thing) : ENNReal :=
  ENNReal.ofReal (normalised_density i)

theorem ennreal_normalised_sums_one : HasSum ennreal_normalised_density 1 := by
  apply ENNReal.hasSum_coe.mpr
  apply NNReal.hasSum_coe.mp
  convert real_sum_one using 1


  have dpos: ∀ i, density i ≥ 0 := by
    intro i
    simp [density]
    exact add_nonneg (Nat.cast_nonneg i.a) (Nat.cast_nonneg i.b)

  have: ∀ i, normalised_density i >= 0 := by
    intro i
    simp [normalised_density]
    apply div_nonneg
    · exact dpos i
    · rw [sum_density]
      exact Finset.sum_nonneg (fun i _ => dpos i)
  ext i
  rw [Real.coe_toNNReal (normalised_density i) (this i)]

noncomputable def p : PMF Thing :=
  { val := ennreal_normalised_density,
    property :=  ennreal_normalised_sums_one
  }
