import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.Posterior

/-! Written by Matteo Cipollina

This file contains generic measure theory and probability theory.
-/

set_option linter.unusedVariables false

namespace Measure

open PMF ProbabilityTheory MeasureTheory Filter Finset
open scoped ENNReal

/-- Value of a `compProd` measure on a rectangle whose first side is a singleton. -/
@[simp]
lemma compProd_apply_singleton
    {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω 𝓧) [IsSFiniteKernel κ] (a : Ω) {s : Set 𝓧}
    (hs : MeasurableSet s) :
    (μ.compProd κ) ({a} ×ˢ s) = μ {a} * κ a s := by
  have h :=
    Measure.compProd_apply_prod (μ := μ) (κ := κ)
      (s := ({a} : Set Ω)) (t := s) (MeasurableSet.singleton a) hs
  have h_int :
      (∫⁻ ω in ({a} : Set Ω), κ ω s ∂μ) = μ {a} * κ a s := by
    rw [lintegral_singleton (f := fun ω : Ω => κ ω s) (a := a)]
    ring
  rw [h, h_int]

end Measure

namespace ProbabilityTheory

namespace Kernel

lemma measurable_kernel_prod_mk_of_const {Ω 𝓧 : Type*}
  [MeasurableSpace Ω] [MeasurableSpace 𝓧]
  (κ : Kernel Ω 𝓧) {s : Set 𝓧} (hs : MeasurableSet s) :
  Measurable (fun ω ↦ κ ω s) := by
  exact Kernel.measurable_coe κ hs

end Kernel

open PMF ProbabilityTheory MeasureTheory Filter Finset
open scoped ENNReal

/-- Bayes' rule on singletons  -/
lemma posterior_apply_singleton
    {Ω 𝓧 : Type*} [Fintype Ω] [Fintype 𝓧] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSpace 𝓧]
    [StandardBorelSpace Ω] [StandardBorelSpace 𝓧]
    (κ : Kernel Ω 𝓧) [IsMarkovKernel κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : 𝓧) (y : Ω)
    (hpos : ((κ ∘ₘ μ) {x}) ≠ 0) :
    (κ†μ) x {y} = (μ {y} * (κ y {x})) / ((κ ∘ₘ μ) {x}) := by
  classical
  have := (Measure.condKernel_apply_of_ne_zero
            (ρ := Measure.map Prod.swap (μ.compProd κ))
            (x := x) (s := ({y} : Set Ω)))
            ?fst_ne_zero
  · have h₁ :
        ((Measure.map Prod.swap (μ.compProd κ)).fst {x})
          = ((κ ∘ₘ μ) {x}) := by
      simp
    have h₂ :
        (Measure.map Prod.swap (μ.compProd κ)) ({x} ×ˢ ({y} : Set Ω))
          = (μ.compProd κ) ({y} ×ˢ ({x} : Set 𝓧)) := by
      rw [Measure.map_apply measurable_swap ((MeasurableSet.singleton x).prod (MeasurableSet.singleton y))]
      congr 1
      ext ⟨a, b⟩
      simp [Prod.swap]; aesop
    have h₃ :
        (μ.compProd κ) ({y} ×ˢ ({x} : Set 𝓧))
          = μ {y} * κ y {x} := by
      simpa using
        Measure.compProd_apply_singleton (μ := μ) (κ := κ)
          (a := y) (s := {x}) (by simp)
    rw [ProbabilityTheory.posterior]
    rw [this, h₁, h₂, h₃]
    rw [div_eq_mul_inv, mul_comm (μ {y}), mul_assoc]
    exact mul_rotate' ((⇑κ ∘ₘ μ) {x})⁻¹ ((κ y) {x}) (μ {y})
  · have : ((Measure.map Prod.swap (μ.compProd κ)).fst {x})
        = ((κ ∘ₘ μ) {x}) := by
      simp
    simpa [this] using hpos

namespace ENNReal

private lemma mul_div_assoc (a b c : ℝ≥0∞) : (a * b) / c = a * (b / c) := by
  rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv]

private lemma one_div_inv (a : ℝ≥0∞) : (1 / a)⁻¹ = a := by
  simp

end ENNReal

open scoped BigOperators

/-- Unfold `μ.bind κ` on a measurable set as the integral of the kernel. -/
@[simp]
lemma Measure.bind_measurable_set {Ω 𝓧 : Type*}
  [MeasurableSpace Ω] [MeasurableSpace 𝓧]
  (μ : Measure Ω) (κ : Kernel Ω 𝓧)
  [SFinite μ] [IsSFiniteKernel κ]
  {s : Set 𝓧} (hs : MeasurableSet s) :
  μ.bind κ s = ∫⁻ ω, κ ω s ∂μ := by
  apply Measure.bind_apply hs
  exact Kernel.aemeasurable κ

/--  Unfold `κ ∘ₘ μ` as an integral, so that in the `Fintype` case
    one can turn it into a finite sum. -/
@[simp]
lemma comp_apply {Ω 𝓧 : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSingletonClass Ω]
  (κ : Kernel Ω 𝓧) (μ : Measure Ω)
  [IsSFiniteKernel κ]
  {s : Set 𝓧} (hs : MeasurableSet s) :
  (κ ∘ₘ μ) s = ∑ ω, μ {ω} * κ ω s := by
  rw [Measure.bind_apply hs (Kernel.aemeasurable κ)]
  rw [lintegral_fintype]
  congr with ω
  exact CommMonoid.mul_comm ((κ ω) s) (μ {ω})

/- Constructing a kernel from an arbitrary function requires measurability. A direct proof of measurability is much easier when the domain is countable. A measurable countable space with measurable singletons turns any function `f: α -> β` into a measurable function. -/
lemma Kernel.ofFunOfCountable_apply [MeasurableSpace α] [MeasurableSpace β] [Countable α]
    /- `MeasurableSingletonClass is required when you need to evaluate kernel at a point. -/
    [MeasurableSingletonClass α] (f : α → Measure β) (a : α) :
    Kernel.ofFunOfCountable f a = f a := rfl

namespace Finset

/-- Sum over a finite type with exactly three pairwise-different elements. -/
lemma sum_univ_of_three {α β : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid β] (f : α → β) {a b c : α}
    (ha : a ≠ b) (hb : a ≠ c) (hc : b ≠ c)
    (hcover : Finset.univ = {a, b, c}) :
    (∑ x, f x) = f a + f b + f c := by
  rw [hcover]
  have h₁ : (a : α) ∉ ({b, c} : Finset α) := by
    simp [ha, hb]
  have h₂ : (b : α) ∉ ({c} : Finset α) := by
    simp [hc]
  simp [Finset.sum_insert h₁, Finset.sum_insert h₂, Finset.sum_singleton,
        add_comm, add_left_comm]


end Finset

end ProbabilityTheory
