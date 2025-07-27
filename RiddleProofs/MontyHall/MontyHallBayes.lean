import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.Posterior

namespace ENNReal
open scoped ENNReal
noncomputable instance instInvENNReal : Inv ℝ≥0∞ := inferInstance

lemma inv_mul_top_top : (⊤ : ℝ≥0∞)⁻¹ * (⊤ : ℝ≥0∞)⁻¹ = (⊤ * ⊤)⁻¹ := by
  simp [ENNReal.inv_top]

lemma inv_mul_top_coe (d : ℝ≥0∞) (hd : d ≠ 0) : (⊤ : ℝ≥0∞)⁻¹ * d⁻¹ = (⊤ * d)⁻¹ := by
  rw [ENNReal.inv_top, zero_mul]
  have h_mul_top : ⊤ * d = ⊤ := by
    by_cases hd_top : d = ⊤
    · rw [hd_top]; simp
    · exact ENNReal.top_mul hd
  rw [h_mul_top, ENNReal.inv_top]

lemma inv_mul_coe_top (b : ℝ≥0∞) (hb : b ≠ 0) : b⁻¹ * (⊤ : ℝ≥0∞)⁻¹ = (b * ⊤)⁻¹ := by
  rw [ENNReal.inv_top, mul_zero]
  have h_mul_top : b * ⊤ = ⊤ := by
    by_cases hb_top : b = ⊤
    · rw [hb_top]; simp
    · exact ENNReal.mul_top hb
  rw [h_mul_top, ENNReal.inv_top]

lemma inv_mul_coe_coe {b d : ℝ≥0∞} (hb : b ≠ ⊤) (hd : d ≠ ⊤) :
    b⁻¹ * d⁻¹ = (b * d)⁻¹ := by
  by_cases hb_zero : b = 0
  · -- If b = 0, then b⁻¹ = ⊤
    rw [hb_zero, ENNReal.inv_zero]
    by_cases hd_zero : d = 0
    · -- If d = 0 too, then d⁻¹ = ⊤, and ⊤ * ⊤ = ⊤
      rw [hd_zero, ENNReal.inv_zero, mul_top']
      simp
    · -- If d ≠ 0, then ⊤ * d⁻¹ = ⊤
      have : d⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hd
      rw [ENNReal.top_mul this]
      rw [zero_mul, ENNReal.inv_zero]
  by_cases hd_zero : d = 0
  · -- If d = 0, then d⁻¹ = ⊤
    rw [hd_zero, ENNReal.inv_zero]
    have : b⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hb
    rw [ENNReal.mul_top this]
    rw [mul_zero, ENNReal.inv_zero]
  rw [ENNReal.mul_inv (Or.inl hb_zero) (Or.inl hb)]

lemma inv_mul_cases (b d : ℝ≥0∞) :
    b⁻¹ * d⁻¹ = (b * d)⁻¹ ↔
    ¬(b = ⊤ ∧ d = 0) ∧ ¬(b = 0 ∧ d = ⊤) := by
  constructor
  · -- Forward direction: if the equation holds, then we're not in the excluded cases
    intro h
    by_cases hb_top : b = ⊤
    · by_cases hd_zero : d = 0
      · simp [hb_top, hd_zero] at h
      · simp [hb_top, hd_zero]
    · -- b ≠ ⊤
      by_cases hb_zero : b = 0
      · by_cases hd_top : d = ⊤
        · -- This is exactly the second excluded case
          simp [hb_zero, hd_top] at h
        · -- Not in excluded case
          simp [hb_zero, hd_top]
      · -- b ≠ 0 and b ≠ ⊤, not in excluded cases
        simp [hb_top, hb_zero]
  · -- Reverse direction: if we're not in the excluded cases, then the equation holds
    intro h
    by_cases hb_top : b = ⊤
    · rw [hb_top]
      by_cases hd_top : d = ⊤
      · -- Both are ⊤
        rw [hd_top]
        exact inv_mul_top_top
      · -- b = ⊤, d ≠ ⊤
        by_cases hd_zero : d = 0
        · -- b = ⊤, d = 0, which is excluded
          simp [hb_top, hd_zero] at h
        · -- b = ⊤, d ≠ 0, d ≠ ⊤
          exact inv_mul_top_coe d hd_zero
    · -- b ≠ ⊤
      by_cases hd_top : d = ⊤
      · -- b ≠ ⊤, d = ⊤
        rw [hd_top]
        by_cases hb_zero : b = 0
        · -- b = 0, d = ⊤, which is excluded
          simp [hb_zero, hd_top] at h
        · -- b ≠ 0, b ≠ ⊤, d = ⊤
          exact inv_mul_coe_top b hb_zero
      · -- Both are not ⊤
        by_cases hb_zero : b = 0
        · -- b = 0, d ≠ ⊤
          rw [hb_zero]
          by_cases hd_zero : d = 0
          · -- Both are 0
            rw [hd_zero]
            simp
          · -- b = 0, d ≠ 0, d ≠ ⊤
            rw [ENNReal.inv_zero]
            have d_inv_ne_zero : d⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hd_top
            rw [ENNReal.top_mul d_inv_ne_zero]
            rw [zero_mul, ENNReal.inv_zero]
        · -- b ≠ 0, b ≠ ⊤
          by_cases hd_zero : d = 0
          · -- d = 0, b ≠ 0, b ≠ ⊤
            rw [hd_zero]
            rw [ENNReal.inv_zero]
            have b_inv_ne_zero : b⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hb_top
            rw [ENNReal.mul_top b_inv_ne_zero]
            rw [mul_zero, ENNReal.inv_zero]
          · -- Both are non-zero and not ⊤
            exact inv_mul_coe_coe hb_top hd_top

lemma top_mul_zero : (⊤ : ℝ≥0∞) * 0 = 0 := by
  rw [mul_zero]

/--
`(a / b) * (c / d) = (a * c) / (b * d)`  provided we are **not**
in the two excluded cases `(b = ⊤ ∧ d = 0)` or `(b = 0 ∧ d = ⊤)`. -/
lemma div_mul_div
    {a b c d : ℝ≥0∞}
    (h₁ : ¬ (b = ⊤ ∧ d = 0))
    (h₂ : ¬ (b = 0 ∧ d = ⊤)) :
    (a / b) * (c / d) = (a * c) / (b * d) := by
  have h : ¬(b = ⊤ ∧ d = 0) ∧ ¬(b = 0 ∧ d = ⊤) := ⟨h₁, h₂⟩
  simp [div_eq_mul_inv, mul_left_comm, mul_assoc,
        (inv_mul_cases b d).mpr h]

end ENNReal
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

/-!
# The Monty Hall Problem: Bayesian Inference with Kernels

-/

open PMF ProbabilityTheory MeasureTheory Filter Finset
open scoped ENNReal  --  we work in ℝ≥0∞ for measure values

/-! Doors and basic combinatorics -/
inductive Door : Type
| left | middle | right
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Door := ⊤
instance : StandardBorelSpace Door := inferInstance
instance : Nonempty Door := ⟨.left⟩

@[simp]
def other_door (d₁ d₂ : Door) : Door :=
  if h : d₁ = d₂ then d₁ else
  match d₁, d₂ with
  | .left,  .middle => .right
  | .left,  .right  => .middle
  | .middle, .left  => .right
  | .middle, .right => .left
  | .right, .left   => .middle
  | .right, .middle => .left
  | _, _ => d₁

lemma other_door_is_other {d₁ d₂ : Door} (h : d₁ ≠ d₂) :
    other_door d₁ d₂ ≠ d₁ ∧ other_door d₁ d₂ ≠ d₂ := by
  revert d₁ d₂ h; decide

section MontyHallBayes

abbrev CarLocation := Door
abbrev HostAction  := Door

/- Prior: uniform on three doors (as a measure). -/
noncomputable def prior : Measure CarLocation :=
  (PMF.uniformOfFintype CarLocation).toMeasure

instance : IsProbabilityMeasure prior := by
  classical
  simpa [prior] using
    (PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype _))

private lemma Kernel.ofFunOfCountable_apply [MeasurableSpace α] [MeasurableSpace β] [Countable α]
    [MeasurableSingletonClass α] (f : α → Measure β) (a : α) :
    Kernel.ofFunOfCountable f a = f a := rfl

/-- For each `p`, the subtype `{ d // d ≠ p }` is nonempty. -/
instance subtype_ne_nonempty (p : Door) : Nonempty { d : Door // d ≠ p } :=
  match p with
  | .left   => ⟨⟨.middle, by decide⟩⟩
  | .middle => ⟨⟨.left,   by decide⟩⟩
  | .right  => ⟨⟨.left,   by decide⟩⟩

/-- likelihood kernel: if the car is at `p`, host picks uniformly among the two doors ≠ `p`. -/
noncomputable def likelihood (p : Door) : Kernel CarLocation HostAction :=
  Kernel.ofFunOfCountable fun c =>
    if hc : c = p then
      -- host chooses uniformly on the two doors not equal to p
      -- Map the measure from the subtype to Door
      Measure.map (fun x : { d // d ≠ p } => x.val)
        ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure)
    else
      -- if car ≠ p, host must open the unique other door
      (PMF.pure (other_door p c)).toMeasure

instance (p : Door) : IsMarkovKernel (likelihood p) :=
⟨fun c => by
  by_cases hc : c = p
  · -- uniform case: push-forward of a uniform PMF on the subtype
    simp only [likelihood, hc, Kernel.ofFunOfCountable_apply]
    haveI : IsProbabilityMeasure ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure) :=
      PMF.toMeasure.isProbabilityMeasure _
    exact
      MeasureTheory.isProbabilityMeasure_map
        measurable_subtype_coe.aemeasurable
  · -- deterministic case: `pure` PMF is a probability measure
    simp only [likelihood, hc, Kernel.ofFunOfCountable_apply]
    exact PMF.toMeasure.isProbabilityMeasure _
⟩

/- `post` already exists in`ProbabilityTheory.posterior` -/
noncomputable def postK (p : Door) : Kernel HostAction CarLocation :=
  (likelihood p)†prior

lemma other_door_involutive {p h : Door} (h_ne_p : h ≠ p) :
    other_door p (other_door p h) = h := by
  revert p h h_ne_p; decide

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

lemma Door.card_eq_three : Fintype.card Door = 3 := by
  decide

lemma Fintype.card_subtype_ne_of_three (p : Door) : Fintype.card { d : Door // d ≠ p } = 2 := by
  rw [Fintype.card_subtype_compl, Door.card_eq_three]
  simp

namespace MontyHallBayes

variable {p h : Door} (h_ne_p : h ≠ p)

/-- The third door, different from `p` and `h`. -/
private noncomputable def o (p h : Door) : Door :=
  other_door p h

private lemma o_ne_p (p h : Door) (h_ne_p : h ≠ p) : o p h ≠ p :=
  -- we use `h_ne_p.symm : p ≠ h` so that `other_door_is_other` matches its arguments
  (other_door_is_other (h_ne_p.symm)).1

private lemma o_ne_h (p h : Door) (h_ne_p : h ≠ p) : o p h ≠ h :=
  -- same trick
  (other_door_is_other (h_ne_p.symm)).2

private lemma other_door_of_ne {p h x : Door} (hp : p ≠ h) (hx_ne_p : x ≠ p) (hx_ne_h : x ≠ h) :
    x = other_door p h := by
  revert p h x hp hx_ne_p hx_ne_h; decide

variable {p h : Door} (h_ne_p : h ≠ p)

namespace Measure

open scoped ENNReal

/--
Probability that the push-forward of the uniform measure on the subtype
`{d // d ≠ p}` assigns to the singleton `{h}`.
Since the subtype has exactly two elements, this value is `1 / 2`. -/
lemma map_uniform_subtype_singleton {p h : Door} (h_ne_p : h ≠ p) :
    (Measure.map (fun x : { d // d ≠ p } => (x : Door))
        ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure)) {h}
      = (1 : ℝ≥0∞) / 2 := by
  classical
  have h_map :
      (Measure.map (fun x : { d // d ≠ p } => (x : Door))
          ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure)) {h}
        = ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure)
            ((fun x : { d // d ≠ p } => (x : Door)) ⁻¹' {h}) := by
    simpa using
      (Measure.map_apply
          (μ := ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure))
          (f := fun x : { d // d ≠ p } => (x : Door))
          measurable_subtype_coe
          (by simp : MeasurableSet ({h} : Set Door)))
  have h_pre :
      ((fun x : { d // d ≠ p } => (x : Door)) ⁻¹' {h})
        = {⟨h, h_ne_p⟩} := by
    ext x
    simp [Set.preimage, Subtype.ext_iff, Set.mem_singleton_iff]
  have h_val :
      ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure) {⟨h, h_ne_p⟩}
        = (1 : ℝ≥0∞) / 2 := by
    have h_pmf : (PMF.uniformOfFintype { d // d ≠ p }) ⟨h, h_ne_p⟩ = (1 : ℝ≥0∞) / 2 := by
      rw [PMF.uniformOfFintype_apply]
      have : Fintype.card { d // d ≠ p } = 2 := Fintype.card_subtype_ne_of_three p
      rw [this]
      norm_num
    rw [PMF.toMeasure_apply_singleton, h_pmf]
    simp_all only [ne_eq, toMeasure_apply_fintype, uniformOfFintype_apply, Fintype.card_subtype_compl,
      Fintype.card_unique, ENNReal.natCast_sub, Nat.cast_one, one_div, inv_inj, MeasurableSet.singleton]
  simp [h_map, h_pre, h_val]

end Measure

variable {p h : Door} (h_ne_p : h ≠ p)

/-- If the car is behind door `p`, the host chooses uniformly among the two
remaining doors, so the probability that he opens `h ≠ p` is `1 / 2`. -/
lemma likelihood_at_p (h_ne_p : h ≠ p) :
    (likelihood p) p {h} = (1 : ℝ≥0∞) / 2 := by
  classical
  simpa [likelihood, Kernel.ofFunOfCountable_apply]
        using Measure.map_uniform_subtype_singleton (p := p) (h := h) h_ne_p

/-- If the car is behind door `h`, the host cannot open `h`. -/
lemma likelihood_at_h (h_ne_p : h ≠ p) :
    (likelihood p) h {h} = 0 := by
  have h_ne : other_door p h ≠ h := (other_door_is_other h_ne_p.symm).2
  rw [likelihood, Kernel.ofFunOfCountable_apply]
  simp only [h_ne_p]
  simp [PMF.pure_apply,]
  exact id (Ne.symm h_ne)

/-- If the car is behind the third door `o p h`, the host must open `h`. -/
lemma likelihood_at_o (h_ne_p : h ≠ p) :
    (likelihood p) (o p h) {h} = 1 := by
  have c_ne_p : o p h ≠ p := o_ne_p p h h_ne_p
  have h_forced : other_door p (o p h) = h := by
    rw [o, other_door_involutive h_ne_p]
  rw [likelihood,Kernel.ofFunOfCountable_apply]
  simp only [c_ne_p]
  rw [h_forced]
  have : (PMF.pure h).toMeasure {h} = 1 := by
    rw [PMF.toMeasure_apply_singleton]
    simp; exact trivial
  exact this

open MeasureTheory ProbabilityTheory

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
lemma ProbabilityTheory.comp_apply {Ω 𝓧 : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSingletonClass Ω]
  (κ : Kernel Ω 𝓧) (μ : Measure Ω)
  [IsSFiniteKernel κ]
  {s : Set 𝓧} (hs : MeasurableSet s) :
  (κ ∘ₘ μ) s = ∑ ω, μ {ω} * κ ω s := by
  rw [Measure.bind_apply hs (Kernel.aemeasurable κ)]
  rw [lintegral_fintype]
  congr with ω
  exact CommMonoid.mul_comm ((κ ω) s) (μ {ω})

/-- The universe of doors consists of exactly the three doors `{p, h, o p h}`. -/
lemma door_univ_eq_three (h_ne_p : h ≠ p) :
    (Finset.univ : Finset Door) = {p, h, o p h} := by
  ext x; simp; by_cases hxp : x = p; · left; assumption
  right; by_cases hxh : x = h; · left; assumption
  right; exact (other_door_of_ne h_ne_p.symm hxp hxh)

/-- The three doors `p`, `h`, and `o p h` are pairwise distinct. -/
lemma doors_pairwise_distinct (h_ne_p : h ≠ p) :
    p ≠ h ∧ p ≠ o p h ∧ h ≠ o p h := by
  constructor
  · exact h_ne_p.symm
  · constructor
    · exact (o_ne_p p h h_ne_p).symm
    · exact (o_ne_h p h h_ne_p).symm

/-- Each door has prior probability 1/3 under the uniform distribution. -/
lemma prior_uniform (d : Door) : prior {d} = 1 / 3 := by
  rw [prior]
  rw [PMF.toMeasure_apply_singleton (PMF.uniformOfFintype CarLocation) d]
  rw [PMF.uniformOfFintype_apply]
  simp [Door.card_eq_three]; trivial

-- Lemma for multiplying fractions
private lemma one_third_mul_one_half : (1 : ℝ≥0∞) / 3 * (1 / 2) = 1 / 6 := by
  rw [ENNReal.div_mul_div]
  norm_num; all_goals aesop

-- Lemma for converting 1/3 to 2/6
private lemma one_third_eq_two_sixths : (1 : ℝ≥0∞) / 3 = 2 / 6 := by
  rw [ENNReal.div_eq_div_iff] <;> norm_num

-- Lemma for adding fractions with same denominator
private lemma one_sixth_plus_two_sixths : (1 : ℝ≥0∞) / 6 + 2 / 6 = 3 / 6 := by
  rw [← ENNReal.add_div]; norm_num

-- Lemma for simplifying 3/6 to 1/2
private lemma three_sixths_eq_one_half : (3 : ℝ≥0∞) / 6 = 1 / 2 := by
  rw [ENNReal.div_eq_div_iff] <;> norm_num

-- Lemma for adding 1/6 + 1/3 = 1/2
private lemma one_sixth_plus_one_third : (1 : ℝ≥0∞) / 6 + 1 / 3 = 1 / 2 := by
  rw [one_third_eq_two_sixths, one_sixth_plus_two_sixths, three_sixths_eq_one_half]

lemma arithmetic_calc :
    (1 : ℝ≥0∞) / 3 * ((1 : ℝ≥0∞) / 2) +
      (1 : ℝ≥0∞) / 3 * 0 +
      (1 : ℝ≥0∞) / 3 * 1 =
    (1 : ℝ≥0∞) / 2 := by
  simp only [mul_zero, add_zero, mul_one]
  rw [one_third_mul_one_half, one_sixth_plus_one_third]

/-- The marginal probability of the host opening door `h`. -/
lemma marginal_prob_h (h_ne_p : h ≠ p) :
    ((likelihood p) ∘ₘ prior) {h} = (1 : ℝ≥0∞) / 2 := by
  classical
  rw [ProbabilityTheory.comp_apply _ _ (by simp)]
  have h_cover := door_univ_eq_three h_ne_p
  have h_doors_distinct := doors_pairwise_distinct h_ne_p
  rw [Finset.sum_univ_of_three _ h_doors_distinct.1 h_doors_distinct.2.1
        h_doors_distinct.2.2 h_cover]
  rw [likelihood_at_p h_ne_p, likelihood_at_h h_ne_p, likelihood_at_o h_ne_p]
  rw [prior_uniform p, prior_uniform h, prior_uniform (o p h)]
  exact arithmetic_calc

/- The probability of winning by switching doors. -/
theorem switch_wins_prob_bayes (p h : Door) (h_ne_p : h ≠ p) :
    (postK p h) {other_door p h} = (2 : ℝ≥0∞) / 3 := by
  classical
  set o : Door := other_door p h with ho
  -- The denominator in Bayes’ formula is non-zero
  have hpos : ((likelihood p) ∘ₘ prior) {h} ≠ 0 := by
    rw [marginal_prob_h h_ne_p]
    norm_num
  -- Bayes’ rule specialised to singletons
  have post_eq :
      (postK p h) {o} =
        (prior {o} * (likelihood p) o {h}) /
          ((likelihood p) ∘ₘ prior) {h} := by
    rw [postK]
    exact posterior_apply_singleton (likelihood p) prior h o hpos
  -- The prior is uniform
  have prior_o : prior {o} = (1 : ℝ≥0∞) / 3 := by
    simpa using prior_uniform o
  have h_post : (postK p h) {o} = (2 : ℝ≥0∞) / 3 := by
    have lik_o : (likelihood p) o {h} = 1 := by
      simpa [ho] using likelihood_at_o (p := p) (h := h) h_ne_p
    have : (prior {o} * (likelihood p) o {h}) /
        ((likelihood p) ∘ₘ prior) {h} = (2 : ℝ≥0∞) / 3 := by
      simp [prior_o, lik_o, marginal_prob_h h_ne_p,
            div_eq_mul_inv, mul_comm]
    simpa [post_eq] using this
  simpa [ho] using h_post

end MontyHallBayes

