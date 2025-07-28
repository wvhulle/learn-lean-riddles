import RiddleProofs.MontyHall.Statement
import RiddleProofs.MontyHall.MeasureTheory
import ENNRealArith

/-! Written by Matteo Cipollina

Edited by Willem Vanhulle

This file contains the Monty Hall specific computations and proof of the main theorem.
-/

open PMF ProbabilityTheory MeasureTheory Filter Finset
open scoped ENNReal


/-! ## Monty Hall Specific Definitions -/

instance : StandardBorelSpace Door := inferInstance

/- Prior: uniform on three doors (as a measure). -/
noncomputable def prior : Measure CarLocation :=
  (PMF.uniformOfFintype CarLocation).toMeasure

instance : IsProbabilityMeasure prior := by
  classical
  simpa [prior] using
    (PMF.toMeasure.isProbabilityMeasure (PMF.uniformOfFintype _))

/-- For each `p`, the subtype `{ d // d ≠ p }` is nonempty. -/
instance subtype_ne_nonempty (p : Door) : Nonempty { d : Door // d ≠ p } :=
  match p with
  | .left   => ⟨⟨.middle, by decide⟩⟩
  | .middle => ⟨⟨.left,   by decide⟩⟩
  | .right  => ⟨⟨.left,   by decide⟩⟩

/-- likelihood kernel: if the car is at `p`, host picks uniformly among the two doors ≠ `p`. -/
noncomputable def likelihood (p : Door) : Kernel CarLocation HostAction :=
  Kernel.ofFunOfCountable fun c =>
    if  c = p then
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
    simp only [likelihood, hc, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
    haveI : IsProbabilityMeasure ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure) :=
      PMF.toMeasure.isProbabilityMeasure _
    exact
      MeasureTheory.isProbabilityMeasure_map
        measurable_subtype_coe.aemeasurable
  · -- deterministic case: `pure` PMF is a probability measure
    simp only [likelihood, hc, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
    exact PMF.toMeasure.isProbabilityMeasure _
⟩

/- Posterior kernel using Bayesian inference -/
noncomputable def postK (p : Door) : Kernel HostAction CarLocation :=
  (likelihood p)†prior

section MontyHallBayes

lemma other_door_involutive {p h : Door} (h_ne_p : h ≠ p) :
    other_door p (other_door p h) = h := by
  cases p <;> cases h <;> simp [other_door]

open scoped BigOperators


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
  simpa [likelihood, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
        using Measure.map_uniform_subtype_singleton (p := p) (h := h) h_ne_p

/-- If the car is behind door `h`, the host cannot open `h`. -/
lemma likelihood_at_h (h_ne_p : h ≠ p) :
    (likelihood p) h {h} = 0 := by
  have h_ne : other_door p h ≠ h := (other_door_is_other h_ne_p.symm).2
  rw [likelihood, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
  simp only [h_ne_p]
  simp [PMF.pure_apply,]
  exact id (Ne.symm h_ne)

/-- If the car is behind the third door `o p h`, the host must open `h`. -/
lemma likelihood_at_o (h_ne_p : h ≠ p) :
    (likelihood p) (o p h) {h} = 1 := by
  have c_ne_p : o p h ≠ p := o_ne_p p h h_ne_p
  have h_forced : other_door p (o p h) = h := by
    rw [o, other_door_involutive h_ne_p]
  rw [likelihood,ProbabilityTheory.Kernel.ofFunOfCountable_apply]
  simp only [c_ne_p]
  rw [h_forced]
  have : (PMF.pure h).toMeasure {h} = 1 := by
    rw [PMF.toMeasure_apply_singleton]
    simp; exact trivial
  exact this

open MeasureTheory ProbabilityTheory


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



/-- The marginal probability of the host opening door `h`. -/
lemma marginal_prob_h (h_ne_p : h ≠ p) :
    ((likelihood p) ∘ₘ prior) {h} = (1 : ℝ≥0∞) / 2 := by
  classical
  rw [ProbabilityTheory.comp_apply _ _ (by simp)]
  have h_cover := door_univ_eq_three h_ne_p
  have h_doors_distinct := doors_pairwise_distinct h_ne_p
  rw [ProbabilityTheory.Finset.sum_univ_of_three _ h_doors_distinct.1 h_doors_distinct.2.1
        h_doors_distinct.2.2 h_cover]
  rw [likelihood_at_p h_ne_p, likelihood_at_h h_ne_p, likelihood_at_o h_ne_p]
  rw [prior_uniform p, prior_uniform h, prior_uniform (o p h)]
  eq_as_reals

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
