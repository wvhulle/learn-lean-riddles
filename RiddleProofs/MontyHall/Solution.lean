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

variable {p h c d : Door}

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

/-- Definition of a kernel representing conditional distributions of host actions given car locations. -/
noncomputable def likelihood (p : Door) : Kernel CarLocation HostAction :=
  /- A kernel κ : α -> Measure β assigns a measure on β for any a ∈ α.
  In the context of probability theory, a is the value of a random variable X and κ(a) represents the conditional probability distribution of some random variable Y given X = a. -/
  Kernel.ofFunOfCountable fun c =>
    if  c = p then
      -- host chooses uniformly on the two doors not equal to p
      -- Map the measure from the subtype to HostAction
      let f : { d // d ≠ p } → Door :=  λ x : { d // d ≠ p } => x.val -- push-forward function
      Measure.map f -- Computes push-forward of measure on codomain `HostAction`.
        ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure)
        -- `Measure.map` works by defining with the inverse map (f₊μ)(A) = μ(f⁻¹(A)).
        -- _Remark_: `f` is not necessarily surjective, but should be measurable
    else
      -- if c ≠ p, host must open the unique other door
      (PMF.pure (remaining_door p c)).toMeasure
      -- `PMF.pure` creates a PMF that assigns 1 to the singleton set `{remaining_door p c}`

/- The kernel `likelihood` must yield an actual probability measure for every `p` door and sum to one. This requirement is captured by the `IsMarkovKernel` type class. -/
instance (p : Door) : IsMarkovKernel (likelihood p) :=
-- For any car location, we prove that `likelihood(p)(c)` is a probability measure over `HostAction`.
⟨fun c => by
  -- Consider each possible car location.
  by_cases p_eq_c : c = p
  · -- uniform case: push-forward of a uniform PMF on the subtype
    show IsProbabilityMeasure ((likelihood p) c)
    simp only [likelihood, p_eq_c, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
    -- We evaluate the kernel at `likelihood(p)(c)` with `ofFunOfCountable_apply`.
    haveI : IsProbabilityMeasure ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure) :=
      PMF.toMeasure.isProbabilityMeasure _ -- We can leave out `(PMF.uniformOfFintype { d // d ≠ p })`.
    exact
      -- If you push-forward a probability measure, it remains a probability measure.
      MeasureTheory.isProbabilityMeasure_map
        /- Required condition: the push-forward function `f` is measurable.
        A slightly more general version of measurability is "almost everywhere measurable" (`aemeasurable`). -/
        measurable_subtype_coe.aemeasurable
  · -- deterministic case: `pure` PMF is a probability measure
    show IsProbabilityMeasure ((likelihood p) c)
    simp only [likelihood, p_eq_c, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
    -- We evaluate the kernel at `likelihood(p)(c)` with `ofFunOfCountable_apply`.
    exact PMF.toMeasure.isProbabilityMeasure _
⟩


/- The \dagger computes an application of the `posterior` operator on kernel `likelihood p` with respect to prior distribution of cars in `prior`.

It works by applying a generalized version of the Bayes theorem that reduces to the more familiar discrete form of Bayes' theorem:

P(Car=X | Host=Y) = P(Host=Y | Car=X) × P(Car=X) / P(Host=Y)

Where the marginal probability is computed like:

P(Host=Y) = Σ_X P(Host=Y | Car=X) × P(Car=X)

-/
noncomputable def postK (p : Door) : Kernel HostAction CarLocation :=
  (likelihood p)†prior



lemma Fintype.card_subtype_ne_of_three (p : Door) : Fintype.card { d : Door // d ≠ p } = 2 := by
  rw [Fintype.card_subtype_compl, Door.card_eq_three]
  simp

private lemma remaining_ne_p (p h : Door) (h_ne_p : h ≠ p) : remaining_door p h ≠ p :=
  -- Use `h_ne_p.symm : p ≠ h` so that `other_door_is_other` matches its arguments
  (other_door_is_other (h_ne_p.symm)).1

private lemma remaining_ne_h (p h : Door) (h_ne_p : h ≠ p) : remaining_door p h ≠ h :=

  (other_door_is_other (h_ne_p.symm)).2

private lemma other_door_of_ne {p h x : Door} (hp : p ≠ h) (hx_ne_p : x ≠ p) (hx_ne_h : x ≠ h) :
    x = remaining_door p h := by
  revert p h x hp hx_ne_p hx_ne_h; decide

/--
Probability that the push-forward of the uniform measure on the subtype
`{d // d ≠ p}` assigns to the singleton `{h}`.
Since the subtype has exactly two elements, this value is `1 / 2`. -/
lemma map_uniform_subtype_singleton {p h : Door} (h_ne_p : h ≠ p) :
    (Measure.map (fun x : { d // d ≠ p } => (x : Door))
        -- This lemma is only used when `pick = car` and the host has to choose uniformly between the two remaining doors.
        ((PMF.uniformOfFintype { d // d ≠ p }).toMeasure)) {h}
      = (1 : ℝ≥0∞) / 2 := by
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



/-- If the car is behind door `p`, the host chooses uniformly among the two
remaining doors, so the probability that he opens `h ≠ p` is `1 / 2`. -/
lemma likelihood_at_when_part_pick_car (h_ne_p : h ≠ p) :
    (likelihood p) p {h} = (1 : ℝ≥0∞) / 2 := by
  classical
  simpa [likelihood, ProbabilityTheory.Kernel.ofFunOfCountable_apply]
        using map_uniform_subtype_singleton (p := p) (h := h) h_ne_p

/-- If the car is behind door `h`, the host cannot open `h`. -/
lemma likelihood_h_when_car_at_h (h_ne_p : h ≠ p) :
    (likelihood p) h {h} = 0 := by
  have h_ne : remaining_door p h ≠ h := (other_door_is_other h_ne_p.symm).2
  rw [likelihood, ProbabilityTheory.Kernel.ofFunOfCountable_apply] -- Evaluate simple kernel.
  simp only [h_ne_p]
  simp [PMF.pure_apply,] -- Apply a PMF defined on a singleton set.
  exact id (Ne.symm h_ne)


/-- If the car is behind the third door `remaining_door p h`, the host must open `h`. -/
lemma likelihood_at_h_when_part_not_pick_car (h_ne_p : h ≠ p) :
    (likelihood p) (remaining_door p h) {h} = 1 := by
  have c_ne_p : remaining_door p h ≠ p := remaining_ne_p p h h_ne_p
  have h_forced : remaining_door p (remaining_door p h) = h := by
    rw [other_door_involutive h_ne_p]
  rw [likelihood,ProbabilityTheory.Kernel.ofFunOfCountable_apply]
  simp only [c_ne_p]
  rw [h_forced]
  have : (PMF.pure h).toMeasure {h} = 1 := by
    rw [PMF.toMeasure_apply_singleton]
    simp; exact trivial
  exact this

open MeasureTheory ProbabilityTheory


/-- The universe of doors consists of exactly the three doors `{p, h, remaining_door p h}`. -/
lemma door_univ_eq_three (h_ne_p : h ≠ p) :
    (Finset.univ : Finset Door) = {p, h, remaining_door p h} := by
  ext x; simp; by_cases hxp : x = p; · left; assumption
  right; by_cases hxh : x = h; · left; assumption
  right; exact (other_door_of_ne h_ne_p.symm hxp hxh)

/-- The three doors `p`, `h`, and `remaining_door p h` are pairwise distinct. -/
lemma doors_pairwise_distinct (h_ne_p : h ≠ p) :
    p ≠ h ∧ p ≠ remaining_door p h ∧ h ≠ remaining_door p h := by
  constructor
  · exact h_ne_p.symm
  · constructor
    · exact (remaining_ne_p p h h_ne_p).symm
    · exact (remaining_ne_h p h h_ne_p).symm

/-- Without host evidence, every door is equally likely to have car for participant. -/
lemma eval_uniform_prior (d : Door) : prior {d} = 1 / 3 := by
  rw [prior]
  rw [PMF.toMeasure_apply_singleton (PMF.uniformOfFintype CarLocation) d]
  rw [PMF.uniformOfFintype_apply]
  simp [Door.card_eq_three]; trivial





/-
First, it is important to understand the concept of the composition of a kernel with a measure.

Given:
- μ : Measure α (a measure on space α)
- κ : Kernel α β (a kernel from α to β)

The composition κ ∘ₘ μ : Measure β is defined as:
(κ ∘ₘ μ)(B) = ∫_{a ∈ α} κ(a)(B) dμ(a)
where κ(a)(B) is the measure that κ(a) assigns to set B ⊆ β

In our Monty Hall context:
- α = CarLocation (the space/type)
- a ranges over specific car locations (door1, door2, door3)
- μ = prior (uniform measure on car locations)
- κ = likelihood pick (kernel giving host behavior for each car location)

Integrate over all possible car locations, weighted by the prior probability of each location.

-/


/--
What is the probability that the host will open door `h`.
-/
lemma marginal_prob_h (h_ne_p : h ≠ p) :
    ((likelihood p) ∘ₘ prior) {h} = (1 : ℝ≥0∞) / 2 := by
  /-
  We first apply a general measure-theoretic version of law of total probability `comp_apply`. In a discrete probability space this becomes:
  Σ_car P(h opens | car location) × P(car location)
  -/
  rw [ProbabilityTheory.comp_apply _ _ (by simp)]
  have h_cover := door_univ_eq_three h_ne_p
  have h_doors_distinct := doors_pairwise_distinct h_ne_p
  rw [ProbabilityTheory.Finset.sum_univ_of_three _ h_doors_distinct.1 h_doors_distinct.2.1
        h_doors_distinct.2.2 h_cover]
  show
    prior {p} * ((likelihood p) p) {h} +
    prior {h} * ((likelihood p) h) {h} +
    prior {remaining_door p h} * ((likelihood p) (remaining_door p h)) {h}
       = 1 / 2
  -- Rewrite each term in the sum:
  -- Case 1: Car at picked door → 1/3 × 1/2
  rw [likelihood_at_when_part_pick_car h_ne_p, eval_uniform_prior p]
  -- Case 2: Car at host door → 1/3 × 0
  rw [likelihood_h_when_car_at_h h_ne_p, eval_uniform_prior h]
  -- Case 3: Car at remaining door → 1/3 × 1
  rw [likelihood_at_h_when_part_not_pick_car h_ne_p, eval_uniform_prior (remaining_door p h)]
  eq_as_reals

/- The probability of winning by switching doors. -/
theorem switch_wins_prob_bayes (p h : Door) (h_ne_p : h ≠ p) :
    (postK p h) {remaining_door p h} = (2 : ℝ≥0∞) / 3 := by
  set o : Door := remaining_door p h with ho
  -- The denominator in Bayes’ formula is non-zero
  have hpos : ((likelihood p) ∘ₘ prior) {h} ≠ 0 := by
    rw [marginal_prob_h h_ne_p]
    norm_num
  -- Bayes’ rule specialised to singletons
  -- Direct calculation: (1/3 * 1) / (1/2) = 2/3
  calc (postK p h) {remaining_door p h}
    = (postK p h) {o} := by rw [ho]
    _ = (prior {o} * (likelihood p) o {h}) / ((likelihood p) ∘ₘ prior) {h} := by
      rw [postK]
      exact posterior_apply_singleton (likelihood p) prior h o hpos
    _ = ((1 : ℝ≥0∞) / 3 * (likelihood p) o {h}) / ((1 : ℝ≥0∞) / 2) := by
      rw [eval_uniform_prior, marginal_prob_h h_ne_p]
    _ = ((1 : ℝ≥0∞) / 3 * 1) / ((1 : ℝ≥0∞) / 2) := by
      rw [likelihood_at_h_when_part_not_pick_car h_ne_p]
    _ = (2 : ℝ≥0∞) / 3 := by
      eq_as_reals
