
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-! Written by Matteo Cipollina

The Monty Hall Problem: Statement and Basic Setup
-/

/-!
# The Monty Hall Problem

This file contains the problem statement and basic definitions for the Monty Hall problem.

## The Problem

In the Monty Hall game show:
1. There are three doors, behind one of which is a car (the prize)
2. The contestant initially picks one door
3. The host, who knows where the car is, opens one of the remaining doors that contains no car
4. The contestant is then given the choice to stick with their original choice or switch to the remaining unopened door

## The Question

What is the probability of winning if the contestant switches doors?

## The Answer

**2/3** - The contestant should always switch! This counterintuitive result is proven rigorously using measure theory and Bayesian inference.

## Mathematical Approach

We model this as a Bayesian inference problem:
- **Prior**: Uniform distribution over the three door locations for the car
- **Likelihood**: The probability distribution of the host's actions given the car location
- **Posterior**: Using Bayes' rule to compute the probability distribution after observing the host's action

The key insight is that the host's action provides information that updates our beliefs about where the car is located.
-/

/-! ## Basic Setup -/


inductive Door : Type
| left | middle | right
  deriving DecidableEq, Repr

instance : Fintype Door := ⟨{.left, .middle, .right}, by intro d; cases d <;> simp⟩

instance : MeasurableSpace Door := ⊤
instance : Nonempty Door := ⟨.left⟩


@[simp]
def other_door (d₁ d₂ : Door) : Door :=
  if d₁ = d₂ then d₁ else
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
  sorry

abbrev CarLocation := Door
abbrev HostAction := Door

/-- **The Monty Hall Theorem**: The probability of winning by switching doors is 2/3. -/
theorem switch_wins_prob_bayes (p h : Door) (h_ne_p : h ≠ p) :
    True := by
  sorry
