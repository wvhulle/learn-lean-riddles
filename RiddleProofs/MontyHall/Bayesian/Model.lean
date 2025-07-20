import RiddleProofs.MontyHall.Basic

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ENNRealArith

open ENNReal

-- Computes P ( car )
noncomputable def car_prior : PMF Door :=
  PMF.ofFintype (fun _ => (1 : ENNReal) / 3) (by
    simp only [Finset.sum_const, Finset.card_univ]
    rw [door_card]
    rw [<- toReal_eq_one_iff]
    eq_as_reals)

-- Given where the car is, what are the probabilities of (pick, host) pairs?
noncomputable def raw_likelihood (car pick host : Door) : ENNReal :=
  if host = car ∨ host = pick then 0    -- Invalid configurations
  else if car = pick then
    -- Contestant picks the car: host uniformly chooses from 2 remaining doors
    -- P(pick = car | car) = 1/3 (uniform pick)
    -- P(host | pick = car, car) = 1/2 (2 valid doors)
    -- So P(pick, host | car) = 1/3 × 1/2 = 1/6
    (1 : ENNReal) / 6
  else
    -- Contestant picks a goat: host must open the other goat door
    -- P(pick ≠ car | car) = 1/3 for each of the 2 goat doors since contestant has no idea at first where the car is
    -- P(host | pick ≠ car, car) = 1 (forced choice)
    -- So P(pick, host | car) = 1/3 × 1 = 1/3
    (1 : ENNReal) / 3


lemma likelihood_val_sum_one (car : Door) :
  ∑ p : Door × Door, raw_likelihood car p.1 p.2 = 1 := by

  simp only [equivalence_door_repr]
  simp only [door_enumeration]
  simp only [door_tuples]
  simp [Finset.sum_product]
  simp only [fin_to_door]
  simp only [raw_likelihood]
  cases car
  case left =>
     split_ifs <;> (first | contradiction | eq_as_reals)
  case middle =>
    split_ifs <;> (first | contradiction | eq_as_reals)
  case right =>
    split_ifs <;> (first | contradiction | eq_as_reals)

-- Likelihood function: P((pick, host) | car)
noncomputable def monty_likelihood (car : Door) : PMF (Door × Door) :=
  PMF.ofFintype (fun (pick, host) => raw_likelihood car pick host)
  (likelihood_val_sum_one car)
