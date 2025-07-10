import RiddleProofs.MontyHall.Statement

/-!
# Monty Hall Problem: Enumeration approach

This file takes a computational approach to the Monty Hall problem by enumerating 
all possible game scenarios and counting outcomes.

**Key insight**: Since there are only 3 doors and 3 choices for each variable
(car location, initial pick, host's choice), we can enumerate all 27 possible
games and count how many lead to wins for each strategy.

**Learning goals**:
- Understand how to enumerate finite types in Lean
- See how to prove equivalences between different representations
- Learn about injective functions and their properties
- Practice with computational proofs using decidable types
-/

open Door

@[ext]
theorem Game.ext {g₁ g₂ : Game} : g₁.car = g₂.car → g₁.pick = g₂.pick →
    g₁.host = g₂.host → g₁ = g₂ := by
  intro h₁ h₂ h₃
  cases g₁ with | mk c₁ p₁ h₁ =>
  cases g₂ with | mk c₂ p₂ h₂ =>
  simp at h₁ h₂ h₃
  simp [h₁, h₂, h₃]

-- Convert numbers 0,1,2 to doors (left, middle, right)
def fin_to_door (f : Fin 3) : Door :=
  match f with
  | 0 => left
  | 1 => middle
  | 2 => right

lemma fin_to_door_injective : Function.Injective fin_to_door := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [fin_to_door] at h <;> rfl

-- All possible triples (car_location, initial_pick, host_choice)
-- This gives us 3 × 3 × 3 = 27 different scenarios
def pairs := ({0, 1, 2} ×ˢ {0, 1, 2} ×ˢ {0, 1, 2} : Finset (Fin 3 × Fin 3 × Fin 3) )

-- Systematically enumerate all possible Monty Hall games
def game_enumeration : Finset Game :=
  pairs.map ⟨(fun x => match x with
    | (car_idx, pick_idx, host_idx) =>
      {car := fin_to_door car_idx, pick := fin_to_door pick_idx, host := fin_to_door host_idx}),
    by
      intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
      simp at h
      have h1 : a1 = b1 := fin_to_door_injective h.1
      have h2 : a2 = b2 := fin_to_door_injective h.2.1
      have h3 : a3 = b3 := fin_to_door_injective h.2.2
      simp [h1, h2, h3]⟩

theorem equivalence_game_repr : (Finset.univ : Finset Game) = game_enumeration := by
  rfl

instance fin_outcome : Finset Game :=
  Finset.univ
