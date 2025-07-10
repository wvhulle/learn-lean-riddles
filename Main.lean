import RiddleProofs

/-!
# Riddle Proofs Workshop: Learn Lean 4 Through Mathematical Puzzles

A hands-on introduction to formal verification using classic mathematical puzzles.
Perfect for software engineers who want to learn proof assistants!

## Getting Started

**To run this program**: `lake exe riddle-proofs`
**To build the project**: `lake build`
**To explore proofs**: Open .lean files in VS Code with the Lean 4 extension

## Learning Path by Difficulty

### 🟢 Beginner Puzzles
Start here if you're new to Lean or proof assistants:

**MontyHall/Statement.lean** 📊
- **Lean concepts**: Basic probability reasoning, decidable propositions
- **Math concepts**: Conditional probability, Bayesian thinking
- **Skills learned**: Writing simple proofs, working with rationals

**BirthdayProblem.lean** 🎂
- **Lean concepts**: Finite types, cardinality functions, `decide` tactic
- **Math concepts**: Combinatorics, probability paradoxes, injective functions
- **Skills learned**: Computational proofs, understanding why intuition fails

### 🟡 Intermediate Puzzles
For those comfortable with basic Lean syntax:

**BlueEyedIslanders.lean** 👁️
- **Lean concepts**: Inductive definitions, finite sets, decidable predicates
- **Math concepts**: Epistemic logic, common knowledge, inductive reasoning
- **Skills learned**: Modeling knowledge and belief, working with finite structures

**JealousHusbands.lean** 🚤
- **Lean concepts**: State machines, custom syntax, BFS algorithms
- **Math concepts**: Graph search, constraint satisfaction problems
- **Skills learned**: Encoding real-world constraints as logical predicates

### 🔴 Advanced Puzzles
For experienced users ready for sophisticated mathematics:

**LightsOut.lean** 💡
- **Lean concepts**: Group theory, linear algebra over finite fields, advanced tactics
- **Math concepts**: Abelian groups, vector spaces, kernel computations
- **Skills learned**: Abstract algebra, connecting puzzles to deep mathematical structures

## Workshop Philosophy

Each puzzle demonstrates how **real-world intuition** translates into **formal mathematical reasoning**.
You'll learn that proof assistants aren't just for abstract math - they're powerful tools
for modeling and verifying any system with clear logical rules.

**Key insight**: If you can explain a puzzle's solution to a human, you can teach Lean to verify it!
-/

def main : IO Unit := do
  IO.println "Welcome to the Riddle Proofs Workshop!"
  IO.println "Explore the RiddleProofs/ directory to see formalized puzzles."
  IO.println "Each file contains detailed explanations and learning objectives."
