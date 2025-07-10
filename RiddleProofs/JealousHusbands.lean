import RiddleProofs.JealousHusbands.Statement
import RiddleProofs.JealousHusbands.Moves
import RiddleProofs.JealousHusbands.Search
import RiddleProofs.JealousHusbands.Solution
import RiddleProofs.JealousHusbands.JealousMathematician


/-!
# The Jealous Husbands River Crossing Puzzle

```
Left Bank                    River                    Right Bank
-----------------------------------------------------------------
H₁ W₁ H₂ W₂ H₃ W₃    [=======🚤======]               (empty)
```

**The goal**: Move all 6 people (3 couples) to the right bank while respecting jealousy constraints.

**Learning goals for this formalization**
- **State space modeling**: Representing puzzle states as data structures
- **Constraint satisfaction**: Encoding safety rules as boolean predicates
- **Graph search algorithms**: Using BFS to find optimal solutions
- **Proof by computation**: Verifying solutions through `native_decide`
- **Custom syntax**: Creating domain-specific notation for moves

## Mathematical structure

This puzzle is a classic **constraint satisfaction problem** that can be modeled as:
- **State space**: All possible arrangements of people and boat positions
- **Transitions**: Valid moves that respect boat capacity and social rules
- **Goal condition**: Reaching the target state where everyone is on the right bank
- **Constraints**: The "jealousy" rules that eliminate unsafe states

The solution uses **breadth-first search** to find the optimal 11-move solution,
demonstrating how algorithmic problem-solving translates into formal verification.

## Module structure

- `Statement.lean`: Core types, state representation, and safety constraints
- `Moves.lean`: Move definitions, validation logic, and custom syntax
- `Search.lean`: BFS algorithm implementation for solution discovery
- `Solution.lean`: Hardcoded optimal solution with correctness proof
- `JealousMathematician.lean`: Alternative puzzle variant with mathematicians

## Why this puzzle matters

The jealous husbands problem illustrates how **real-world constraints** (social rules)
can be encoded as **mathematical predicates**, making it perfect for demonstrating
how proof assistants handle both algorithmic reasoning and formal verification.
-/
