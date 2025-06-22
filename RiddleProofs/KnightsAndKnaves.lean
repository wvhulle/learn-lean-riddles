import Std

/-!
# The Knights and Knaves Puzzle

**Problem**: On an island, knights always tell the truth, knaves always lie.
You meet A and B who say:
- A: "B is a knave"
- B: "We are of opposite types"

What are A and B?

**Solution**: Model all possibilities, check which are consistent.
-/

/-- The two people in our puzzle -/
inductive Person | A | B deriving DecidableEq, Repr

/-- Knight (truth-teller) or knave (liar) -/
inductive Role | knight | knave deriving DecidableEq, Repr

open Person Role

/-- A world assigns roles to people -/
def World := Person → Role

/-- Helper to create a world from A's and B's roles -/
def mkWorld (roleA roleB : Role) : World :=
  fun p => match p with | Person.A => roleA | Person.B => roleB

/-- All possible role combinations -/
def all_role_pairs : List (Role × Role) :=
  [(knight, knight), (knight, knave), (knave, knight), (knave, knave)]

/-- All 4 possible worlds -/
def all_worlds : List World :=
  all_role_pairs.map (fun (rA, rB) => mkWorld rA rB)

/-- Check if both statements are consistent in world w -/
def statements (w : World) : Bool :=
  let a_says := w Person.B = knave  -- A says "B is a knave"
  let b_says := w Person.A ≠ w Person.B  -- B says "We are opposite types"
  match w Person.A, w Person.B with
  | knight, knight => a_says ∧ b_says
  | knight, knave  => a_says ∧ ¬b_says
  | knave, knight  => ¬a_says ∧ b_says
  | knave, knave   => ¬a_says ∧ ¬b_says

/-- Find consistent worlds -/
def solutions : List World := all_worlds.filter statements

-- The answer: only one consistent world
#eval solutions.map fun w => (w Person.A, w Person.B)

-- Alternative: show all worlds with their consistency status
#eval all_worlds.map fun w => ((w Person.A, w Person.B), statements w)

/-!
## Step-by-Step Analysis

Let's work through each possible world to see why only one works:

**World 1: A = knight, B = knight**
- A (knight) says "B is a knave": Since A tells truth, B must be knave. Contradiction! (B is knight)
- This world is inconsistent.

**World 2: A = knight, B = knave**
- A (knight) says "B is a knave": Since A tells truth, B is knave ✓
- B (knave) says "We are opposite types": Since B lies, we are NOT opposite. But A=knight, B=knave ARE opposite. Contradiction!
- This world is inconsistent.

**World 3: A = knave, B = knight**
- A (knave) says "B is a knave": Since A lies, B is NOT a knave, so B is knight ✓
- B (knight) says "We are opposite types": Since B tells truth, A and B ARE opposite types ✓
- This world is consistent! ✓✓

**World 4: A = knave, B = knave**
- A (knave) says "B is a knave": Since A lies, B is NOT a knave. Contradiction! (B is knave)
- This world is inconsistent.

**Conclusion**: Only World 3 works, so A is a knave and B is a knight.
-/

/-!
## Verification: Check Each World

Let's verify our analysis by checking all four possible worlds:
-/

-- Check if statements are consistent for each world using modern syntax
#eval all_role_pairs.map fun (rA, rB) =>
  let w := mkWorld rA rB
  ((rA, rB), statements w)

-- Alternative: show the reasoning for each world
def analyze_world (roleA roleB : Role) : String :=
  let w := mkWorld roleA roleB
  let consistent := statements w
  s!"World: A={repr roleA}, B={repr roleB} → Consistent: {consistent}"

#eval String.join (all_role_pairs.map fun (rA, rB) =>
  analyze_world rA rB ++ "\n")

/-!
## Summary

This demonstrates computational logic solving:
1. **Model** the problem with types and constraints
2. **Enumerate** all possibilities systematically
3. **Filter** consistent solutions
4. **Verify** the unique answer: A = knave, B = knight

The approach scales to much larger Knights and Knaves puzzles!
-/

/-- The unique solution -/
def the_solution : World := mkWorld knave knight

/-- Verify there's exactly one solution -/
example : solutions.length = 1 := by decide

/-- Verify A is a knave and B is a knight in the solution -/
example : the_solution Person.A = knave ∧ the_solution Person.B = knight := by decide

/-- Show that the solution satisfies the constraints -/
example : statements the_solution = true := by decide
