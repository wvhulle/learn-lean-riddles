import RiddleProofs.LightsOut.Statement

section TwoByTwo

/-- A simple 2×2 puzzle: single light at top-left corner (0,0)
    Visual representation:
    ┌───┬───┐
    │ ● │ ○ │
    ├───┼───┤
    │ ○ │ ○ │
    └───┴───┘
-/
def example2x2 : LightState 2 2 :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- What happens when we press the button at (0,0)?
    It toggles itself and its neighbors (0,1) and (1,0)
    Result:
    ┌───┬───┐
    │ ○ │ ● │  -- (0,0) toggled off, (0,1) toggled on
    ├───┼───┤
    │ ● │ ○ │  -- (1,0) toggled on, (1,1) unaffected
    └───┴───┘
-/
theorem example2x2_press_00 :
  pressAt example2x2 0 0 = Matrix.of fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0 := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { rw [pressAt, press, example2x2, effect, Matrix.add_apply, Matrix.of_apply, Matrix.of_apply]
    simp only [isAffected, areAdjacent]
    decide }

theorem example2x2_solution :
  applyButtons example2x2 ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) = allOff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [applyButtons, effect, isAffected,
    areAdjacent, example2x2, allOff]
    simp
    decide }

theorem example2x2_solvable : isSolvable example2x2 := by
  use fun btn => if btn ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) then 1 else 0
  simp [applySelection, fromVector, buttonMatrix, toVector]
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [example2x2, allOff, effect, isAffected, areAdjacent]
    decide }

end TwoByTwo


section ThreeByThree

/-- 3×3 cross pattern: lights on in middle row and column
    Visual representation:
    ┌───┬───┬───┐
    │ ○ │ ● │ ○ │
    ├───┼───┼───┤
    │ ● │ ● │ ● │
    ├───┼───┼───┤
    │ ○ │ ● │ ○ │
    └───┴───┴───┘
-/
def cross3x3 : LightState 3 3 :=
  Matrix.of fun i j => if i = 1 ∨ j = 1 then 1 else 0

theorem cross3x3_solvable : isSolvable cross3x3 := by
  use fun btn => if btn = (1, 1) then 1 else 0
  simp [applySelection, fromVector, buttonMatrix, toVector]
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [cross3x3, allOff, effect, isAffected, areAdjacent]
    decide }


end ThreeByThree


/-!
## Example Solutions

### 2×2 Examples
- Single light at corner: Press 3 buttons in L-shape
- Solution exploits symmetry and overlapping effects

### 3×3 Examples  
- Cross pattern: Press center button only
- All lights on: Press all 4 corners
- Corner solutions work due to non-overlapping effects

## Challenges
- Implement brute-force solution finder
- Characterize solvable vs unsolvable configurations
- Explore larger grid patterns
-/
