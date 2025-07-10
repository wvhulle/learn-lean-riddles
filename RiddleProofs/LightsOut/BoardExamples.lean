import RiddleProofs.LightsOut.Statement

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

/-- The correct solution for 2×2 single light: press buttons (0,0), (0,1), (1,0)
    Why this works: Each button toggles overlapping regions, and the overlaps
    cancel out, leaving only the original light toggled off -/
theorem example2x2_solution :
  applyButtons example2x2 ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) = allOff := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [applyButtons, effect, isAffected,
    areAdjacent, example2x2, allOff]
    simp
    decide }

/-- 2×2 puzzle is solvable via linear algebra -/
theorem example2x2_solvable : isSolvable example2x2 := by
  -- Solution: press (0,0), (0,1), (1,0)
  use fun btn => if btn ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Button 2 2)) then 1 else 0
  simp [applySelection, fromVector, buttonMatrix, toVector]
  funext i j
  fin_cases i <;> fin_cases j <;>
  { simp only [example2x2, allOff, effect, isAffected,
    areAdjacent]
    decide }

def cross3x3 : LightState 3 3 := Matrix.of fun i j =>
  if i = 1 || j = 1 then 1 else 0

instance : Inhabited (LightState 3 3) := ⟨cross3x3⟩

def example3x3Cross : LightState 3 3 :=
  Matrix.of fun i j =>
    if (i = 1) ∨ (j = 1) then 1 else 0

/-- All-on 3×3 solved by pressing corners -/
def allOn3x3_solution : LightState 3 3 → LightState 3 3 :=
  fun initial =>
    let corners : Finset (Button 3 3) := {(0, 0), (0, 2), (2, 0), (2, 2)}
    applyButtons initial corners
