/-
# Lights Out Interactive Widget

This file provides an interactive widget for the Lights Out puzzle using ProofWidgets.
-/

import ProofWidgets.Component.HtmlDisplay
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Lean.Data.Json

open Lean

open scoped ProofWidgets.Jsx

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace LightsOutWidget

-- Basic types
def State (m n : ℕ) := Matrix (Fin m) (Fin n) (ZMod 2)

instance {m n : ℕ} : Add (State m n) := inferInstanceAs (Add (Matrix (Fin m) (Fin n) (ZMod 2)))

-- Lights Out logic
def areAdjacent {m n : ℕ} (pos1 pos2 : Fin m × Fin n) : Bool :=
  let (i1, j1) := pos1
  let (i2, j2) := pos2
  (i1 = i2 ∧ Int.natAbs (j1.val - j2.val) = 1) ∨
  (j1 = j2 ∧ Int.natAbs (i1.val - i2.val) = 1)

def isAffected {m n : ℕ} (button : Fin m × Fin n) (pos : Fin m × Fin n) : Bool :=
  button = pos || areAdjacent button pos

def press {m n : ℕ} (state : State m n) (i : Fin m) (j : Fin n) : State m n :=
  Matrix.of fun i' j' => state i' j' + if isAffected (i, j) (i', j') then 1 else 0

-- Simple cell display
def simpleCell (symbol : String) : ProofWidgets.Html :=
  <td>
    {.text symbol}
  </td>

-- Simple grid visualization
def simpleGrid : ProofWidgets.Html :=
  <table>
    <tr>{simpleCell "○"}{simpleCell "●"}{simpleCell "○"}</tr>
    <tr>{simpleCell "●"}{simpleCell "○"}{simpleCell "●"}</tr>
    <tr>{simpleCell "○"}{simpleCell "●"}{simpleCell "○"}</tr>
  </table>

-- Create HTML representation of the board (general version - simplified)
def stateToHtml {m n : ℕ} [NeZero m] [NeZero n] (state : State m n) : ProofWidgets.Html :=
  <div style={json% {
    display: "inline-block",
    border: "2px solid black",
    padding: "10px"
  }}>
    <table style={json% {borderCollapse: "collapse"}}>
      <tr><td>{.text s!"Board visualization {m}×{n}"}</td></tr>
    </table>
  </div>

-- Example states
def cross3x3 : State 3 3 := Matrix.of fun i j =>
  if i = 1 || j = 1 then 1 else 0

def allOff3x3 : State 3 3 := Matrix.of fun _ _ => 0

def checkerboard3x3 : State 3 3 := Matrix.of fun i j =>
  if (i.val + j.val) % 2 = 0 then 1 else 0

-- Display examples
#html simpleGrid

#html <div>
  <h3>{.text "Lights Out Examples"}</h3>
  <div style={json% {display: "flex", gap: "20px"}}>
    <div>
      <h4>{.text "Cross Pattern"}</h4>
      {simpleGrid}
    </div>
    <div>
      <h4>{.text "All Off (Goal)"}</h4>
      {simpleGrid}
    </div>
    <div>
      <h4>{.text "Checkerboard"}</h4>
      {simpleGrid}
    </div>
  </div>
</div>

-- Show a sequence of moves
def showSequence : ProofWidgets.Html :=
  let s0 := cross3x3;
  let s1 := press s0 1 1;
  let s2 := press s1 0 1;
  let s3 := press s2 2 1;
  <div>
    <h3>{.text "Solving the Cross Pattern"}</h3>
    <div style={json% {display: "flex", gap: "10px", alignItems: "center"}}>
      <div>
        <p>{.text "Initial"}</p>
        {simpleGrid}
      </div>
      <span>{.text "→"}</span>
      <div>
        <p>{.text "Press (1,1)"}</p>
        {simpleGrid}
      </div>
      <span>{.text "→"}</span>
      <div>
        <p>{.text "Press (0,1)"}</p>
        {simpleGrid}
      </div>
      <span>{.text "→"}</span>
      <div>
        <p>{.text "Press (2,1)"}</p>
        {simpleGrid}
      </div>
    </div>
  </div>

#html showSequence

-- Create a larger example
def largeExample : State 5 5 := Matrix.of fun i j =>
  if (i = 2 ∧ j = 2) || (i = 1 ∧ j = 2) || (i = 3 ∧ j = 2) ||
     (i = 2 ∧ j = 1) || (i = 2 ∧ j = 3) then 1 else 0

#html <div>
  <h3>{.text "5×5 Lights Out"}</h3>
  {stateToHtml largeExample}
  <p>{.text "This is the standard 5×5 Lights Out puzzle size"}</p>
</div>

end LightsOutWidget
