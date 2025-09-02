import ProofWidgets.Component.HtmlDisplay
import RiddleProofs.LightsOut.BoardExamples

open scoped ProofWidgets.Jsx

def stateCell (value : ZMod 2) : ProofWidgets.Html :=
  let symbol := if value = 0 then "○" else "●";
  <td style={json% {
    width: "30px",
    height: "30px",
    border: "1px solid black",
    textAlign: "center",
    fontSize: "18px"
  }}>
    {.text symbol}
  </td>


def generateRowCells {m n : ℕ} [NeZero m] [NeZero n] (state : LightState m n) (i : Fin m) : Array ProofWidgets.Html :=
  ((List.finRange n).map fun j =>
    stateCell (state i j)).toArray

def generateTableRow {m n : ℕ} [NeZero m] [NeZero n] (state : LightState m n) (i : Fin m) : ProofWidgets.Html :=
  let cells := generateRowCells state i;
  <tr>
    {...cells}
  </tr>

def wrapInGameBoard (rows : List ProofWidgets.Html) : ProofWidgets.Html :=
  <div style={json% {
    display: "inline-block",
    border: "2px solid black",
    padding: "10px"
  }}>
    <table style={json% {
      borderCollapse: "collapse"
    }}>
      {...rows.toArray}
    </table>
  </div>

def stateToHtml {m n : ℕ} [NeZero m] [NeZero n] (state : LightState m n) : ProofWidgets.Html :=
  let rows := (List.finRange m).map (generateTableRow state);
  wrapInGameBoard rows


def generateStateSequence {m n : ℕ} [NeZero m] [NeZero n] (initial : LightState m n)
    (coordinates : Array (Fin m × Fin n)) : Array (LightState m n) :=
  coordinates.foldl (fun acc coord =>
    acc.push (press acc.back! coord)) #[initial]

def renderStateStep {m n : ℕ} [NeZero m] [NeZero n] (state : LightState m n) (stepLabel : String) : ProofWidgets.Html :=
  <div style={json% {
    textAlign: "center",
    display: "inline-block"
  }}>
    <p>{.text stepLabel}</p>
    {stateToHtml state}
  </div>

def addNavigationArrows (elements : Array ProofWidgets.Html) : Array ProofWidgets.Html :=
  elements.toList.intersperse
    (<span style={json% {
      fontSize: "24px"
    }}>
      {.text "→"}
    </span>) |>.toArray

def generateStepElements {m n : ℕ} [NeZero m] [NeZero n] (states : Array (LightState m n))
    (coordinates : Array (Fin m × Fin n)) : Array ProofWidgets.Html :=
  (states.toList.zipIdx.map (fun (s, idx) =>
    let stepLabel := if idx = 0 then "Initial" else s!"Press ({coordinates[idx-1]!.1},{coordinates[idx-1]!.2})"
    renderStateStep s stepLabel
  )).toArray

def showSequence {m n : ℕ} [NeZero m] [NeZero n] (initial : LightState m n)
    (coordinates : Array (Fin m × Fin n)) (title : String := "Button Sequence") : ProofWidgets.Html :=
  let states := generateStateSequence initial coordinates;
  let elements := generateStepElements states coordinates;

  <div>
    <h3>{.text title}</h3>
    <div style={json% {
      display: "flex",
      flexDirection: "row",
      gap: "15px",
      alignItems: "center",
      flexWrap: "wrap"
    }}>
      {...addNavigationArrows elements}
    </div>
  </div>

def crossSequenceExample : ProofWidgets.Html :=
  showSequence cross3x3 #[(0, 0), (0, 2), (2, 0), (2, 2)] "Solving the Cross Pattern"

#html crossSequenceExample
