import ProofWidgets.Component.HtmlDisplay
import RiddleProofs.LightsOut.BoardExamples

open Lean

open scoped ProofWidgets.Jsx

def stateCell (value : ZMod 2) : ProofWidgets.Html :=
  let symbol := if value = 0 then "○" else "●";
  <td style={json% {
            width: "30px",
            height: "30px",
            border: "1px solid black",
            textAlign: "center",
            fontSize: "18px"
          }}>{.text symbol}</td>


def stateToHtml {m n : ℕ} [NeZero m] [NeZero n] (state : LightState m n) : ProofWidgets.Html :=
  let rows := (List.range m).map fun i =>
    if h1 : i < m then
      let cells := (List.range n).map fun j =>
        if h2 : j < n then
          let cellValue := state ⟨i, h1⟩ ⟨j, h2⟩;
          stateCell cellValue

        else
          <td></td>;
      <tr>{...cells.toArray}</tr>
    else
      <tr></tr>;

  <div style={json% {
    display: "inline-block",
    border: "2px solid black",
    padding: "10px"
  }}>
    <table style={json% {borderCollapse: "collapse"}}>
      {...rows.toArray}
    </table>
  </div>


def showSequence : ProofWidgets.Html :=
  let s0 := cross3x3;
  let coordinates := #[
    (0, 0), (0, 2), (2, 0), (2, 2)
  ];
  let states := coordinates.foldl (fun acc (i, j) =>
    let lastState := acc[acc.size - 1]!;
    let newState := press lastState (i, j);
    acc.push newState) #[s0];

  let elements := (states.toList.zipIdx.map (fun (s, idx) =>
    <div style={json% {textAlign: "center", display: "inline-block"}}>
      {if idx = 0 then
        <p>{.text "Initial"}</p>
      else
        <p>{.text s!"Press ({coordinates[idx-1]!.1},{coordinates[idx-1]!.2})"}</p>}
      {stateToHtml s}
    </div>
  )).toArray;

  <div>
    <h3>{.text "Solving the Cross Pattern"}</h3>
    <div style={json% {
      display: "flex", flexDirection: "row", gap: "15px",
      alignItems: "center", flexWrap: "wrap"
    }}>
      {...(elements.toList.intersperse
        (<span style={json% {fontSize: "24px"}}>{.text "→"}</span>)).toArray}
    </div>
  </div>

#html showSequence
