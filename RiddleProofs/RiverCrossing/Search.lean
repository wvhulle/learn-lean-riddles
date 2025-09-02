namespace RiverCrossing

class MoveState (State Move : Type) where
  initial : State
  generateMoves : State → List Move
  applyMove : Move → State → State

class GoalGraph (State Move : Type) extends MoveState State Move where
  isGoal : State → Bool

class SearchProblem (State Move : Type) extends GoalGraph State Move where
  isValid : State → Bool := fun _ => true

structure SearchParams where
  maxDepth : Nat := 15
  deriving Repr


def expandNeighbors {State Move : Type} [MoveState State Move]
    (state : State) (path : List Move) : List (State × List Move) :=
  MoveState.generateMoves state |>.map fun move =>
    (MoveState.applyMove move state, move :: path)

def expandFrontier {State Move : Type} [BEq State] [inst : SearchProblem State Move]
    (state : State) (path : List Move) (visited : List State) : List (State × List Move) :=
  expandNeighbors state path |>.filter fun (newState, _) =>
    inst.isValid newState && !visited.contains newState

abbrev SearchNode (State Move : Type) := State × List Move

def shouldProcess {State Move : Type} [BEq State]
    (state : State) (path : List Move) (params : SearchParams) (visited : List State) : Bool :=
  path.length ≤ params.maxDepth && !visited.contains state



partial def bfs {State Move : Type} [BEq State] [inst : SearchProblem State Move]
    (params : SearchParams := {}) : Option (List Move) :=
  let rec search : List (SearchNode State Move) → List State → Option (List Move)
    | [], _ => none
    | (state, path) :: rest, visited =>
      if inst.isGoal state then
        some path.reverse
      else if shouldProcess state path params visited then
        let newVisited := state :: visited
        let newNodes := expandFrontier state path newVisited
        search (rest ++ newNodes) newVisited
      else
        search rest visited

  search [(inst.initial, [])] []

structure GraphConfig (State Move : Type) where
  initialState : State
  generateMoves : State → List Move
  applyMove : Move → State → State

structure GoalGraphConfig (State Move : Type) extends GraphConfig State Move where
  isGoal : State → Bool

structure SearchConfig (State Move : Type) extends GoalGraphConfig State Move where
  isValidState : State → Bool
  maxDepth : Nat := 15

instance {State Move : Type} [BEq State] : Coe (SearchConfig State Move) (SearchProblem State Move) where
  coe config := {
    initial := config.initialState
    generateMoves := config.generateMoves
    applyMove := config.applyMove
    isGoal := config.isGoal
    isValid := config.isValidState
  }

def genericBFS {State Move : Type} [BEq State]
    (config : SearchConfig State Move) : Option (List Move) :=
  letI inst : SearchProblem State Move := config
  @bfs State Move _ inst ⟨config.maxDepth⟩

def generic_bfs := @genericBFS

def solve {State Move : Type} [BEq State] [inst : SearchProblem State Move]
    (params : SearchParams := {}) : Option (List Move) :=
  @bfs State Move _ inst params

partial def findPathOfLength {State Move : Type} [BEq State] [inst : MoveState State Move]
    (targetLength : Nat) : Option (List Move) :=
  let rec search : List (State × List Move) → List State → Option (List Move)
    | [], _ => none
    | (state, path) :: rest, visited =>
      if path.length == targetLength then
        some path.reverse
      else if path.length > targetLength || visited.contains state then
        search rest visited
      else
        let newVisited := state :: visited
        let newNodes := expandNeighbors state path
        search (rest ++ newNodes.filter (fun (s, _) => !newVisited.contains s)) newVisited
  search [(inst.initial, [])] []

end RiverCrossing
