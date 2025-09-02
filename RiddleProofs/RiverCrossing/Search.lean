namespace RiverCrossing

class StateTransition (State Move : Type) where
  initial : State
  generateMoves : State → List Move
  applyMove : Move → State → State

class GoalOrientedGraph (State Move : Type) extends StateTransition State Move where
  isGoal : State → Bool

class ConstrainedSearch (State Move : Type) extends GoalOrientedGraph State Move where
  isValid : State → Bool := fun _ => true

structure SearchParams where
  maxDepth : Nat := 15
  deriving Repr


def expandNeighbors {State Move : Type} [StateTransition State Move]
    (currentState : State) (currentPath : List Move) : List (State × List Move) :=
  StateTransition.generateMoves currentState |>.map fun move =>
    (StateTransition.applyMove move currentState, move :: currentPath)

def expandFrontier {State Move : Type} [BEq State] [problem : ConstrainedSearch State Move]
    (currentState : State) (currentPath : List Move) (visitedStates : List State) : List (State × List Move) :=
  expandNeighbors currentState currentPath |>.filter fun (newState, _) =>
    problem.isValid newState && !visitedStates.contains newState

abbrev SearchNode (State Move : Type) := State × List Move

def shouldProcess {State Move : Type} [BEq State]
    (currentState : State) (currentPath : List Move) (params : SearchParams) (visitedStates : List State) : Bool :=
  currentPath.length ≤ params.maxDepth && !visitedStates.contains currentState



partial def bfs {State Move : Type} [BEq State] [problem : ConstrainedSearch State Move]
    (params : SearchParams := {}) : Option (List Move) :=
  let rec search : List (SearchNode State Move) → List State → Option (List Move)
    | [], _ => none
    | (currentState, currentPath) :: remainingQueue, visitedStates =>
      if problem.isGoal currentState then
        some currentPath.reverse
      else if shouldProcess currentState currentPath params visitedStates then
        let newVisited := currentState :: visitedStates
        let newNodes := expandFrontier currentState currentPath newVisited
        search (remainingQueue ++ newNodes) newVisited
      else
        search remainingQueue visitedStates

  search [(problem.initial, [])] []

structure StateTransitionConfig (State Move : Type) where
  initialState : State
  generateMoves : State → List Move
  applyMove : Move → State → State

structure GoalOrientedConfig (State Move : Type) extends StateTransitionConfig State Move where
  isGoal : State → Bool

structure ConstrainedSearchConfig (State Move : Type) extends GoalOrientedConfig State Move where
  isValidState : State → Bool
  maxDepth : Nat := 15

instance {State Move : Type} [BEq State] : Coe (ConstrainedSearchConfig State Move) (ConstrainedSearch State Move) where
  coe config := {
    initial := config.initialState
    generateMoves := config.generateMoves
    applyMove := config.applyMove
    isGoal := config.isGoal
    isValid := config.isValidState
  }

def genericBFS {State Move : Type} [BEq State]
    (config : ConstrainedSearchConfig State Move) : Option (List Move) :=
  let problem : ConstrainedSearch State Move := config
  @bfs State Move _ problem ⟨config.maxDepth⟩



end RiverCrossing
