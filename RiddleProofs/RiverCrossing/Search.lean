namespace RiverCrossing

/-!
# Generic Search Algorithms for River Crossing Problems

This module provides a type class-based abstraction for search problems
and implements a generic breadth-first search algorithm.
-/

/-- Type class for basic graph traversal -/
class Graph (State Move : Type) where
  [beq : BEq State]
  initial : State
  generateMoves : State → List Move
  applyMove : Move → State → State

/-- Type class for goal-oriented graph search -/
class GoalGraph (State Move : Type) extends Graph State Move where
  isGoal : State → Bool

/-- Type class for constrained search problems -/
class SearchProblem (State Move : Type) extends GoalGraph State Move where
  isValid : State → Bool := fun _ => true

/-- Configuration for search algorithms with customizable parameters -/
structure SearchParams where
  maxDepth : Nat := 15
  deriving Repr

/-- Result of a search algorithm -/
inductive SearchResult (Move : Type) where
  | success (path : List Move)
  | failure (reason : String)
  deriving Repr

/-- Convert SearchResult to Option for backward compatibility -/
def SearchResult.toOption : SearchResult Move → Option (List Move)
  | .success path => some path
  | .failure _ => none

/-- Helper function to expand neighbors in a graph -/
def expandNeighbors {State Move : Type} [inst : Graph State Move]
    (state : State) (path : List Move) : List (State × List Move) :=
  inst.generateMoves state |>.map fun move =>
    (inst.applyMove move state, move :: path)

/-- Helper function to expand the search frontier with validation -/
def expandFrontier {State Move : Type} [inst : SearchProblem State Move]
    (state : State) (path : List Move) (visited : List State) : List (State × List Move) :=
  have : BEq State := inst.toGoalGraph.toGraph.beq
  expandNeighbors state path |>.filter fun (newState, _) =>
    inst.isValid newState && !visited.contains newState

/-- State and path pair for search algorithms -/
abbrev SearchNode (State Move : Type) := State × List Move

/-- Check if we should process a state -/
def shouldProcess {State Move : Type} [inst : Graph State Move]
    (state : State) (path : List Move) (params : SearchParams) (visited : List State) : Bool :=
  have : BEq State := inst.beq
  path.length ≤ params.maxDepth && !visited.contains state

/-- Simple graph traversal (finds all reachable states) -/
partial def reachable {State Move : Type} [inst : Graph State Move] (maxDepth : Nat := 10) : List State :=
  have : BEq State := inst.beq
  let rec traverse : List (State × Nat) → List State → List State
    | [], visited => visited
    | (state, depth) :: rest, visited =>
      if depth > maxDepth || visited.contains state then
        traverse rest visited
      else
        let neighbors := inst.generateMoves state |>.map (inst.applyMove · state)
        let newStates := neighbors.map (·, depth + 1)
        traverse (rest ++ newStates) (state :: visited)
  traverse [(inst.initial, 0)] []

/-- Breadth-first search for goal states -/
partial def bfsGoal {State Move : Type} [inst : GoalGraph State Move]
    (params : SearchParams := {}) : Option (List Move) :=
  have : BEq State := inst.toGraph.beq
  let rec search : List (SearchNode State Move) → List State → Option (List Move)
    | [], _ => none
    | (state, path) :: rest, visited =>
      if inst.isGoal state then
        some path.reverse
      else if shouldProcess state path params visited then
        let newVisited := state :: visited
        let newNodes := expandNeighbors state path
        search (rest ++ newNodes.filter (fun (s, _) => !newVisited.contains s)) newVisited
      else
        search rest visited
  search [(inst.toGraph.initial, [])] []

/-- Breadth-first search with validation -/
partial def bfs {State Move : Type} [inst : SearchProblem State Move]
    (params : SearchParams := {}) : Option (List Move) :=
  have : BEq State := inst.toGoalGraph.toGraph.beq
  let rec search : List (SearchNode State Move) → List State → Option (List Move)
    | [], _ => none
    | (state, path) :: rest, visited =>
      if inst.toGoalGraph.isGoal state then
        some path.reverse
      else if shouldProcess state path params visited then
        let newVisited := state :: visited
        let newNodes := expandFrontier state path newVisited
        search (rest ++ newNodes) newVisited
      else
        search rest visited
  
  search [(inst.toGoalGraph.toGraph.initial, [])] []

/-- Basic graph structure for search problems -/
structure GraphConfig (State Move : Type) where
  initial_state : State
  generate_moves : State → List Move
  apply_move : Move → State → State

/-- Graph with goal checking -/
structure GoalGraphConfig (State Move : Type) extends GraphConfig State Move where
  is_goal : State → Bool

/-- Full search configuration with validation and depth limit -/
structure SearchConfig (State Move : Type) extends GoalGraphConfig State Move where
  is_valid_state : State → Bool := fun _ => true
  max_depth : Nat := 15

/-- Convert GraphConfig to Graph instance -/
def GraphConfig.toInstance {State Move : Type} [BEq State]
    (config : GraphConfig State Move) : Graph State Move :=
  { beq := inferInstance
    initial := config.initial_state
    generateMoves := config.generate_moves
    applyMove := config.apply_move }

/-- Convert GoalGraphConfig to GoalGraph instance -/
def GoalGraphConfig.toInstance {State Move : Type} [BEq State]
    (config : GoalGraphConfig State Move) : GoalGraph State Move :=
  { toGraph := config.toGraphConfig.toInstance
    isGoal := config.is_goal }

/-- Convert SearchConfig to SearchProblem instance -/
def SearchConfig.toInstance {State Move : Type} [BEq State] 
    (config : SearchConfig State Move) : SearchProblem State Move :=
  { toGoalGraph := config.toGoalGraphConfig.toInstance
    isValid := config.is_valid_state }

/-- Backward compatible BFS function -/
def generic_bfs {State Move : Type} [BEq State]
    (config : SearchConfig State Move) : Option (List Move) :=
  let inst : SearchProblem State Move := config.toInstance
  @bfs State Move inst ⟨config.max_depth⟩

/-- Run BFS with a SearchProblem instance -/
def solve {State Move : Type} [inst : SearchProblem State Move] (params : SearchParams := {}) : Option (List Move) :=
  @bfs State Move inst params

/-- Example: Find any path of specific length from initial state -/
partial def findPathOfLength {State Move : Type} [inst : Graph State Move] (targetLength : Nat) : Option (List Move) :=
  have : BEq State := inst.beq
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
