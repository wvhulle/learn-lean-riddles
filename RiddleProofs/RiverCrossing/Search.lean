namespace RiverCrossing

/-!
# Generic Search Algorithms for River Crossing Problems

This module provides a type class-based abstraction for search problems
and implements a generic breadth-first search algorithm.
-/

/-- Type class for problems that can be solved with graph search algorithms -/
class SearchProblem (State Move : Type) where
  [beq : BEq State]
  initial : State
  isGoal : State → Bool
  generateMoves : State → List Move
  applyMove : Move → State → State
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

/-- Helper function to expand the search frontier -/
def expandFrontier {State Move : Type} [inst : SearchProblem State Move]
    (state : State) (path : List Move) (visited : List State) : List (State × List Move) :=
  have : BEq State := inst.beq
  inst.generateMoves state |>.filterMap fun move => do
    let newState := inst.applyMove move state
    guard (inst.isValid newState)
    guard (!visited.contains newState)
    pure (newState, move :: path)

/-- State and path pair for search algorithms -/
abbrev SearchNode (State Move : Type) := State × List Move

/-- Check if we should process a state -/
def shouldProcess {State Move : Type} [inst : SearchProblem State Move]
    (state : State) (path : List Move) (params : SearchParams) (visited : List State) : Bool :=
  have : BEq State := inst.beq
  path.length ≤ params.maxDepth && !visited.contains state

/-- Generic breadth-first search algorithm -/
partial def bfs {State Move : Type} [inst : SearchProblem State Move]
    (params : SearchParams := {}) : Option (List Move) :=
  have : BEq State := inst.beq
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

/-- Legacy interface for backward compatibility -/
structure SearchConfig (State Move : Type) where
  initial_state : State
  is_goal : State → Bool
  generate_moves : State → List Move
  apply_move : Move → State → State
  is_valid_state : State → Bool
  max_depth : Nat := 15

/-- Adapter to use the old SearchConfig structure with the new type class -/
def SearchConfig.toInstance {State Move : Type} [BEq State] 
    (config : SearchConfig State Move) : SearchProblem State Move :=
  { beq := inferInstance
    initial := config.initial_state
    isGoal := config.is_goal
    generateMoves := config.generate_moves
    applyMove := config.apply_move
    isValid := config.is_valid_state }

/-- Backward compatible BFS function -/
def generic_bfs {State Move : Type} [BEq State]
    (config : SearchConfig State Move) : Option (List Move) :=
  let inst : SearchProblem State Move := config.toInstance
  @bfs State Move inst ⟨config.max_depth⟩

/-- Run BFS with a SearchProblem instance -/
def solve {State Move : Type} [inst : SearchProblem State Move] (params : SearchParams := {}) : Option (List Move) :=
  @bfs State Move inst params

end RiverCrossing
