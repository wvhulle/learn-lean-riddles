import RiddleProofs.RiverCrossing.Husbands.Statement
import Mathlib.Data.Finset.Card

open RiverCrossing.Husbands

/-! ## Abbreviated person input

Three display methods for Person type:
1. ToString instance: Use for string concatenation and debugging
2. Notation shortcuts: Use for quick input (H 0, W 1)
3. Unexpanders: Use for pretty-printing in goal view and error messages
-/
notation "H" n:max => Person.husband ⟨n, by decide⟩
notation "W" n:max => Person.wife ⟨n, by decide⟩

example : Person := H 0
example : Person := W 1


-- Test that notation and direct construction are equivalent
example : H 0 = Person.husband ⟨0, by decide⟩ := by rfl
example : W 2 = Person.wife ⟨2, by decide⟩ := by rfl


/- ## Abbreviated person output
-/

instance : ToString Person where
  toString p := match p with
  | .husband i => s!"H{i.val}"
  | .wife i => s!"W{i.val}"

#eval s!"I am {(Person.husband 0)}"  -- Shows "H0"


/- ## Abbreviated persons in proof state
-/

@[app_unexpander Person.husband]
def unexpandHusband : Lean.PrettyPrinter.Unexpander
  | `($_ ⟨$n, $_⟩) => `(H $n)
  | `($_ $n) => `(H $n)
  | _ => throw ()

@[app_unexpander Person.wife]
def unexpandWife : Lean.PrettyPrinter.Unexpander
  | `($_ ⟨$n, $_⟩) => `(W $n)
  | `($_ $n) => `(W $n)
  | _ => throw ()

-- Test that unexpanders work in equality proofs
example : Person.husband 0 = Person.husband ⟨0, by decide⟩ := by
  -- Put your cursor in front of `rfl`. You should see the unexpander being used
  rfl

example : Person.wife ⟨1, by decide⟩ = Person.wife ⟨1, by decide⟩ := rfl



/-! ## Abbreviated direction in output

Two display methods for Direction type:
1. ToString instance: Use for compact string output (R/L)
2. Automatic Repr derivation: Use for debugging and #eval statements
-/

/-- Direction the boat travels. The boat must shuttle back and forth. -/
inductive Direction
| toRight  -- From left bank to right bank
| toLeft   -- From right bank to left bank
deriving DecidableEq, Repr

instance : ToString Direction where
  toString
  | .toRight => "R"
  | .toLeft => "L"

#eval s!"Going {Direction.toRight}"

/-! ## Move structure and constructors

Core structure representing a single boat crossing move.
-/

structure Move where
  people_in_boat : Finset Person
  direction : Direction
  amount_people_in_boat : people_in_boat.card ≤ 2 ∧ people_in_boat.card > 0

def single (p : Person) (dir : Direction) : Move :=
  ⟨{p}, dir, by simp [Finset.card_singleton]⟩

def pair (p1 p2 : Person) (dir : Direction) (h : p1 ≠ p2) : Move :=
  ⟨{p1, p2}, dir, by
    constructor
    · simp [Finset.card_pair h]
    · simp [Finset.card_pair h]⟩

/-! ## Abbreviated move input -/


syntax:50 "R" "{" term "}" : term
syntax:50 "L" "{" term "}" : term
syntax:50 "R" "{" term "," term "}" : term
syntax:50 "L" "{" term "," term "}" : term

macro_rules
  | `(R {$p}) => `(single $p Direction.toRight)
  | `(L {$p}) => `(single $p Direction.toLeft)
  | `(R {$p1, $p2}) => `(pair $p1 $p2 Direction.toRight (by simp))
  | `(L {$p1, $p2}) => `(pair $p1 $p2 Direction.toLeft (by simp))

/-
Examples:
- `R {H 0}`: Husband 0 moves right (alone)
- `L {W 1}`: Wife 1 moves left (alone)
- `R {H 0, W 0}`: Couple 0 moves right (together)
- `L {H 1, H 2}`: Husbands 1 and 2 move left (together) -/


/-! ## Move display methods
-/

private def formatCommaSeparated [ToString α] (items : List α) : String :=
  String.intercalate "," (items.map toString)

private def formatPeople (people_in_boat : Finset Person) : String :=
  let all_people : List Person := [
    Person.husband ⟨0, by decide⟩, Person.husband ⟨1, by decide⟩, Person.husband ⟨2, by decide⟩,
    Person.wife ⟨0, by decide⟩, Person.wife ⟨1, by decide⟩, Person.wife ⟨2, by decide⟩
  ]
  let people_in_move := all_people.filter (· ∈ people_in_boat)

  match people_in_move with
  | [] => "nobody"                                 -- Edge case
  | [p] => toString p                              -- Single person: "H0"
  | people => formatCommaSeparated people          -- Multiple people: "H0,W1"


instance: ToString Move where
  toString m := toString m.direction ++ "{" ++ formatPeople m.people_in_boat ++ "}"


-- Because `ToString` is implemented, you can see these evaluations:
#eval (R {Person.husband ⟨0, by decide⟩})     -- Should show "R{H0}"
#eval (L {Person.wife ⟨1, by decide⟩, Person.husband ⟨2, by decide⟩}) -- Should show "L{W1,H2}"


/- ## Abbreviated moves in proof states -/

@[app_unexpander single]
def unexpandSingle : Lean.PrettyPrinter.Unexpander
  | `($_ $p Direction.toRight) =>
      `(R {$p})
  | `($_ $p Direction.toLeft) => `(L {$p})
  | _ => throw ()

@[app_unexpander pair]
def unexpandPair : Lean.PrettyPrinter.Unexpander
  | `($_ $p1 $p2 Direction.toRight $_) => `(R {$p1, $p2})
  | `($_ $p1 $p2 Direction.toLeft $_) => `(L {$p1, $p2})
  | _ => throw ()

-- You can test these unexpanders by writing proofs that involve moves.
