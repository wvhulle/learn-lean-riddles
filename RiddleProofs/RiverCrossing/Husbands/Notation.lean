import RiddleProofs.RiverCrossing.Husbands.Statement
import Mathlib.Data.Finset.Card



open RiverCrossing.Husbands


instance : ToString Person where
  toString p := match p with
  | .husband i => s!"H{i.val}"
  | .wife i => s!"W{i.val}"

notation "H" n => Person.husband ⟨n, by decide⟩
notation "W" n => Person.wife ⟨n, by decide⟩

@[app_unexpander Person.husband]
def unexpandHusband : Lean.PrettyPrinter.Unexpander
  | `($_ ⟨$n, $_⟩) => `(H $n)
  | _ => throw ()

@[app_unexpander Person.wife]
def unexpandWife : Lean.PrettyPrinter.Unexpander
  | `($_ ⟨$n, $_⟩) => `(W $n)
  | _ => throw ()

/-- SafetyConstraint instance for JealousHusbandsState -/
instance : SafetyConstraint Person Person num_couples where
  is_safe := bank_safe
  is_safe_decidable := by infer_instance


/-- Direction the boat travels. The boat must shuttle back and forth. -/
inductive Direction
| toRight  -- From left bank to right bank
| toLeft   -- From right bank to left bank
deriving DecidableEq, Repr

instance : ToString Direction where
  toString
  | .toRight => "R"
  | .toLeft => "L"


structure Move where
  /-- A move consists of 1-2 people traveling in a specific direction. -/
  people_in_boat : Finset Person
  direction : Direction
  amount_people_in_boat : people_in_boat.card ≤ 2 ∧ people_in_boat.card > 0
deriving DecidableEq



-- Helper to format a list of items using their ToString instances
private def formatCommaSeparated [ToString α] (items : List α) : String :=
  String.intercalate "," (items.map toString)

-- Helper to format the people part of a move using existing ToString instances
private def formatPeople (people_in_boat : Finset Person) : String :=
  let all_people : List Person := [H 0, H 1, H 2, W 0, W 1, W 2]
  let people_in_move := all_people.filter (· ∈ people_in_boat)

  match people_in_move with
  | [] => "nobody"                                 -- Edge case
  | [p] => toString p                              -- Single person: "H0"
  | people => formatCommaSeparated people          -- Multiple people: "H0,W1"

-- Computable function to reconstruct the exact syntax using existing ToString instances
def moveToExactSyntaxComputable (m : Move) : String :=
  toString m.direction ++ "{" ++ formatPeople m.people_in_boat ++ "}"



instance : Repr Move where
  reprPrec m _ := moveToExactSyntaxComputable m



/-- Create a move with a single person traveling in the given direction. -/
def single (p : Person) (dir : Direction) : Move :=
  ⟨{p}, dir, by simp [Finset.card_singleton]⟩

/-- Create a move with two people traveling together in the given direction.
    Requires proof that the two people are different. -/
def pair (p1 p2 : Person) (dir : Direction) (h : p1 ≠ p2) : Move :=
  ⟨{p1, p2}, dir, by
    constructor
    · simp [Finset.card_pair h]
    · simp [Finset.card_pair h]⟩


/-- Custom syntax for readable move notation.

    Examples:
    - `R {H 0}`: Husband 0 moves right (alone)
    - `L {W 1}`: Wife 1 moves left (alone)
    - `R {H 0, W 0}`: Couple 0 moves right (together)
    - `L {H 1, H 2}`: Husbands 1 and 2 move left (together) -/
syntax:50 "R" "{" term "}" : term
syntax:50 "L" "{" term "}" : term
syntax:50 "R" "{" term "," term "}" : term
syntax:50 "L" "{" term "," term "}" : term

macro_rules
  | `(R {$p}) => `(single $p Direction.toRight)
  | `(L {$p}) => `(single $p Direction.toLeft)
  | `(R {$p1, $p2}) => `(pair $p1 $p2 Direction.toRight (by simp))
  | `(L {$p1, $p2}) => `(pair $p1 $p2 Direction.toLeft (by simp))



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

-- Test the simplified formatting
#eval moveToExactSyntaxComputable (R {H 0})     -- Should show "R{H0}"
#eval moveToExactSyntaxComputable (L {W 1, H 2}) -- Should show "L{W1,H2}"
