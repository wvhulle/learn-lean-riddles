/-!
# The Knights and Knaves Puzzle

On an island, knights always tell the truth and knaves always lie. You meet two inhabitants, A and B. A says, “B is a knave.” B says, “We are of opposite types.” What are A and B?
-/

inductive Person | A | B deriving DecidableEq, Repr
inductive Role | knight | knave deriving DecidableEq, Repr

open Person Role

/-- A world assigns a role to each person. -/
def World := Person → Role

/-- A knight's statement is true, a knave's statement is false. -/
def says (w : World) (p : Person) (prop : Prop) : Prop :=
  match w p with
  | knight => prop
  | knave => ¬prop

/-- The statements: -/
def statements (w : World) : Bool :=
  match w A, w B with
  | knight, knight => (w B = knave) ∧ (w A ≠ w B)
  | knight, knave  => (w B = knave) ∧ ¬(w A ≠ w B)
  | knave, knight  => ¬(w B = knave) ∧ (w A ≠ w B)
  | knave, knave   => ¬(w B = knave) ∧ ¬(w A ≠ w B)

/-- There are only four possible worlds. -/
def all_worlds : List World :=
  [ fun p => match p with | A => knight | B => knight,
    fun p => match p with | A => knight | B => knave,
    fun p => match p with | A => knave | B => knight,
    fun p => match p with | A => knave | B => knave ]

/-- Find all worlds where the statements are true. -/
def solutions : List World := all_worlds.filter statements

instance : ToString Role where
  toString r := match r with | knight => "knight" | knave => "knave"

#eval solutions.map (fun w => (toString (w A), toString (w B)))
