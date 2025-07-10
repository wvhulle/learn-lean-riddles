import Lake
open Lake DSL

package «riddle-proofs» where
  version := v!"0.0.1"

@[default_target]
lean_lib «RiddleProofs» where


/- **Main executable**: Runs welcome message and project info -/
lean_exe «riddle-proofs» where
  root := `Main

/- **Core dependency**: Mathlib4 provides mathematical foundations
   - Probability theory (for BirthdayProblem, MontyHall)
   - Group theory and linear algebra (for LightsOut)
   - Finite type theory (for BlueEyedIslanders, JealousHusbands)
   - General mathematical infrastructure (tactics, lemmas, notation) -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5c5a8deb94353f2b659cb9c578fe833f90febac7"

/- **Extended real arithmetic**: Specialized library for extended non-negative reals
   - Used in advanced probability measure theory sections
   - Provides additional tactics and lemmas for ENNReal computations -/
require «ennreal-arith» from git
  "https://github.com/wvhulle/ennreal-arith.git" @ "1d0a4390415dcdb1903be38cfc0256a9867d878e"

/- **Interactive widgets**: Provides rich visualizations in VS Code
   - Enables interactive proof exploration
   - Supports custom visualizations for puzzles (if implemented)
   - Enhances the learning experience with better UI elements -/
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.67"
