import RiddleProofs

-- Main entry point for the riddle-proofs project
-- This is a simple executable that just prints a greeting
--
-- For workshop participants:
-- - The interesting content is in the RiddleProofs/ directory
-- - Each riddle has its own file with explanations and examples
-- - Start with simpler puzzles like MontyHall or BlueEyedIslanders
-- - The LightsOut puzzle shows more advanced linear algebra techniques
--
-- To run this program: `lake exe riddle-proofs`
-- To build the project: `lake build`
-- To explore proofs interactively: open the .lean files in VS Code with Lean 4 extension

def main : IO Unit := do
  IO.println "Welcome to the Riddle Proofs Workshop!"
  IO.println "Explore the RiddleProofs/ directory to see formalized puzzles."
  IO.println "Each file contains detailed explanations and learning objectives."
