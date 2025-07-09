import Lake
open Lake DSL

package «riddle-proofs» where
  version := v!"0.0.1"
  -- Enable comprehensive linting for better code quality
  leanOptions := #[
    -- -- Core linters
    -- ⟨`linter.all, false⟩,                              -- Don't enable ALL linters (too strict)
    -- ⟨`linter.unusedVariables, true⟩,                   -- Catch unused variables
    -- ⟨`linter.unusedVariables.funArgs, true⟩,          -- Including function arguments
    -- ⟨`linter.unusedVariables.patternVars, true⟩,      -- Including pattern variables
    -- ⟨`linter.unusedVariables.analyzeTactics, true⟩,   -- Analyze tactics for unused vars
    -- ⟨`linter.constructorNameAsVariable, true⟩,        -- Warn when variable names match constructors
    -- ⟨`linter.deprecated, true⟩,                       -- Warn about deprecated features
    -- ⟨`linter.missingDocs, false⟩,                     -- Don't require docs for exercises
    -- ⟨`linter.unnecessarySimpa, true⟩,                 -- Suggest simpler simp usage

    -- -- Style linters (mathlib-style)
    -- ⟨`linter.style.lambdaSyntax, true⟩,               -- Prefer 'fun' over 'λ'
    -- ⟨`linter.style.dollarSyntax, true⟩,               -- Prefer '<|' over '$'
    -- ⟨`linter.style.longLine, true⟩,                   -- Enforce 100 character line limit
    -- ⟨`linter.style.longFile, true⟩,                   -- Warn on files > 1500 lines
    -- ⟨`linter.style.commandStart, true⟩,               -- Commands should start at line beginning
    -- ⟨`linter.style.cdot, true⟩,                       -- Check proper cdot usage

    -- -- Advanced linters for proof quality
    -- ⟨`linter.haveLet, true⟩,                             -- Suggest 'let' for non-propositions
    -- ⟨`linter.unusedTactic, true⟩,                     -- Catch tactics that do nothing
    -- ⟨`linter.minImports, false⟩,                      -- Don't check minimal imports (too pedantic)
    -- ⟨`linter.oldObtain, true⟩,                        -- Modernize obtain usage
    -- ⟨`linter.style.multiGoal, true⟩,                  -- Warn on multiple active goals
    -- ⟨`linter.style.refine, true⟩,                     -- Catch refine' usage
    -- ⟨`linter.style.admit, true⟩,                      -- Catch admit usage
    -- ⟨`linter.style.openClassical, true⟩,              -- Scope classical logic opens
    -- ⟨`linter.style.header, false⟩,                    -- Don't enforce strict header format
    -- ⟨`linter.style.docString, false⟩,                 -- Don't enforce docstring format
    -- ⟨`linter.style.nameCheck, true⟩,                  -- Check naming conventions
    -- ⟨`linter.flexible, true⟩,                         -- Check tactic flexibility
    -- ⟨`linter.omit, true⟩                              -- Warn against 'omit' usage
  ]

@[default_target]
lean_lib «RiddleProofs» where
  moreLeanArgs := #[
    "-DwarningAsError=true"                            -- Treat warnings as errors
  ]

lean_exe «riddle-proofs» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5c5a8deb94353f2b659cb9c578fe833f90febac7"

require «ennreal-arith» from git
  "https://github.com/wvhulle/ennreal-arith.git" @ "1d0a4390415dcdb1903be38cfc0256a9867d878e"
