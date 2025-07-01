# Copilot Instructions for Lean Development

## General Principles
- Never replace a working, type-checked proof with `sorry`.
- Avoid sketching proofs in comments. Instead, prioritize proving smaller, initial lemmas. Writing comments instead of code is not helpful.

## Lean/Mathlib Strategy
- The primary source for definitions and theorems is the `mathlib4` library.
- To find relevant theorems, use the following resources:
  - **Loogle:** [https://loogle.lean-lang.org/](https://loogle.lean-lang.org/) (paste the goal's shape)
  - **LeanExplore:** [https://www.leanexplore.com/](https://www.leanexplore.com/) (for broader searches)

## Tool Usage

### `simp` Tactic
- Use the `simp` tactic to automate low-level arithmetic and casting steps.
- Define custom `simp` lemmas for recurring simplifications.
- These lemmas must be generic:
  - Avoid magic numbers.
  - Use implicit constraints (e.g., finiteness, non-zeroness, strict positivity).

### Lean MCP Server
- **Always use the Lean MCP server first.** The binary name is `lean-lsp-mcp`.
- Never guess solutions; query the MCP server's capabilities before you start.
- Re-query the MCP server after making fundamental changes to the code.

### Lake & Build System
- **Do not delete the `.lake` directory or run `lake clean`.** This is almost always a mistake.
- Fix build issues by correcting errors in the project's source files, not by rebuilding dependencies.
- When you need output from Lean, prefer using the Lean MCP server configured for VS Code.

## Code Style
- Prefer equational proofs using `calc` over a series of successive `have` statements. `calc` blocks are easier to read and follow.

## Workflow for Large Files
- When asked to fix a large file, work in small, incremental steps.
- **Do not try to solve all `sorry`s at once.**
- Follow this process:
  1. Read the final statements in the file to understand the overall structure.
  2. Identify the first lemma that has a `sorry` or an error.
  3. Focus on fixing that single lemma before moving to the next.