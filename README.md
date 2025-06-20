# Collection of riddles and puzzles in Lean 4

This is a collection of riddles and puzzles implemented in Lean 4 for a workshop given on 17th of July 2025 at Ghent.

_**Note**: This is a work in progress. The code is not complete yet, but the puzzles are solvable.

## Getting started (for new users)

If you have never used Lean before, you will have to install some system dependencies and tools to get started.

### Toolchain

Install [`elan`](https://github.com/leanprover/elan), to manage Lean toolchains. It provides the `lean` and `lake` commands. `lake` is similar to cargo and `lean` is similar to `rustc`. To start a new project in the current directory:

```bash
lake init
```

### Project structure

Lean code is written in side the files (indirectly) referenced in the `lakefile.toml` file.

### General documentation

The [reference manual](https://lean-lang.org/doc/reference/latest/) contains information about the core language.

### Standard library

If you need data structures or things that live in the standard libraries, you have to import the definitions from the standard library.

After writing an import like this for a Lean module, the definitions from the module become available in the current Lean source file.

```lean
import Std.Data.HashSet
```

You might need to restart the language server of Lean in your editor after changing an import. Shortcut: `Ctrl + Shift + X`.

You can find the **import paths** by look at the relative path of the module to the `src/std` directory in the [Lean 4 repository](https://github.com/leanprover/lean4/tree/master/src/Std).

_**Important**: References to the definitions in the standard library in the reference manual point to namespaces (not import paths for modules)._

For example `HashSet` is defined in the namespace `Std.HashSet`, according to the reference manual, but you have to import it like `import Std.Data.HashSet`.

### Building the project

Successfull compilation of a project in Lean shows that all logical and mathematical statements expressed the type system are valid. To compile (build) the project, run:

```bash
lake build
```

## Mathematics

### Mathlib

A large superset of the standard library. It contains a lot of mathematical definitions and theorems, which are useful for writing mathematical proofs in Lean.

### Mathlib installation

To install Mathlib as a dependency to your current project, follow [Mathlib installation instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency).

Inside the `lakefile.toml` file, add the following lines:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

```bash
lake update mathlib
```

### Searching mathematical facts

The collection of definitions and theorems in Mathlib is large, so it is useful to have some tools to search for definitions and theorems:

- Interactive [HTML pages](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html) with cross-references and syntax highlighting.

- Definition search engines provided by language server (and hosted online):
  - Based on using meta-variables and the type system: [Loogle](https://loogle.lean-lang.org/).
  - Search using natural language: [Moogle](https://moogle.ai/).

Example of an import for a mathematical definition from Mathlib:

```lean
import Mathlib.Algebra.MonoidAlgebra.Basic
#check AddMonoidAlgebra.lift_def
```

### Mathematical learning resources

Good resources to learn how to do (tranditional) formal mathematics in Lean:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)

## Puzzles

Located inside the [`RiddleProofs`](./RiddleProofs) directory.
