# Riddles in Lean

This is a collection of riddles and puzzles implemented in Lean 4 for a [workshop](https://sysghent.be/events/lean/) given on 17th of July 2025 in Ghent for [SysGhent](https://sysghent.be).

_**Note**: This is a work in progress. The code is not complete yet, but the puzzles are mostly solvable._

## Getting started (for new users)

If you have never used Lean before, you will have to install some system dependencies and tools to get started.

### Toolchain

Install [`elan`](https://github.com/leanprover/elan), to manage Lean toolchains. It provides the `lean` and `lake` commands.

_Remark: Installing `elan` installs two executables. The executable `lake` has a similar role as cargo and `lean` is similar to `rustc`._

### Scaffolding

You can just continue with the rest of this workshop in the same folder, but you can also create a new project. To start a new Lean project, `cd` into a new empty directory and run:

```bash
lake init
```

### Project structure

Lean code is written inside Lean source files (indirectly) referenced in the `lakefile.toml` file. Extra dependencies will be added to `lakefile.toml`.

_Remark: On some sites, you might see there is a `lakefile.lean` instead of `lakefile.toml`. In this project we will stick to the TOML variant._

For more information see the [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#--tech-term-package-configuration).

### Language documentation

If you need a fast-paced introduction you can read [Hitchhiker's Guide to Logical Verification (2023 Edition)](https://lean-forward.github.io/hitchhikers-guide/2023/).

While learning, you may have further questions. Consult the [reference manual](https://lean-lang.org/doc/reference/latest/) for information about the core language. Refer to it for information about the syntax, type system, and other language features.

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

- Definition search engines provided by the Lean language server in the editor (and hosted online):
  - Based on using meta-variables and the type system: [Loogle](https://loogle.lean-lang.org/).
  - Search using natural language: [Moogle](https://moogle.ai/).

To open `loogle` in VS Code, you can use the command palette (`Ctrl + Shift + P`) and type `Loogle: Search for a definition`. You can also use the `#check` command to check the type of a definition or theorem.

Example of an import for a mathematical definition from Mathlib:

```lean
import Mathlib.Algebra.MonoidAlgebra.Basic
#check AddMonoidAlgebra.lift_def
```

### Mathematical learning resources

Good resources to learn how to do (tranditional) formal mathematics in Lean:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)

## Puzzles

In this workshop, we will solve some well-known puzzles and riddles using Lean.

Problem statements and solutions are located in the[`RiddleProofs`](./RiddleProofs) sub-directory.
