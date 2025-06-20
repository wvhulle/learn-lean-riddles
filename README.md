# Riddles in Lean

This is a collection of riddles and puzzles implemented in Lean 4 for a [workshop](https://sysghent.be/events/lean/) given on 17th of July 2025 in Ghent for [SysGhent](https://sysghent.be).

## Getting started (for new users)

If you have never used Lean before, you will have to install some system dependencies and tools to get started.

### Editor

Unfortunately, there is not that much choice for Lean editors. The recommended editor is [Visual Studio Code](https://code.visualstudio.com/), which has a [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) that provides syntax highlighting, code completion, and other features.

### Installing toolchain

Install [`elan`](https://github.com/leanprover/elan), to manage Lean toolchains. It provides the `lean` and `lake` commands.

_Remark: Installing `elan` installs two executables. The executable `lake` has a similar role as cargo and `lean` is similar to `rustc`._

### Initializing a project

You can just continue with the rest of this workshop in the same folder, but you can also create a new project. To start a new Lean project, `cd` into a new empty directory and run:

```bash
lake init
```

After initialisation, the directory tree will look like this:

```txt
riddle-proofs/
├── lakefile.toml         # Project configuration for Lake (Lean's build tool)
├── lean-toolchain        # Specifies the Lean toolchain version to use
├── README.md             # Project documentation and instructions
├── Main.lean             # (Optional) Main entry point for the project, often imports or runs top-level code
├── RiddleProofs.lean     # (Optional) Index file for the RiddleProofs/ folder, re-exports submodules
├── RiddleProofs/
│   ├── Basic.lean        # (Example) A Lean file for basic definitions or warm-up exercises
│   └── JealousMath.lean  # A Lean file containing the code and proofs for the "Jealous Mathematicians" puzzle
```

Source files that are "top-level entrypoints" (like `/Main.lean` and `/RiddleProofs.lean`) have to be declared in the `lakefile.toml` file.

Extra dependencies, needed later on during development, will also be added to `lakefile.toml`. For more information see the [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#--tech-term-package-configuration).

_Remark: On some sites, you might see there is a `lakefile.lean` instead of `lakefile.toml`. In this project we will stick to the TOML variant._

### Language documentation

If you need a fast-paced introduction you can read [Hitchhiker's Guide to Logical Verification (2023 Edition)](https://lean-forward.github.io/hitchhikers-guide/2023/).

While learning, you may have further questions. Consult the [reference manual](https://lean-lang.org/doc/reference/latest/) for information about the core language. Refer to it for information about the syntax, type system, and other language features.

If the reference manual is not enough, you can also ask questions on the [Lean Zulip chat](https://leanprover.zulipchat.com/). The community is very welcoming and helpful, so don't hesitate to ask questions.

### Importing modules

If you need data structures or things that live in the standard libraries, you have to import the definitions from the standard library.

After writing an import like this for a Lean module, the definitions from the module become available in the current Lean source file.

```lean
import Std.Data.HashSet
```

You might need to restart the language server of Lean in your editor after changing an import. Shortcut: `Ctrl + Shift + X`.

### Obtaining import paths

The easiest way to find the import paths for modules in the standard library is to install `mathlib` and use its [API documentation site](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html). It also includes and re-exports the standard library of Lean. However, for completeness, this section explains how to find the import paths without installing `mathlib`.

Let's say you need a certain module from the standard library called `Foo`. You don't know the fully-qualified import path to use it in your project.

1. Open the `Std` sub-folder of the [Lean 4 repository](https://github.com/leanprover/lean4/tree/master/src/Std)
2. Search for the module file `Foo.lean` in the `Std` folder using the [top search bar](https://github.com/search?q=repo%3Aleanprover%2Flean4%20Foo&type=code) of GitHub.
3. Use the path of the module file, relative to the `src/Std` directory, to create a fully-qualified import statement in Lean. For example, if the file is located at `src/Std/Data/Foo.lean`, you can import it in your Lean source file like this:

    ```lean
    import Std.Data.Foo
    ```

_**Important**: References to the definitions in the standard library in the reference manual point to namespaces (not import paths for modules)._

> For example `HashSet` is defined in the namespace `Std.HashSet`, according to the reference manual, but you have to import it like `import Std.Data.HashSet`.

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

### More learning resources

Good resources to learn how to do (traditional) formal software verification or mathematics in Lean:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)

## Puzzles

In this workshop, we will solve some well-known puzzles and riddles using Lean.

Problem statements and solutions for this workshop are located in the [`RiddleProofs`](./RiddleProofs) sub-directory.

_**Note**: This is a work in progress. The code is not complete yet, but the puzzles are mostly solvable. Still looking for more riddles!_
