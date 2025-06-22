# Riddles in Lean

This is a collection of riddles implemented in Lean 4 for a [workshop](https://sysghent.be/events/lean/) given on 17th of July 2025 in Ghent for [SysGhent](https://sysghent.be).

## Target audience

This workshop is suitable for everyone who:

- is not afraid of mathematics or theorem proving,
- knows at least one functional programming language,
- loves mathematical or logical riddles.

## Installation

You choose to use the online instance at [Lean Web Editor](https://live.lean-lang.org/) or you can install Lean locally on your computer.

### Editor

Unfortunately, there is not that much choice for Lean editors. The recommended editor is [Visual Studio Code](https://code.visualstudio.com/). Emacs and Vim are also supported, but the experience may be harder.

A linter is available for VS Code as a [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) that provides syntax highlighting, code completion, and other features. There is no formatter for Lean code available yet.

### Installing toolchain

If you have never used Lean before, you will have to install some system dependencies and tools to get started.

For Windows users, it is recommended to use the [Windows Subsystem for Linux (WSL)](https://docs.microsoft.com/en-us/windows/wsl/install) to run Lean. This way, you can use the same commands as on Linux and macOS.

Install [`elan`](https://github.com/leanprover/elan), to manage Lean toolchains. It provides the `lean` and `lake` commands.

_Remark: Installing `elan` installs two executables. The executable `lake` has a similar role as cargo and `lean` is similar to `rustc`._

## Getting started

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

A basic introduction can be found on the [Introduction in the reference](https://lean-lang.org/doc/reference/latest/Introduction/#introduction):

> Leonardo de Moura launched the Lean project when he was at Microsoft Research in 2013, and Lean 0.1 was officially released on June 16, 2014. The goal of the Lean project is to combine the high level of trust provided by a small, independently-implementable logical kernel with the convenience and automation of tools like SMT solvers, while scaling to large problems. This vision still guides the development of Lean, as we invest in improved automation, improved performance, and user-friendliness; the trusted core proof checker is still minimal and independent implementations exist.

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

Lean is both a functional programming language and a flexible proof assistant. 

The best learning resource for mathematics with Lean is the book [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean).

An interactive tutorial / Lean learning game is available at  [University Düsseldorf](https://adam.math.hhu.de/)

### AI / LLMs and Lean

A team from Google managed to solve some of the International Mathematical Olympiad (IMO) problems using Lean 4 and the Mathlib library. See the blog post [AI solves IMO problems at silver medal level](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) for more information.

As of June 2025, the status of LLMs and Lean for ordinary users is:

- GPT4.1 is well integrated in VS Code.
- Claude 4 is good at refactoring Lean4 code (using the Copilot Chat Agent). 

One thing that is lacking is a fine-tuned LLM that is trained on the standard library code and the large Mathlib library. 

_Remark: To build a fine-tuned Lean model, you need to start from a popular open model like LLama 3.1. First, you have to create good dataset with any language. Training / fine-tuning can only be done in Python and using a fine-tuning framework like [Unsloth](https://unsloth.ai/). Afterwards you can do inference with any inference engine._

### Mathlib

All of undergraduate and graduate (even PhD) mathematics is formalized in Lean 4's Mathlib library. It contains a lot of mathematical definitions and theorems, which are useful for writing mathematical proofs in Lean.

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


## Riddles

In this workshop, we will solve some well-known riddles using Lean.

### Problem statements and solutions

Problem statements and solutions for this workshop are located in the [`RiddleProofs`](./RiddleProofs) sub-directory.

_**Note**: This is a work in progress. The code is not complete yet, but the riddles are mostly solvable. Still looking for more riddles!_

## Contributing

If you want to add formalizations of new riddles to this collection, you can find some on [Reddit/Mathriddles](https://www.reddit.com/r/mathriddles/).


