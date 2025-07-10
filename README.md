# Learn Lean by solving riddles

(... riddles or computational problems)

This repository contains material for a [workshop on Lean](https://sysghent.be/events/lean/) given on 17th of July 2025 in Ghent for the [SysGhent](https://sysghent.be) community.

A basic introduction to Lean can be found on the [Introduction in the reference](https://lean-lang.org/doc/reference/latest/Introduction/#introduction):

> Leonardo de Moura launched the Lean project when he was at Microsoft Research in 2013, and Lean 0.1 was officially released on June 16, 2014. The goal of the Lean project is to combine the high level of trust provided by a small, independently-implementable logical kernel with the convenience and automation of tools like SMT solvers, while scaling to large problems. This vision still guides the development of Lean, as we invest in improved automation, improved performance, and user-friendliness; the trusted core proof checker is still minimal and independent implementations exist.

A simple example:

```lean4
theorem Nat.exists_infinite_primes (n : ℕ) :
∃ (p : ℕ), n ≤ p ∧ Prime p
```

Using LLM's or AI tools / assistants will not be covered in this workshop. See the [sysghent.be](https://sysghent.be/events) for future events.

## Target audience

This workshop is suitable for everyone who:

- is not afraid of mathematics or theorem proving,
- knows at least one functional programming language,
- loves mathematical or logical computational problems.

## Installation

Several options:

1. Use the online [Lean Web Editor](https://live.lean-lang.org/) and don't install anything locally.
2. Download VS Code and install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
3. Install Lean locally on your computer and choose your editor:
    - Use [Visual Studio Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
    - Use [Emacs](https://www.gnu.org/software/emacs/) with [Lean4 mode](https://github.com/leanprover-community/lean4-mode)
    - Use [Vim](https://www.vim.org/) with [lean.nvim](https://github.com/Julian/lean.nvim) plugin

Other editors are not officially supported. For custom setups, you can use command-line tools like the `python` package `leanclient` to implement your own language server integration.

### Installing Lean locally (optional)

In case you choose to install Lean locally:

1. **Windows users**: Use [Windows Subsystem for Linux (WSL)](https://docs.microsoft.com/en-us/windows/wsl/install). Then follow the instructions for Linux below.
2. **Linux / Mac users**: Install the Lean version manager [`elan`](https://github.com/leanprover/elan):

  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
  ```

  This will provide you mainly with two commands:

- `lean` - the Lean compiler and interpreter
- `elan` - the Lean version manager

### Initializing a project

You can just continue with the rest of this workshop in the same folder, but you can also create a new project. To start a new Lean project, `cd` into a new empty directory and run:

```bash
lake init .
lake new myproject .lean
```

The first command initializes a project in the current directory, the second creates a new project directory with a `lakefile.lean` configuration file.

After initialisation, the directory tree will look like this:

```txt
riddle-proofs/
├── lakefile.lean            # Dependencies and build configuration
├── lean-toolchain           # Enforces a version of Lean
├── README.md             
├── Main.lean                # (Optional) Main binary to run Lean code
├── RiddleProofs.lean        # Exports submodules
├── RiddleProofs/
│   ├── Basic.lean           # Conventional sub-module entry-point / prelude
│   └── JealousHusbands.lean # A sub-module
```

Source files that are "top-level entrypoints" (like `/Main.lean` and `/RiddleProofs.lean`) have to be declared in the `lakefile.lean` file.

Extra dependencies, needed later on during development, will also be added to `lakefile.lean`. For more information see the [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#--tech-term-package-configuration).

_Remark: You might see references to `lakefile.toml` format in some documentation. This workshop uses the `lakefile.lean` format which allows for more flexible configuration using Lean code itself._

### Setting toolchain per project

The `lean-toolchain` file in your project root specifies which Lean version to use:

```bash
leanprover/lean4:v4.22.0-rc3
```

This will be updated automatically when you run `lake update`. If you update this manually, make sure the version is compatible with Mathlib or other dependencies.

## Managing dependencies (optional)

You can skip this section if you are not interested in using external dependencies.

### Mathlib dependency

Mathlib is the de-facto standard library of Lean 4 and contains the official standard library as well. It is recommended to add it to every new project. To add Mathlib as a dependency, add this to your `lakefile.lean` file:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5c5a8deb94353f2b659cb9c578fe833f90febac7"
```

**Important**: Since compiling Mathlib from source takes several hours, you must download a pre-compiled cache to avoid long build times.

```bash
lake exe cache get
```

Pre-compiled caches are only available for Mathlib. Other dependencies must be compiled from source.

By default, Lake automatically selects a compatible Mathlib version. You can optionally pin to specific versions.

### Adding dependencies in general

Dependencies are added to the `lakefile.lean` file in the root of your project. Here's a complete sample `lakefile.lean` file:

```lean
import Lake
open Lake DSL

package «riddle-proofs» where
  version := v!"0.1.0"
  keywords := #["mathematics", "puzzles", "proofs"]
  description := "Lean proofs for classic riddles and puzzles"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "5c5a8deb94353f2b659cb9c578fe833f90febac7"

@[default_target]
lean_lib «RiddleProofs» where
  globs := #[.andSubmodules `RiddleProofs]

lean_exe «riddle-proofs» where
  root := `Main
```

You can also point to local directories for dependencies. The `lakefile.lean` format gives you the full power of Lean's programming language to configure your build system.

### Updating dependencies

When you have updated a local or remote dependency, or you want to point to a new version of a dependency, you can update the `lakefile.lean` file with the new version or path.

You then need to update the source code of the dependency. This can be done with the `lake update` command:

```bash
lake update [DEP_NAME] 
```

If you don't want to trigger post-update hooks for Mathlib, you can use:

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update ennreal-arith --no-build
```

To update all dependencies (and the Lean compiler) in the project, you can run:

```bash
lake update
```

### Download Mathlib cache (when needed)

If you updated the `mathlib4` package, you may need to redownload the pre-compiled cache for Mathlib before you run `lake build` again. This is because the cache is only valid for a specific Mathlib version:

```bash
lake exe cache get
```

_Note: This is automatically done during `lake update` for Mathlib, so manual execution is only needed if you encounter build issues._

### Building

Building all dependencies (which can take a while the first time) and  Lean files in the current project:

```bash
lake build
```

You can also compile single files or folders by specifying the module import specifier (useful for debugging):

```bash
lake build RiddleProofs.MontyHall
```

## Learning Resources

### Beginner documentation

If you need a fast-paced introduction you can read [Hitchhiker's Guide to Logical Verification (2023 Edition)](https://lean-forward.github.io/hitchhikers-guide/2023/).

While learning, you may have further questions. Consult the [reference manual](https://lean-lang.org/doc/reference/latest/) for information about the core language. Refer to it for information about the syntax, type system, and other language features.

A few educational interactive problems are provided as games at [University Düsseldorf](https://adam.math.hhu.de/).

### Community resources

If the reference manual is not enough, you can also ask questions on the [Lean Zulip chat](https://leanprover.zulipchat.com/). The community is very welcoming and helpful, so don't hesitate to ask questions.

Don't forget to set your location on the [Lean community map](https://leanprover-community.github.io/meet.html#community-guidelines). You can find in-person Lean courses and workshops on the [event page](https://leanprover-community.github.io/events.html).

### Importing definitions

If you need data structures or things that live in the standard libraries, you have to import the definitions from either the standard library, Mathlib (if it is installed) or other dependencies.

Imports have to be placed on the top of the file and are written like this:

```lean
import Std.Data.Foo
```

After inserting a new import, you might need to restart the language server of Lean. VS Code shortcut: `Ctrl + Shift + P` then search for "Lean 4: Restart Server".

### Namespaces

If you do not want to write `Foo.theorem_1` to reference a theorem inside the `Foo` module, you can also open the namespace `Foo` with `open Foo`. Then you only have to write `theorem_1`. Every module file in Lean is also a namespace. You might have also have nested namespaces inside the module file, like `namespace Bar` in the example below:

```lean
-- In Foo.lean
namespace Bar
  theorem nested_theorem : True := trivial
end Bar

theorem top_level_theorem : True := trivial
```

In this case, you can import the module and open the `Bar` namespace like this:

```lean
import Foo
open Foo.Bar
```

### Obtaining import paths

The easiest way to find the import paths for modules in the standard library is to install `mathlib` and use its [API documentation site](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html). It also includes and re-exports the standard library of Lean. However, for completeness, this section explains how to find the import paths without installing `mathlib`.

### Using the standard library only

Let's say you need a certain module from the standard library called `Foo`. You found it's path in the reference manual. You don't know the fully-qualified import path to use it in your project.

The path in the reference manual to the standard library points to namespaces, not import paths for modules. This might be confusing.

> For example `HashSet` is defined in the namespace `Std.HashSet`, according to the reference manual, but you have to import it like `import Std.Data.HashSet`.

It is easier to use the `Mathlib` dependency instead (which includes the standard library). If you really don't want to use `Mathlib`, you can still find the import path for the module using `git`:

1. Open the `Std` sub-folder of the [Lean 4 repository](https://github.com/leanprover/lean4/tree/master/src/Std)
2. Search for the module file `Foo.lean` in the `Std` folder using the [top search bar](https://github.com/search?q=repo%3Aleanprover%2Flean4%20Foo&type=code) of GitHub.
3. Use the path of the module file, relative to the `src/Std` directory, to create a fully-qualified import statement in Lean. For example, if the file is located at `src/Std/Data/Foo.lean`, you can import it in your Lean source file like this:

   ```lean
   import Std.Data.Foo
   ```

### Finding syntax

For finding special syntax, you can use:

```lean
import Mathlib.Tactic.FindSyntax 
#find_syntax "#lint"
```

## Mathematics

Lean is not only a powerful functional programming language, but is also known for being a flexible proof assistant. It has helped thousands of mathematicians worldwide to formalize starter up-to research-level mathematics.

The best learning resource for mathematics with Lean is the book [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean). It is quite long, but has a lot of step-wise exercises to learn the language and the Mathlib library.

### Searching mathematical patterns

The collection of definitions and theorems in Mathlib is large. Sometimes the naming of the modules, namespaces and proofs is not entirely consistent. Use these resources to find the definitions and theorems you need:

You can use [Loogle](https://loogle.lean-lang.org/) to search for definitions that help to solve a particular open goal. To open `loogle` in VS Code, you can use the command palette (`Ctrl + Shift + P`) and type `Loogle: Search for a definition`.

Examples of Loogle searches:

- To find theorems about addition and less than:

  ```lean
  ?a + ?b < ?c
  ```

- To find theorems about multiplication being associative:

  ```lean
  ?a * (?b * ?c) = (?a * ?b) * ?c
  ```

- To find definitions involving lists and membership:

  ```lean
  ?a ∈ List ?b
  ```

- To find theorems about natural number induction:

  ```lean
  (?P 0) → (∀ n, ?P n → ?P (n + 1)) → ∀ n, ?P n
  ```
  
### Searching mathematical concepts

You can also search using English / natural language on [Moogle](https://moogle.ai/) or [Lean Explore](https://www.leanexplore.com). For natural language search, simply describe what you're looking for in plain English:

- "addition is associative"
- "if a function is continuous then it is measurable"
- "natural number induction principle"
- "Cauchy-Schwarz inequality"
- "derivative of composition of functions"

If you prefer reading documentation in your browser, you can search on the [HTML pages](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html) with cross-references and syntax highlighting.

## Exercises

In this workshop, we will try to solve some well-known riddles using Lean.

### Famous riddles

Problem statements and solutions for this workshop are located in the [`RiddleProofs`](./RiddleProofs) sub-directory.

_**Note**: This is a work in progress. The code is not complete yet, but the riddles are mostly solvable. Still looking for more riddles! Most of the educational comments are generated by Claude Opus 4._

### Advanced Lean problems

If you are ready for it, continue with more challenging problems. Use the techniques in the proofs to improve your skills.

- Solutions to recent International Mathematical Olympiad problems: <https://dwrensha.github.io/compfiles/imo.html>
- Have a look at the [math index page](https://leanprover-community.github.io/mathlib-overview.html).

### Unformalised problems

When you have had enough of formalised (in Lean) problems, you can have a look at problems that are unformalised:

- Larger, older, well-known (solved) problems in mathematics: <https://www.cs.ru.nl/~freek/100/>

- Also have a look at [Project Euler](https://projecteuler.net/) if you want to solve new riddles or problems and compete with others.

## Extending the Lean ecosystem

You can make your own packages and redistribute them on GitHub.

If certain requirements are met, your package will be automatically listed by [Reservoir](https://reservoir.lean-lang.org/).

### Linting

For detecting enabling all lints in a particular module:

```lean
set_option linter.all true
```

If you want to be more specific, you can use tab-autocompletion in the `set_option linter.<tab>` command to see all available checks.

Or have a look at the [Lean linter source code](https://github.com/leanprover/lean4/blob/master/src/Lean/Linter.lean).

### Overview available linters

Core Lean 4.22.0-rc3 Linters:

| Name                        | Description                                  | Enabled by default | Kind     |
|-----------------------------|----------------------------------------------|--------------------|----------|
| `all`                       | Enable all lints                             | No                 | Basic    |
| `unusedVariables`           | Warn about unused variables                  | Yes                | Basic    |
| `deprecated`                | Warn about deprecated features               | Yes                | Basic    |
| `constructorNameAsVariable` | Warn when variable names match constructors  | Yes                | Basic    |
| `unusedSectionVars`         | Warn about unused section variables          | Yes                | Basic    |
| `missingDocs`               | Require documentation for public definitions | No                 | Advanced |

So, for example, the fully qualified import path of `unusedVariables` is `linter.unusedVariables`. You can enable it with `set_option linter.unusedVariables true`.

Mathlib Linters (only available when Mathlib is a dependency):

| Name                        | Description                                  | Enabled by default | Kind     |
|-----------------------------|----------------------------------------------|--------------------|----------|
| `style.longLine`            | Enforce 100 character line limit            | Yes                | Style    | 
| `style.commandStart`        | Commands should start at line beginning     | Yes                | Style    | 
| `style.multiGoal`           | Warn on multiple active goals               | Yes                | Style    | 
| `style.refine`              | Catch refine' usage                          | Yes                | Style    |
| `style.docString`           | Enforce docstring format                     | No                 | Style    |
| `style.header`              | Enforce strict header format                | No                 | Style    | 
| `style.longFile`            | Warn on files > 1500 lines                  | Yes                | Style    | 
| `style.cdot`                | Check proper cdot usage                      | Yes                | Style    |
| `style.lambdaSyntax`        | Prefer 'fun' over 'λ'                        | Yes                | Style    |
| `style.dollarSyntax`        | Prefer '<|' over '$'                         | Yes                | Style    |
| `style.openClassical`       | Scope classical logic opens                 | Yes                | Style    | 
| `style.admit`               | Catch admit usage                            | Yes                | Style    |
| `style.nameCheck`           | Check naming conventions                     | Yes                | Style    |
| `oldObtain`                 | Modernize obtain usage                       | Yes                | Advanced |
| `haveLet`                   | Suggest 'let' for non-propositions          | Yes                | Advanced | 
| `unusedTactic`              | Catch tactics that do nothing               | Yes                | Advanced | 
| `minImports`                | Check minimal imports                        | No                 | Advanced |
| `flexible`                  | Check tactic flexibility                     | Yes                | Advanced |
| `unnecessarySimpa`          | Suggest simpler simp usage                   | Yes                | Advanced |
| `omit`                      | Warn against 'omit' usage                   | Yes                | Advanced | 


See the [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter.html) for a complete list of available linters for Mathlib.

### Global linter options

You can also set linter options globally for a particular build target in the `lakefile.lean` file:

```lean
import Lake
open Lake DSL

package «riddle-proofs» where
  version := v!"0.0.1"
  leanOptions := #[
    ⟨`linter.all, false⟩,                         
    ⟨`linter.unusedVariables, true⟩,                  
  ]
```

Turn linter warnings into errors:

```lean

@[default_target]
lean_lib «RiddleProofs» where
  leanOptions := #[
    ⟨`warningAsError, true⟩,           
  ]
```

### Formatting

There is no standard formatter as of July 2025.


### Profiling

For benchmarking compilation and type-checking time:

```lean
set_option profiler true
```

Use `#lint` for catching stylistic issues in Mathlib.


### Tests

Your [`lakefile.lean`](./lakefile.lean) should contain a "test driver" that depends on your main exported library:

```lean
import Lake
open Lake DSL

@[default_target]
lean_lib «RiddleProofs» where
  globs := #[.andSubmodules `RiddleProofs]

@[test_driver]
lean_lib «RiddleTest» where
  globs := #[.andSubmodules `RiddleTest]
  needs := #[RiddleProofs]
```

Then you can just run `lake test` to run all tests defined under the sub-directory `RiddleTest`.

## CI

Use the official [Github action](https://github.com/leanprover/lean-action).
