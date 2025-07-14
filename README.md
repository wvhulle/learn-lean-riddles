# Learn Lean by solving riddles

(... riddles or computational problems)

This repository contains material for a [workshop on Lean](https://sysghent.be/events/lean/) given on 17th of July 2025 in Ghent for the [SysGhent](https://sysghent.be) community.

**Lean is a functional programming language and theorem prover. It is used to write formal proofs in mathematics, computer science, and other fields.**

A basic introduction to Lean can be found on the [Introduction in the reference](https://lean-lang.org/doc/reference/latest/Introduction/#introduction):

> Leonardo de Moura launched the Lean project when he was at Microsoft Research in 2013, and Lean 0.1 was officially released on June 16, 2014. The goal of the Lean project is to combine the high level of trust provided by a small, independently-implementable logical kernel with the convenience and automation of tools like SMT solvers, while scaling to large problems. This vision still guides the development of Lean, as we invest in improved automation, improved performance, and user-friendliness; the trusted core proof checker is still minimal and independent implementations exist.

A simple example of the syntax of Lean is:

```lean4
theorem Nat.exists_infinite_primes (n : ℕ) :
∃ (p : ℕ), n ≤ p ∧ Prime p
```

Using automated LLM agents with Lean will not be covered in this workshop (although they were used to quickly generate examples). See the [sysghent.be](https://sysghent.be/events) for future events.

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

A typical Lean project's directory tree will look like this:

```txt
riddle-proofs/
├── lake-manifest.json       # Version lock file for dependencies
├── lakefile.lean            # Dependencies and build configuration
├── lean-toolchain           # Enforces a version of Lean
├── LICENSE                  # For publishing on Reservoir
├── Main.lean                # (Optional) Main binary to run Lean code
├── README.md                
├── RiddleProofs.lean        # Exports submodules
├── RiddleProofs/            # (Optional) Sub-module collection
│   ├── Basic.lean           # Prelude
│   ├── MontyHall.lean       # Index file of sub-module MontyHall
│   └── MontyHall/
│       ├── Basic.lean       # Prelude of MontyHall
│       ├── Dilemma.lean     # A file containing definitions
│       └── Measure.lean     # A file that imports Dilemma.lean
```

In this case, there are two build targets:

- The main executable `Main`.
- The main exported library: `RiddleProof`

Both have to be declared in the `lakefile.lean` as build targets. Extra dependencies, needed later on during development, will also be added to `lakefile.lean`. For more information see the [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#--tech-term-pe-configuration).

_Remark: You might see references to `lakefile.toml` format in some documentation. This workshop uses the `lakefile.lean` format which allows for more flexible configuration using Lean code itself._

### Setting toolchain per project

The `lean-toolchain` file in your project root specifies which Lean version to use:

```bash
leanprover/lean4:v4.22.0-rc3
```

This will be updated automatically when you run `lake update`. If you update this manually, make sure the version is compatible with Mathlib or other dependencies.

## Managing dependencies

You can skip this section if you are not interested in using external dependencies.

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

You can also point to local directories for dependencies.

```lean
require «ennreal-arith» from
  "../ennreal"
```


The `lakefile.lean` format gives you the full power of Lean's programming language to configure your build system.

### Updating dependencies

Steps: 

1. Update the `lakefile.lean` file with the new version or path
2. Run the `lake update` command to fetch the new version and update the `lake-manifest.json` file (a kind of version lock-file).
   ```bash
   lake update # Update all exact versions in lock-file
   lake update [DEP_NAME] # Update a specific dependency in lock-file
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

### Importing modules

If you need data structures or things that live in the standard libraries, you have to import the definitions from either the standard library, Mathlib (if it is installed) or other dependencies. Definitions are imported by importing the module that contains them.

Imports have to be placed on the top of the file and are written like this:

```lean
import Std.Data.Foo
```

After inserting a new import, you might need to restart the language server of Lean. VS Code shortcut: `Ctrl + Shift + P` then search for "Lean 4: Restart Server".


### Namespaces

Let's say you are working in a file `Foo.lean` and you have identical identifiers for two different parts of the file. You can separate both using namespaces.

So in `Foo.lean` you would write
```lean
namespace Foo
  theorem duplicated_id : True := trivial
end Foo

theorem duplicated_id : True := trivial
```

The identifiers don't clash, because they are in different namespaces. You can access the first one using `Foo.duplicated_id`. You can also **open a namespace** to avoid writing the full qualified name, but then the identifiers cannot clash (or you will get an error):

```lean
namespace Foo
  theorem id : True := trivial
end Foo 

open Foo
#check id
```

In this case, you didn't need to write `Foo.id`, because you opened the `Foo` namespace. If you had another `id` in the global namespace, it would have caused a clash.

### Modules and namespaces

Every module in Lean creates a namespace with the same name. However, **importing a module does NOT automatically open its namespace**. A **namespace in Lean** is a way to organize identifiers to avoid naming conflicts.

When you have two files `Foo.lean` and `Bar.lean`, you can import `Foo` from `Bar`.

So `Foo.lean` might contain a definition:

```lean
def sum (a b : Nat) : Nat := a + b
```

And `Bar.lean` imports it:

```lean
import Foo
#eval Foo.sum 3 4 -- This will evaluate to 7
```

When you wrote `import Foo`, you imported the `Foo` module, which makes its definitions available under the `Foo` namespace. You need to write `Foo.sum` to access the `sum` function, unless you explicitly open the namespace:

```lean
import Foo
open Foo
#eval sum 3 4 -- Now this works without qualification
``` 


### Obtaining import paths

The easiest way to find the import paths for modules in the standard library is to install `mathlib` and use its [API documentation site](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html). It also includes and re-exports the standard library of Lean. However, for completeness, this section explains how to find the import paths without installing `mathlib`.

### Import paths without Mathlib (optional)

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

### Search proof state

Copy-paste the current proof state in:

https://premise-search.com/


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

- Lemma's defined for the type `ENNReal` (extended non-negative real numbers):
  
  ```lean
  ENNReal _ / _ = _ ↔ _
  ````
  


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

Your package will be automatically listed by [Reservoir](https://reservoir.lean-lang.org/) when it is hosted on Github (and meets the criteria).



## CI

Use the official [Github action](https://github.com/leanprover/lean-action).


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

So, for example, the fully qualified import path of `unusedVariables` is `linter.unusedVariables`. You can enable it with:

- A command in a module:
  ```lean
  set_option linter.unusedVariables true
  ```
- Or globally in your `lakefile.lean` file:
  ```lean
  import Lake
  open Lake DSL
  package «riddle-proofs» where
    leanOptions := #[
      ⟨`linter.unusedVariables, true⟩,
    ]
  ```

Mathlib Linters (only available when Mathlib is a dependency):

| Name                        | Description                                  | Kind     |
|-----------------------------|----------------------------------------------|----------|
| `style.longLine`            | Enforce 100 character line limit            | Style    | 
| `style.commandStart`        | Commands should start at line beginning     | Style    | 
| `style.multiGoal`           | Warn on multiple active goals               | Style    | 
| `style.refine`              | Catch refine' usage                          | Style    |
| `style.docString`           | Enforce docstring format                     | Style    |
| `style.header`              | Enforce strict header format                | Style    | 
| `style.longFile`            | Warn on files > 1500 lines                  | Style    | 
| `style.cdot`                | Check proper cdot usage                      | Style    |
| `style.lambdaSyntax`        | Prefer 'fun' over 'λ'                        | Style    |
| `style.dollarSyntax`        | Prefer '<|' over '$'                         | Style    |
| `style.openClassical`       | Scope classical logic opens                 | Style    | 
| `style.admit`               | Catch admit usage                            | Style    |
| `style.nameCheck`           | Check naming conventions                     | Style    |
| `oldObtain`                 | Modernize obtain usage                       | Advanced |
| `haveLet`                   | Suggest 'let' for non-propositions          | Advanced | 
| `unusedTactic`              | Catch tactics that do nothing               | Advanced | 
| `minImports`                | Check minimal imports                        | Advanced |
| `flexible`                  | Check tactic flexibility                     | Advanced |
| `unnecessarySimpa`          | Suggest simpler simp usage                   | Advanced |
| `omit`                      | Warn against 'omit' usage                   | Advanced | 

Most are enabled by default when you use Mathlib as a dependency. There are two ways to explicitly enable / disable them:

- Enable them globally in your `lakefile.lean` file:
  ```lean
  import Lake
  open Lake DSL
  package «riddle-proofs» where
    leanOptions := #[
      ⟨`linter.style.longLine, true⟩,
    ]
  ```
- Import the `#lint` command from Mathlib and use it in your Lean files:
  
  ```lean
  import Mathlib.Tactic.Linter
  #lint                    -- Run all linters
  #lint only flexible      -- Run only specific linter
  #lint- only oldObtain     -- Run all except specified
  ```
  

See the [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linter.html) for a complete list of available linters for Mathlib.


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

### Visibility

Usually people put code that should be private within a module inside a namespace, named after the build target / project.

The same namespace can be used across different files. Definitions nested under the same namespace (in other files) can see eachother.


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

### Profiling

For benchmarking compilation and type-checking time of user-defined tactics or definitions, you can enable the Lean profiler:

```lean
set_option profiler true
```

### Tracing

Built-in tracing

```lean
set_option trace.Meta.Tactic.simp true
```

Custom tracing. In library code:

```lean4
open Lean 

initialize
  registerTraceClass `ENNRealArith
  registerTraceClass `ENNRealArith.conversion
```

In unit tests:

```lean
set_option trace.ENNRealArith.conversion true in
lemma test_solve_as_real_inverse_1 : (5 : ENNReal)⁻¹ = 1 / 5 := by solve_as_real
```
