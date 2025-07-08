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

Using LLMs or AI tools / assistants will not be covered in this workshop. See the [sysghent.be](https://sysghent.be/events) for future events.

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
    - Use [Vim](https://www.vim.org/)

Other editors are not supported as far as I know. Use command-line tools like the `python` package `leanclient` to implement your own language server.

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
lake init
```

After initialisation with `lake init`, you'll get a basic structure like:

```txt
my-project/              # (your chosen project name)
├── lakefile.toml        # Dependencies
├── lean-toolchain       # Enforces a version of Lean
├── README.md            
└── Main.lean            # Main entry point
```

The more complex structure shown below is specific to this riddle-proofs project:

```txt
riddle-proofs/
├── lakefile.toml            # Dependencies
├── lean-toolchain           # Enforces a version of Lean
├── README.md             
├── Main.lean                # (Optional) Main binary to run Lean code
├── RiddleProofs.lean        # Exports submodules
├── RiddleProofs/
│   ├── Basic.lean           # Conventional sub-module entry-point / prelude
│   └── JealousHusbands.lean # A sub-module
```

Source files that are "top-level entrypoints" (like `/Main.lean` and `/RiddleProofs.lean`) have to be declared in the `lakefile.toml` file.

Extra dependencies, needed later on during development, will also be added to `lakefile.toml`. For more information see the [Lake documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#--tech-term-package-configuration).

_Remark: On some sites, you might see there is a `lakefile.lean` instead of `lakefile.toml`. In this project we will stick to the TOML variant._

The `lean-toolchain` file in your project root specifies which Lean version to use:

```
leanprover/lean4:v4.22.0-rc3
```

Note: The `lean-toolchain` file is NOT automatically updated by `lake update`. You need to manually update it if you want to change the Lean version.

## Managing dependencies (optional)

You can skip this section if you are not interested in using external dependencies.

See also the [Lake documentation](https://github.com/leanprover/lean4/blob/master/src/lake/README.md).

### Mathlib dependency

Mathlib is the mathematical library for Lean 4 that extends the standard library (std4) with comprehensive mathematical definitions and theorems. It is recommended to add it to projects that need mathematical concepts. To add Mathlib as a dependency, add this to your `lakefile.toml`:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

**Remark**: Since compiling Mathlib would take several hours, you have to download a pre-compiled cache.

```bash
lake exe cache get
```

This is only possible for Mathlib, not for other dependencies.

By default, Lake automatically selects a compatible Mathlib version. You can optionally pin to specific versions.

### Adding dependencies in general

In general dependencies are added to the `lakefile.toml` file in the root of your project.

When a dependency is available through [Reservoir](https://reservoir.lean-lang.org/), you can add it with:

```toml
[[require]]
name = "<package-name>"    # Replace with actual package name
scope = "<package-owner>"  # Replace with actual owner/organization
```

Otherwise, you can add a local dependency (only available on your pc):

```toml
[[require]]
name = "ennreal-arith"
path = "../ennreal"
```

Usually, you want to add Git dependencies with:

```toml
[[require]]
git = "https://github.com/wvhulle/ennreal-arith"
name = "ennreal-arith"
rev = "main"
```

There is also another format for dependencies available: `lakefile.lean`.

### Updating dependencies

When you have updated a local or remote dependency, or you want to point to a new version of a dependency, you can update the `lakefile.toml` file with the new version or path.

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

Or, if you don't want to re-compile dependencies that are available in the remote cache, you can download them from the remote cache:

```bash
lake exe cache get
```

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

After inserting a new import, you might need to restart the language server of Lean. VS Code: `Ctrl + Shift + P` then search for "Lean 4: Restart Server".

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

It is easier to use the `Mathlib` dependency instead (which includes the standard library). If you really don't want to use `Mathlib`, you can still find the import path for the module:

Note: The standard library (std4) is now in a separate repository at <https://github.com/leanprover/std4>. To find import paths:

1. Browse the [std4 repository](https://github.com/leanprover/std4)
2. Navigate to the module you need
3. Use the path relative to the repository root as your import path

For example, if the file is at `Std/Data/HashSet.lean`, import it as:

```lean
import Std.Data.HashSet
```

### Finding syntax

For finding special syntax, you can use:

```lean
import Mathlib.Tactic.FindSyntax 
#find_syntax "#lint"
```

## Mathematics

Lean is not only a powerful functional programming language, but is also known for being a flexible proof assistant. It has helped thousands of mathematicians worldwide to formalize starter up to research-level mathematics.

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

_**Note**: This is a work in progress. The code is not complete yet, but the riddles are mostly solvable. Still looking for more riddles!_

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

For detecting dead code:

```lean
set_option linter.all true
```

For benchmarking compilation and type-checking time:

```lean
set_option profiler true
```

Use `#lint` for catching stylistic issues in Mathlib.

There is no standard formatter as of June 2025.

### Tests

Your [`lakefile.toml`](./lakefile.toml) should look like:

```toml
defaultTargets = ["ENNRealTest"] # Include the test library.
testDriver = "TestRunner"   # Point to the test runner script, written in Lean.

[[lean_lib]]                # The tests are in a self-contained library.
name = "ENNRealTest"        # Be careful not to choose `Test` because it is usually taken.
                            # Usually people prefix the main library name.
[[lean_exe]]
name = "TestRunner"         # This is the testing entry point. 
```

The `TestRunner` executable points to a file `TestRunner.lean` located at the root of the repository with contents:

```lean
import ENNRealTest.Unit     # Reference modules in the test sub-module.
import ENNRealTest.Integration

def main : IO Unit := do
  IO.println "Tests completed successfully"
```

Then you can just run `lake test` to run `TestRunner` (after trying to compile the testing library).

### Using @[test_runner] attribute (to be checked)

You can also use the `@[test_runner]` attribute for a more lightweight testing approach:

```lean
-- In a test file like Test/Basic.lean
import Lean

@[test_runner]
def testRunner : IO Unit := do
  -- Run your tests here
  IO.println "Running tests..."
  assert! (1 + 1 = 2)
  IO.println "All tests passed!"
```

This approach doesn't require a separate test executable in your lakefile.
