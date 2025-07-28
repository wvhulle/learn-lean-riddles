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
2. Install Lean locally on your computer and choose your editor:
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

If you update this manually, make sure the version is compatible with Mathlib or other dependencies.

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
   
You don't have to run `lake update` when you modify a local dependency referenced in a local folder.


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

## Learning Lean

### Documentation for beginners

How to choose?

- You are a **mathematician**? 
  - Start with the interactive tutorial "Mathematics in Lean".
  - Look at "100 theorems in Lean".
  - Look at the Mathlib4 index page.
  - Join the "math" channel on [Lean Zulip chat](https://leanprover.zulipchat.com/).
- You are a **developer**? 
  - Start with "Functional programming Lean"
  - Read the [Lean reference manual](https://lean-lang.org/doc/reference/latest/)
- You are a **language nerd**?
  - [Hitchhiker's Guide to Logical Verification (2023 Edition)](https://lean-forward.github.io/hitchhikers-guide/2023/)
  - Read "Tactic programming guide"
  - Read "Metaprogramming in Lean"
- You are **something else**? Try the interactive "Natural number game" at [Lean games (University Düsseldorf)](https://adam.math.hhu.de/).

Don't forget to set your location on the [Lean community map](https://leanprover-community.github.io/meet.html#community-guidelines). You can find in-person Lean courses and workshops on the [event page](https://leanprover-community.github.io/events.html).

### How Lean works

Lean code lives in two "worlds": the world of **syntax** (what you write) and the world of **expressions** (what it means).

#### User's world: `Syntax`

When you write code in a `.lean` file, Lean first sees it as just text. Its first job is to parse this text into a structure called `Syntax`. Think of `Syntax` as a blueprint that describes your code's structure—its notations, commands, and layout.

  * **Macros:** Lean is highly customizable. You can define your own notation (like `a ∣ b` for "a divides b") using **macros**. Macros are rules that transform `Syntax` into other `Syntax` before anything else happens. This lets you shape the language to your needs.

#### Logic's world: `Expr`

For Lean to understand the *mathematical meaning* of your code, it must leave the world of `Syntax`. It converts your code's blueprint into a core logical object called an `Expr` (short for "Expression").

An `Expr` is the fundamental data structure for everything in Lean's logic:

  * A **term** like `$5$` is an `Expr`.
  * A **type** like `ℕ` (the natural numbers) is an `Expr`.
  * A **theorem statement** like `$2 + 2 = 4$` is an `Expr`.
  * A **proof** of that theorem is also an `Expr`.

So types, proofs and terms are just a special kind of `Expr`.  `Expr` is where Lean performs its magic: type checking, proof verification, and logical computation.


#### The bridge: elaboration and the environment

How does `Syntax` become an `Expr`? Through a crucial process called **elaboration**. The elaborator is Lean's "brain." It takes your user-friendly syntax and:

1.  Infers types.
2.  Resolves notation.
3.  Checks for logical correctness.
4.  Translates it all into a well-typed `Expr`.

Once a definition or theorem is successfully elaborated into an `Expr`, it's stored in a global library called the **environment**. When you import `mathlib4`, you are loading its tens of thousands of `Expr`s into this environment, ready for you to use.


#### Talking back to you: delaboration

When Lean needs to show you something—like a proof goal or an error message—it does the reverse process. It takes an internal, computer-readable `Expr` and **delaborates** it back into human-readable `Syntax` to display on your screen.

### Namespaces

**Namespaces** group related definitions to avoid naming conflicts. They work like folders for your code.

```lean
namespace MyLibrary
  def helper : Nat := 42
end MyLibrary

def helper : String := "different helper"
```

Both `helper` functions can coexist because they're in different namespaces. Access the first one with `MyLibrary.helper`.

**Opening namespaces** lets you use short names:

```lean
open MyLibrary
#check helper  -- Now refers to MyLibrary.helper
```

Namespaces with the same name across different files are automatically merged when imported.


### Imports

**Imports** bring definitions from other files into your current file. They're completely different from namespaces.

```lean
import Std.Data.List        -- From standard library
import MyProject.Utils      -- From your project
```

Import paths follow the file structure:
- `Std.Data.List` → file at `Std/Data/List.lean`
- `MyProject.Utils` → file at `MyProject/Utils.lean`

Imports must come before any definitions or `open` statements.

After importing, you can access definitions:

```lean
import MyProject.Utils

-- Use full name
#eval MyProject.Utils.myFunction 42

-- Or open the namespace for short names
open MyProject.Utils
#eval myFunction 42
```

**Import transitivity**: Imports in Lean are **not transitive**. If module B imports module A, and you import module B, you will not automatically see the definitions from module A. You must explicitly import A if you want to use its definitions. This design keeps dependencies explicit and prevents accidental transitive dependencies.




#### Finding the correct import path

**Common confusion**: Documentation often shows namespace qualifiers (like `Std.HashSet`) that don't match the import path you need.

**Why this happens**:
- Namespaces organize APIs logically
- Import paths follow file structure
- One file can export definitions under different namespaces

**How to find the correct import**:

1. **Try the obvious path first**, then experiment:
   ```lean
   import Std.HashSet     -- Might fail
   import Std.Data.HashMap  -- HashSet is actually here
   #check Std.HashSet     -- Now this works
   ```

2. **Use Lean's discovery tools**:
   ```lean
   #check Std.HashSet     -- Tells you if it's available and shows type
   #print Std.HashSet     -- Shows definition if available
   ```

3. **Use VS Code navigation**: Press F12 on any identifier to see its actual file location

4. **Browse the source**: Check the [Lean 4 repository structure](https://github.com/leanprover/lean4/tree/master/src/Std) to see where things actually live

5. **For Mathlib**: Use the [API documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib.html) which shows both namespace and import path 

#### Visibility modifiers

**`private`**: Hides definitions from both namespace opening and imports. Private definitions are only accessible within the same file where they're defined.

**`protected`**: Prevents access via namespace opening but allows access through imports using the full qualified name.

```lean
namespace MyLib
  private def internal_helper : Nat := 42        -- Only visible in this file
  protected def safe_function : Nat := 100       -- Requires MyLib.safe_function even after opening
  def public_function : Nat := 200               -- Accessible as usual
end MyLib

open MyLib
#check public_function     -- ✓ Works
#check safe_function       -- ✗ Error: must use MyLib.safe_function  
#check MyLib.safe_function -- ✓ Works
#check internal_helper     -- ✗ Error: not accessible from other files
```


#### Selective re-export

You can selectively control which definitions from imported modules are available to users of your library:

```lean
-- Import a module but don't expose all its definitions
import SomeLibrary.Internal.Details

-- Re-export only specific definitions you want to expose (TRANSITIVE)
export SomeLibrary.Internal.Details (publicFunction, PublicType)

-- Or selectively open parts of a namespace (LOCAL ONLY)
open SomeLibrary.Internal.Details (publicFunction PublicType)
```

**Important distinction**:
- **`export`**: Makes names available to files that import the current file (transitive)
- **`open`**: Only creates local aliases within the current file (not transitive)

If you want importing files to access the short names, use `export`. If you only want local convenience aliases, use `open`.

This allows you to:
- Hide implementation details while exposing only the public API
- Create a cleaner interface for library users
- Control which transitive dependencies are visible to users of your library



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


There is a new place where you can copy-paste the current proof state and search for theorems that can help you solve it: https://premise-search.com/.

## Practice


### Computational problems

For this workshop, I prepared some example problems. Although not necessarily riddles, the computational problems they involve offer a good starting point for learning: see [`RiddleProofs`](./RiddleProofs) sub-directory.


_**Note**: Many tedious proofs were solved with the help of Claude Opus 4 (not covered in this workshop)._


### Advanced Lean problems

If you are ready for it, continue with more challenging problems. Use the techniques in the proofs to improve your skills.

- Solutions to recent International Mathematical Olympiad problems: <https://dwrensha.github.io/compfiles/imo.html>
- Have a look at the [100 problems](https://leanprover-community.github.io/100.html). The list is inspired by <https://www.cs.ru.nl/~freek/100/>.

### Unformalised problems

When you have had enough of formalised (in Lean) problems, you can find new problems to formalize and solve in [Project Euler](https://projecteuler.net/) if you want to solve new riddles or problems and compete with others.

## Extending the Lean ecosystem

You can make your own packages and redistribute them on GitHub.

Your package will be automatically listed by [Reservoir](https://reservoir.lean-lang.org/) when it is hosted on Github (and meets the criteria).



## Basic checks in CI

Use the official [Github action](https://github.com/leanprover/lean-action). It seems to require the `lakefile.lean` (opposed to `lakefile.toml`) format.


### Linting

For detecting enabling all lints in a particular module:

```lean
set_option linter.all true
```

If you want to be more specific, you can use tab-autocompletion in the `set_option linter.<tab>` command to see all available checks.

Or have a look at the [Lean linter source code](https://github.com/leanprover/lean4/blob/master/src/Lean/Linter.lean).

### Overview built-in linters

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

### List of Mathlib Linters

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

Lean has support for tracing built-in. You can enable display of the tracing for the built-in `simp` tactic with

```lean
set_option trace.Meta.Tactic.simp true
```

Notice that you can click on the objects mentioned in the trace output to see their definitions and types. This is possible because the `trace` command (just like the logging commands) can print either `Syntax` or `Expr` objects. 

- Printing `Syntax` is what you would do in any other language and works like `trace[SCOPE] s!"A = {}"`.
- Printing `Expr` is more powerful. The command `trace[SCOPE] m!"A = {A}"` will print the elaborated `Expr` of `A`, which you can click to see its definition and type.

Tracing can be created in a library that is consumed by another file / library.

```lean
open Lean 

initialize
  registerTraceClass `ENNRealArith
  registerTraceClass `ENNRealArith.conversion
```

The library that imports the library / file with tracing can then (selectively) enable the display of tracing output in the InfoView window:

```lean
set_option trace.ENNRealArith.conversion true in
lemma test_solve_as_real_inverse_1 : (5 : ENNReal)⁻¹ = 1 / 5 := by solve_as_real
```



## Work-arounds

### Changing imports

After changing the import graph of your library (by adding or removing imports from Lean files), you might need to restart the language server of Lean. Find the option in the 'forall'-symbol in the upper-right corner (VS Code shortcut: `Ctrl + Shift + P` then search for "Lean 4: Restart Server".)

It can be partially automated by setting an option for the Lean LSP in VS Code:

```json
{
  "lean4.automaticallyBuildDependencies": true,
}
```


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