
# Creating your own project

You can make your own packages and redistribute them on GitHub.

Your package will be automatically listed by [Reservoir](https://reservoir.lean-lang.org/) when it is hosted on Github (and meets the criteria).


## New project

To start a new Lean project, `cd` into a new empty directory and run:

```bash
lake init .
lake new myproject .lean
```

The first command initializes a project in the current directory, the second creates a new project directory with a `lakefile.lean` configuration file.

## Setting toolchain per project

The `lean-toolchain` file in your project root specifies which Lean version to use:

```bash
leanprover/lean4:v4.22.0-rc3
```

If you update this manually, make sure the version is compatible with Mathlib or other dependencies.



## Adding dependencies in general

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

## Updating dependencies

Steps: 

1. Update the `lakefile.lean` file with the new version or path
2. Run the `lake update` command to fetch the new version and update the `lake-manifest.json` file (a kind of version lock-file).
   ```bash
   lake update # Update all exact versions in lock-file
   lake update [DEP_NAME] # Update a specific dependency in lock-file
   ```
   
You don't have to run `lake update` when you modify a local dependency referenced in a local folder.


## Download Mathlib cache

If you updated the `mathlib4` package, you need to redownload the pre-compiled cache for Mathlib before you run `lake build` again. This is because the cache is only valid for a specific Mathlib version:

```bash
lake exe cache get
```

_Note: This is automatically done during `lake update` for Mathlib, so manual execution is only needed if you encounter build issues._



## Basic checks in CI

Use the official [Github action](https://github.com/leanprover/lean-action). It seems to require the `lakefile.lean` (opposed to `lakefile.toml`) format.


## Linting

For detecting enabling all lints in a particular module:

```lean
set_option linter.all true
```

If you want to be more specific, you can use tab-autocompletion in the `set_option linter.<tab>` command to see all available checks.

Or have a look at the [Lean linter source code](https://github.com/leanprover/lean4/blob/master/src/Lean/Linter.lean).

## Overview built-in linters

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

## List of Mathlib Linters

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

## Formatting

There is no standard formatter as of July 2025.


## Tests

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

## Profiling

For benchmarking compilation and type-checking time of user-defined tactics or definitions, you can enable the Lean profiler:

```lean
set_option profiler true
```

## Tracing

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


