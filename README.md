# Collection of riddles and puzzles in Lean 4

This is a collection of riddles and puzzles implemented in Lean 4 for a workshop given on 17th of July 2025 at Ghent.

## Lean 4

Lean code is written in side the files (indirectly) referenced in the `lakefile.toml` file.

## Standard library

```lean
import Std.Data.HashSet
```

## Mathlib

Add dependency on Mathlib:<https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency>

Inside the `lakefile.toml` file, add the following lines:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

```bash
lake update mathlib
```

Search for the theorems that you need in Mathlib:

- Loogle, Moogle
- Directly in the browser: <https://leanprover-community.github.io/mathlib4_docs/Mathlib.html>

Import

```lean
import Mathlib.Algebra.MonoidAlgebra.Basic
#check AddMonoidAlgebra.lift_def
```

## Changing imports

It seems like you have to rerun "restart file" when you change the imports in the file. Shortcut: `Ctrl + Shift + X`.
