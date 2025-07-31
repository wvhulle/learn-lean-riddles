
## Structure of the project

The folder structure of a Lean project is flexible, but it seems like most projects have a structure that looks like this:

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


## Building

Building all dependencies (which can take a while the first time) and  Lean files in the current project:

```bash
lake exe cache get
lake build
```

You can also compile single files or folders by specifying the module import specifier (useful for debugging):

```bash
lake build RiddleProofs.MontyHall
```

## Organizing Lean code

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


### Sections

A section is something that looks a bit like a namespace, but it is completely different.

Sections are used to declare instances, variable names and types valid within the scope of the section. They do not hide definitions.

```lean
section LinearAlgebra
  variable {α : Type*} [Field α]
  variable (V : Type*) [AddCommGroup V] [Module α V]
  
  def zero_smul : (0 : α) • (v : V) = 0 := sorry
  def add_smul (a b : α) (v : V) : (a + b) • v = a • v + b • v := sorry
  -- Both definitions automatically have access to α, V and their instances
end LinearAlgebra

-- Names are not qualified - they're just `zero_smul` and `add_smul`
#check zero_smul
#check add_smul
```

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




### Finding the correct import path

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

### Visibility modifiers

Lean provides visibility modifiers to control how definitions can be accessed both within the same file and across files:

| Modifier | Access via `open` | Access from other files | Use case |
|----------|------------------|------------------------|----------|
| `private` | No | No | Implementation details, helper functions |
| `local` | Yes | No | Section-local definitions, temporary helpers |
| `protected` | No (requires full name) | Yes (full name only) | API boundaries, prevent name conflicts |
| (default/public) | Yes | Yes | Public API, general use |

**`private`**: Completely file-local. Hidden from both namespace opening and imports.

**`local`**: File-local but accessible via `open`. Cannot be imported by other files.

**`protected`**: Prevents short names via `open` but allows full qualified access from other files.

**public (default)**: No restrictions on access.

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
#check internal_helper     -- ✗ Error: private, not accessible at all
```


### Selective re-export

You can selectively control which definitions from imported modules are available to users of your library using `export` and `open`:

| Command | Scope | Effect on importing files | Use case |
|---------|-------|--------------------------|----------|
| `export ModuleName (item1, item2)` | Transitive | Other files importing this file can access short names | Public API design, controlled re-exports |
| `open ModuleName (item1 item2)` | Local only | No effect on other files | Local convenience, reduce typing |

```lean
-- File: MyLibrary.lean
import SomeLibrary.Internal.Details

-- Re-export only specific definitions (TRANSITIVE)
-- Files importing MyLibrary can use short names
export SomeLibrary.Internal.Details (publicFunction, PublicType)

-- Open parts of a namespace (LOCAL ONLY)  
-- Only this file can use short names
open SomeLibrary.Internal.Details (helperFunction HelperType)

def myFunction := publicFunction + helperFunction  -- Both work here
```

```lean
-- File: Client.lean
import MyLibrary

-- This works because MyLibrary exported publicFunction
#check publicFunction     

-- This fails - helperFunction was only opened locally in MyLibrary
#check helperFunction     -- Error: not found

-- Must use full name for non-exported items
#check SomeLibrary.Internal.Details.helperFunction  -- Works
```

**Key differences**:
- **`export`**: Makes names available to files that import the current file (transitive)
- **`open`**: Only creates local aliases within the current file (not transitive)

**When to use each**:
- Use `export` when you want to provide a clean public API that hides implementation details
- Use `open` when you want local convenience without affecting your module's public interface

This pattern allows you to:
- Hide implementation details while exposing only the public API
- Create a cleaner interface for library users  
- Control which transitive dependencies are visible to users of your library
