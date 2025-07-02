# Learn Lean by solving riddles

This are notes for a [workshop on Lean](https://sysghent.be/events/lean/) given on 17th of July 2025 in Ghent for [SysGhent](https://sysghent.be).

A basic introduction to Lean can be found on the [Introduction in the reference](https://lean-lang.org/doc/reference/latest/Introduction/#introduction):

> Leonardo de Moura launched the Lean project when he was at Microsoft Research in 2013, and Lean 0.1 was officially released on June 16, 2014. The goal of the Lean project is to combine the high level of trust provided by a small, independently-implementable logical kernel with the convenience and automation of tools like SMT solvers, while scaling to large problems. This vision still guides the development of Lean, as we invest in improved automation, improved performance, and user-friendliness; the trusted core proof checker is still minimal and independent implementations exist.

A simple example:

```lean4
theorem Nat.exists_infinite_primes (n : ℕ) :
∃ (p : ℕ), n ≤ p ∧ Prime p
```

A team from Google managed to solve some of the International Mathematical Olympiad (IMO) problems using Lean 4 and the Mathlib library. See the blog post [AI solves IMO problems at silver medal level](https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/) for more information.


## Target audience

This workshop is suitable for everyone who:

- is not afraid of mathematics or theorem proving,
- knows at least one functional programming language,
- loves mathematical or logical computational problems.

## Installation

You can either use the online [Lean Web Editor](https://live.lean-lang.org/) or install Lean locally on your computer.

### Editor

The recommended editor is [Visual Studio Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4). Emacs and Vim are also supported but may be more challenging for beginners.

### Installing Lean locally

For complete installation instructions, see the [official Lean installation guide](https://lean-lang.org/doc/reference/latest/Setup/#installation).

Quick summary:
1. **Windows users**: Use [Windows Subsystem for Linux (WSL)](https://docs.microsoft.com/en-us/windows/wsl/install)
2. **All platforms**: Install [`elan`](https://github.com/leanprover/elan) to manage Lean toolchains

```bash
# Install elan (provides `lean` and `lake` commands)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Managing Lean toolchain

### Check current version
```bash
lean --version
elan show
```

### Update toolchain
```bash
# Update to latest stable
elan update

# Install specific version
elan install leanprover/lean4:v4.22.0
elan default leanprover/lean4:v4.22.0
```

### Project-specific toolchain

The `lean-toolchain` file in your project root specifies which Lean version to use:

```
leanprover/lean4:v4.22.0-rc2
```

Toolchain management workflow:
1. Check compatibility between your Lean version and Mathlib version
2. Update gradually - don't jump multiple major versions at once
3. Test after updates: run `lake build` to ensure everything still compiles
4. Update cache: run `lake exe cache get` after toolchain changes

When to update Lean:
- When you need new language features
- When Mathlib requires a newer version
- For security updates (rare but important)
- **Caution**: Major version updates may break existing code

## Dependency management

### Adding dependencies

Mathlib is the de-facto standard library of Lean 4 and contains the official standard library as well. To add Mathlib as a dependency, add this to your `lakefile.toml`:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

Version pinning (optional):

By default, Lake automatically selects a compatible Mathlib version. You can optionally pin to specific versions:

```toml
# Option 1: Pin to a stable release (recommended for production)
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.9.1"

# Option 2: Pin to a specific commit (for exact reproducibility)
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "99042f33ebede3d0a9893f0e8021575d50c5354e"

# Option 3: Use development branch (for latest features)
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "master"
```

When to pin versions:
- No pinning: Best for development with cutting-edge Lean versions (like this project)
- Release tags: For stable projects that need tested, documented versions
- Commit hashes: For published research or when exact reproducibility is critical

Finding other packages: Search for additional Lean packages at [Reservoir](https://reservoir.lean-lang.org/).

### Updating dependencies

```bash
# Update all dependencies
lake update

# Update specific dependency
lake update mathlib
```

When to update:
- After adding new dependencies to `lakefile.toml`
- When you want the latest compatible versions
- When switching Lean toolchain versions

### Building and cache

Getting Mathlib cache (recommended first step):
```bash
lake exe cache get
```

Important: `lake exe cache get` is only for Mathlib, not for other dependencies. This is a special tool provided by Mathlib to download pre-compiled binaries.

Building from source:
```bash
# Build everything
lake build

# Build specific target
lake build RiddleProofs
```

When to use cache vs build:
- Always use cache first for Mathlib (saves 30-60 minutes)
- Use cache after updating Mathlib dependency or when Mathlib files are compiling from scratch
- Use build for your own code changes or other small dependencies
- Why cache matters: Mathlib is huge (~1GB compiled), other packages compile quickly from source



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

## Learning Resources

### Beginner documentation

If you need a fast-paced introduction you can read [Hitchhiker's Guide to Logical Verification (2023 Edition)](https://lean-forward.github.io/hitchhikers-guide/2023/).


While learning, you may have further questions. Consult the [reference manual](https://lean-lang.org/doc/reference/latest/) for information about the core language. Refer to it for information about the syntax, type system, and other language features.

A few educational interactive problems are provided as games at [University Düsseldorf](https://adam.math.hhu.de/).

### Linting

Use `#lint` for catching stylistic issues. Seems to be unsupported by MCP

There is no standard formatter as of June 2025.


### Community resources

If the reference manual is not enough, you can also ask questions on the [Lean Zulip chat](https://leanprover.zulipchat.com/). The community is very welcoming and helpful, so don't hesitate to ask questions.

Don't forget to set your location on the [Lean community map](https://leanprover-community.github.io/meet.html#community-guidelines). You can find in-person Lean courses and workshops on the [event page](https://leanprover-community.github.io/events.html).

### Importing definitions

If you need data structures or things that live in the standard libraries, you have to import the definitions from either the standard library, Mathlib (if it is installed) or other dependencies.

Imports have to be placed on the top of the file and are written like this:

```lean
import Std.Data.Foo
```

After insterting a new import, you might need to restart the language server of Lean. VS Code shortcut: `Ctrl + Shift + X`.

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

The collection of definitions and theorems in Mathlib is large. Sometimes the naming of the modules, namespaces and proofs is not entirly consistent. Use these resources to find the definitions and theorems you need:

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

### Hints for certain math topics

(Work-in-progress)

For computing sums of weight functions explicitly as a real number, you might have to map the index set to an equivalent set that is easier to enumerate. This requires you to define an equivalent set and prove an equivalence relation.

Unfinished proof states may suggest that you need complex types such as  `ENNReal` (extended non-negative real numbers)  for making a proof pass. However, avoid such specific types and use instead common types such as `Real`.

When you become more proficient, it is recommended to replace mentions of `Nat` or `Real` by fields or other algebraic structures. Such concepts are encoded in Lean by using type classes. One of the simpler type classes is `Monoid` (a type with an associative binary operation and an identity element). When you use type classes instead of concrete types,  you can re-use the same definitions and theorems for different types of sets.

## Riddles

In this workshop, we will try to solve some well-known riddles using Lean.

### Simple

Problem statements and solutions for this workshop are located in the [`RiddleProofs`](./RiddleProofs) sub-directory.

_**Note**: This is a work in progress. The code is not complete yet, but the riddles are mostly solvable. Still looking for more riddles!_


### Harder

If you are ready for it, continue with more challenging problems. Use the techniques in the proofs to improve your skills.

- Larger, older, well-known (solved) problems in mathematics: https://www.cs.ru.nl/~freek/100/
- Solutions to recent International Mathematical Olympiad problems: https://dwrensha.github.io/compfiles/imo.html
- Have a look at the [math index page](https://leanprover-community.github.io/mathlib-overview.html).




## Lean and AI


### Install extension

Install an extension in your editor that can do inference of strong LLM AI models:

- [Continue](https://docs.continue.dev)
- [Copilot Chat](https://marketplace.visualstudio.com/items?itemName=GitHub.copilot-chat)

To be able to let LLMs search online from Copilot Chat, you have install an extension in VS Code: `ms-vscode.vscode-websearchforcopilot`. Enable it in the context settings.

Ideally, the extension should support edit/agent mode and custom MCP servers.


### MCP server

LLMs cannot see all proof context by default. For that, you need to install a local MCP server for the Lean language server (`lean-lsp`) and add it to the settings of your editor.

#### Ubuntu / Fedora / etc.

Install the MCP server from [`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp/tree/main). Follow the project's instructions or use the `shell.nix` provided with this project to install it. You have to add it to your user `settings.json` file in VS Code:

```json
{
    "mcp": {
        "servers": {
            "lean-lsp": {
                "command": "uvx",
                "args": ["lean-lsp-mcp"],
            }
        }
    }
}
```

#### NixOS

In case you use the `shell.nix` file, you can instead use this setting in your workspace's `settings.json` file (already included in this project):

```json
{
    "mcp": {
        "servers": {
            "lean-lsp": {
                "command": "lean-lsp-mcp",
            }
        }
    }
}
```

For VS Code to discover this binary, you have to launch VS Code from the shell where you have installed the MCP server. 

```bash
nix-shell
code .
```

Or if you want it to happen automatically:

```bash
direnv allow
``` 

### Usage

The easiest way to use AI in Lean is to use [Copilot Chat](https://github.com/features/copilot). Install the extension in VS Code and click on the icon next to the search bar on the top of the window. On the right appears a sidebar with a chat interface. You can ask questions about Lean code, Mathlib, or even ask it to write code for you.  

Switch the mode from "Ask" to "Agent". Select Claude Sonnet 4 from the model selection menu. Claude 4 is not completely free, but seems to be the best at agentic coding on Lean4 code, because it has a slightly deeper understanding of the APIs and respects context such as MCP or system prompts better.


Now you can select parts of your Lean code that are incomplete or problematic, and ask the LLM to fix them. Any LLM will fail when you provide too much context. Ideally, you should select fewer than 5 problematic Lean source code lines before you start any LLM in agentic coding mode. Errors that cover more than 10 source code lines will easily confuse the LLM and time-out or give up after > 10 frustrating minutes.

As you go along, you will notice quirks and undesirable behaviour of the LLM. You can fix this by providing the right context. Adjust the instructions in [`.github/copilot-instructions.md`](.github/copilot-instructions.md). These instructions will be passed to every conversation with any LLM using Copilot Chat. You should also make sure the MCP server for Lean is configured. Click on the "tools" icon on the bottom left. Scroll down and toggle the Lean MCP server that you added previously to the settings. 

### Explore models

If you want to try another model than Claude 4, you should have a look at the [Vellum leaderboard](https://www.vellum.ai/llm-leaderboard#) for more models. It is also recommended to create an account on OpenRouter, and configure OpenRouter as an LLM inference provider in VS Code. Local LLMs such LLama 3.2 hosted by `ollama` can also be used, but they are not as powerful as the cloud-based LLMs. You have to check whether the local LLM supports function / tool calling or MCP servers. You might have to fine-tune a local model on Lean code to get better results (using Unsloth).



