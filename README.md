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

You choose to use the online instance at [Lean Web Editor](https://live.lean-lang.org/) or you can install Lean locally on your computer.

### Editor

Unfortunately, there is not that much choice for Lean editors. The recommended editor is [Visual Studio Code](https://code.visualstudio.com/). Emacs and Vim are also supported, but the experience may be harder.

A linter is available for VS Code as a [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) that provides syntax highlighting, code completion, and other features. There is no formatter for Lean code available yet.

### Installing toolchain

If you have never used Lean before, you will have to install some system dependencies and tools to get started.

For Windows users, it is recommended to use the [Windows Subsystem for Linux (WSL)](https://docs.microsoft.com/en-us/windows/wsl/install) to run Lean. This way, you can use the same commands as on Linux and macOS.

Install [`elan`](https://github.com/leanprover/elan), to manage Lean toolchains. It provides the `lean` and `lake` commands.

_Remark: Installing `elan` installs two executables. The executable `lake` has a similar role as cargo and `lean` is similar to `rustc`._

### Mathlib

This is the de-facto standard library of Lean 4 and contains the official standard library as well.

To install Mathlib as a dependency to your current project, follow  the [Mathlib installation instructions](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency).

Inside the `lakefile.toml` file, add the following lines:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

Dependencies are installed and updated with:

```bash
lake update mathlib
```

### LLM


Install an extension in your editor that can do inference of strong LLM AI models:

- [Continue](https://docs.continue.dev)
- [Copilot Chat](https://marketplace.visualstudio.com/items?itemName=GitHub.copilot-chat)

Ideally, the extension should support 
- edit / agent mode
- custom MCP servers


### MCP server

LLMs cannot see all proof context by default. For that, you need to install a local MCP server for the Lean language server (`lean-lsp`) and add it to the settings of your editor (see the installation instructions above).

#### Ubuntu / Fedora / etc.

Install the MCP server from [`lean-lsp-mcp`](https://github.com/oOo0oOo/lean-lsp-mcp/tree/main). Follow the project's instructions or use the `shell.nix` provided with this project to install it. You have to add it to your  user `settings.json` file in VS Code, so that the Lean language server can use it:

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

### Enable in VS Code

Open the Copilot Chat sidebar and click on the "tools" icon on the bottom left. Scroll down and toggle the Lean MCP server that you added previously to the settings.


### Other tools

To be able to let LLMs search online, you have install an extension in VS Code: `ms-vscode.vscode-websearchforcopilot`. Enable it in the context settings.


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
import Std.Data.Foo
open Std.Data.Foo.Bar
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



### Building the project

Successfull compilation of a project in Lean shows that all logical and mathematical statements expressed the type system are valid. To compile (build) the project, run:

```bash
lake build
```

### Cloud LLM inference

Any LLM will fail when you provide too much context. Ideally, you should select fewer than 5 problematic Lean source code lines before you start any LLM in agentic coding mode. Errors that cover more than 10 source code lines will easily confuse the LLM and time-out or give up after > 10 frustrating minutes.

- The free included LLM GPT-4.1 can be used in agentic mode and may come up with creative solutions quickly (in case it uses the MCP server). 
- Claude 4 is not completely free, but seems to be the best at agentic coding on Lean4 code, because it has a slightly deeper understanding of the APIs (and more consistently queries the MCP server). Claude does not have streaming output, so it might seem to hang. 
- Gemini 2.5 Pro is quite smart given the right context. However, it is often slow and does not use the provided MCP server for Lean.

Have a look at [Vellum](https://www.vellum.ai/llm-leaderboard#) for more models. 

### Local inference

Local LLMs such LLama 3.2 hosted by `ollama` can also be used, but they are not as powerful as the cloud-based LLMs and cannot be used in "agent mode" or with an MCP server. You might have to fine-tune them on Lean code to get better results.

_Remark: To build a local fine-tuned Lean model, you need to start from a popular open model like LLama 3.2. First, you have to create good dataset with any language. Training / fine-tuning can only be done in Python and using a fine-tuning framework like [Unsloth](https://unsloth.ai/). Afterwards you can do inference with any inference engine._

### Injecting prompts 

When you use LLMs and repeat yourself often, you can add global or (workspace-local) prompts in VS Code for GitHub Copilot Chat inside [`.github/prompts`](./github/prompts). Search for the command `Chat: new prompt file` in the command palette (`Ctrl + Shift + P`). A few useful prompts were already added to this project as examples.

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
