
# Installation of Lean

Several options:

1. Use the online [Lean Web Editor](https://live.lean-lang.org/) and don't install anything locally.
2. Install Lean locally on your computer and use your editor of choice.


## Lean on Linux

Install the Lean version manager [`elan`](https://github.com/leanprover/elan):

```bash
sudo apt install elan   # Ubuntu / WSL
nix-shell -p elan       # NixOS
```

This will provide you mainly with two commands:

- `lean` - the Lean compiler and interpreter
- `elan` - the Lean version manager

## Lean on Windows

Install WSL (Windows subsystem for linux):

1. Search for "turn windows features on / off" in start menu. Reboot.
2. Run powershell as admin
3. Type `wsl --install` to install Ubuntu within your Windows installation.
4. Pick password. If you made a mistake, you can do `wsl -u root` and run `passwd $USER`.
5. Launch Ubuntu with `wsl`.


Now you can now follow the installation steps for Linux inside WSL.

## Clone this project

You can now clone this project from a Linux shell to your Linux home directory with:

```bash
git clone https://github.com/wvhulle/learn-lean-riddles ~/learn-lean-riddles
```

In Windows, it is important not to clone it from the Windows environment, but within an Linux WSL environment. Otherwise, the filesystem permissions of the Windows filesystem will give problems for WSL.

## Initial build

After you have installed `elan` and you just `git` cloned this project, you should do:

```bash
cd ~/learn-lean-riddles
lake exe cache get        # Important: download a pre-compiled cache of Mathlib
lake build                # Important: only do this after downloading the cache 
```

## Download an editor

The editor recommended by the Lean organization is [Visual Studio Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).


For Linux, follow [Microsoft instructions](https://code.visualstudio.com/docs/setup/linux). On Windows, you can install VS Code using a PowerShell terminal with:

```ps
winget install Microsoft.VisualStudioCode
```

There are some alternative editors with Lean extensions: 

- Use [Emacs](https://www.gnu.org/software/emacs/) with [Lean4 mode](https://github.com/leanprover-community/lean4-mode)
- Use [Vim](https://www.vim.org/) with [lean.nvim](https://github.com/Julian/lean.nvim) plugin


## Configure editor on Windows

On Linux the editor VS Code does not need to be configured. On Windows, you can configure it to run within a Linux container:

1. Open this repository as a folder with VS Code using file manager (click right on folder)
2. Install the extension `ms-vscode-remote.remote-wsl` if it is not installed already.
3. earch for the command (`CTRL-SHIFT-P`) `WSL: Open folder in WSL..` 
4. Open a terminal. It should open a Linux Bash shell.

If you installed WSL in the previous steps, you are now running VS Code within WSL and you can use Linux shell and Linux-specific development commands in the terminal.



During development, you can also press the "forall" symbol on the top-right of an opened Lean file and select "rebuild" / "reload". 




## Changing imports

After changing the import graph of your library (by adding or removing imports from Lean files), you might need to restart the language server of Lean. Find the option in the 'forall'-symbol in the upper-right corner (VS Code shortcut: `Ctrl + Shift + P` then search for "Lean 4: Restart Server".)

It can be partially automated by setting an option for the Lean LSP in VS Code:

```json
{
  "lean4.automaticallyBuildDependencies": true,
}
```