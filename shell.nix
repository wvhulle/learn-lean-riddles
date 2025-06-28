# shell.nix
# This shell.nix provides a development environment for lean-lsp-mcp using the custom Nix packaging in lean-lsp-mcp.nix.

let
  pkgs = import <nixpkgs> { };
  leanLspMcp = import ./lean-lsp-mcp.nix { inherit pkgs; };
in
pkgs.mkShell {
  buildInputs = [ leanLspMcp ];
}
