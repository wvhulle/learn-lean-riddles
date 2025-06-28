let
  pkgs = import <nixpkgs> { };
  leanLspMcp = import ./lean-lsp-mcp.nix { inherit pkgs; };
in
pkgs.mkShell {
  buildInputs = [ leanLspMcp ];
}
