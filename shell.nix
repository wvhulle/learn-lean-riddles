let
  pkgs = import <nixpkgs> { };
  leanLspMcp = import ./lean-lsp-mcp.nix { inherit pkgs; };
in
pkgs.mkShell {
  buildInputs = with pkgs; [
    leanLspMcp
    bash
    elan
    mathlibtools
    git
  ];
}
