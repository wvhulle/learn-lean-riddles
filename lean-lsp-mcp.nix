# lean-lsp-mcp.nix
# This file defines how to build the lean-lsp-mcp Python package with Nix
# using standard Python packaging, not uv2nix overlays.

{
  pkgs ? import <nixpkgs> { },
}:

let
  leanclient = pkgs.python3Packages.buildPythonPackage rec {
    pname = "leanclient";
    version = "0.1.12";
    format = "pyproject";
    src = pkgs.python3Packages.fetchPypi {
      inherit pname version;
      sha256 = "sha256-yPALTn0WG9D6fT6jDInRt0y10/iyNIUuPEo42srLcIY=";
    };
    propagatedBuildInputs = with pkgs.python3Packages; [
      poetry-core
      orjson
      tqdm
    ];
    doCheck = false;
  };

  mcp = pkgs.python3Packages.buildPythonPackage rec {
    pname = "mcp";
    version = "1.9.4";
    format = "pyproject";
    src = pkgs.python3Packages.fetchPypi {
      inherit pname version;
      sha256 = "sha256-z7C80alTW0LtrviZR7nhio/rSTYuHMBZ1uf8Y28ssJ8=";
    };
    propagatedBuildInputs = with pkgs.python3Packages; [
      hatchling
      uv-dynamic-versioning
      anyio
      httpx
      httpx-sse
      pydantic
      pydantic-settings
      python-multipart
      sse-starlette
      starlette
      uvicorn
      python-dotenv
      typer
    ];
    doCheck = false;
  };

in
pkgs.python3Packages.buildPythonApplication rec {
  pname = "lean-lsp-mcp";
  version = "0.3.0";
  src = pkgs.fetchFromGitHub {
    owner = "oOo0oOo";
    repo = pname;
    rev = "v${version}";
    sha256 = "sha256-hCEbVoxiUBRysDiNvZyx9nZTxbaAQsgsQTiQvhyLosM=";
  };
  propagatedBuildInputs = with pkgs.python3Packages; [
    setuptools
    leanclient
    mcp
  ];
  dontCheckRuntimeDeps = true;
  format = "pyproject";
  meta = with pkgs.lib; {
    description = "Lean Theorem Prover MCP (Multi-Client Protocol)";
    homepage = "https://github.com/oOo0oOo/lean-lsp-mcp";
    license = licenses.mit;
    maintainers = with maintainers; [ ];
    platforms = platforms.linux;
  };
}
