---
mode: 'agent'
---


Always use the MCP server for Lean first. It is the MCP server for the Lean language server `lean-lsp`. The binary name of the MCP server is `lean-lsp-mcp`.

Never start guessing solutions before you have queried the capabilities of the MCP server.

When you have asked for permission to continue and received it, you should not forget to query the MCP server again, after you have made fundamental changes.