#!/usr/bin/env python3
"""Thin CLI over the arxiv-mcp-server (blazickjp/arxiv-mcp-server) via MCP stdio.

Usage:
  uv run --with mcp python scripts/arxiv_tool.py list
  uv run --with mcp python scripts/arxiv_tool.py search_papers '{"query":"assume-guarantee contract decomposition","max_results":10}'
  uv run --with mcp python scripts/arxiv_tool.py get_abstract '{"paper_id":"2103.13743"}'
  uv run --with mcp python scripts/arxiv_tool.py download_paper '{"paper_id":"2103.13743"}'
  uv run --with mcp python scripts/arxiv_tool.py read_paper '{"paper_id":"2103.13743","max_chars":20000}'
  uv run --with mcp python scripts/arxiv_tool.py export_citations '{"paper_ids":["2103.13743"]}'
Papers are stored under lit/papers/.
"""
import asyncio, json, sys, os
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STORE = os.path.join(ROOT, "lit", "papers")

async def main(tool, args):
    params = StdioServerParameters(command="uvx", args=["arxiv-mcp-server", "--storage-path", STORE])
    async with stdio_client(params) as (r, w):
        async with ClientSession(r, w) as s:
            await s.initialize()
            if tool == "list":
                tools = await s.list_tools()
                for t in tools.tools:
                    print(f"## {t.name}\n{t.description}\n{json.dumps((getattr(t,'input_schema',None) or getattr(t,'inputSchema',{})).get('properties', {}), indent=1)}\n")
                return
            res = await s.call_tool(tool, args)
            for c in res.content:
                print(getattr(c, "text", c))

if __name__ == "__main__":
    tool = sys.argv[1]
    args = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
    asyncio.run(main(tool, args))
