# Can the proposer/verifier/coordinator loop be built with Strands (and Strands Labs)?

Feasibility note, 2026-10-19. Sources are official docs, GitHub and PyPI only. I read the Python SDK docs and source at
tag `python/v1.61.1` (commit `5cb8805`, 2026-10-15) of `github.com/strands-agents/harness-sdk`, and
`strands-labs/ai-functions` at commit `145efc8` (2026-10-09). Nothing was installed into `.venv`. I made **no model
calls**, so every statement about runtime behaviour against the Anthropic API is **unverified** unless it is marked
as tested. The only things I ran were Z3 one-liners in `.venv`.

## 0. Verdict

**It fits, but Strands adds little to the core loop.** The coordinator and the verifier are deterministic Python, and
the author's reproducibility rule requires them to be. The only LLM component is the proposer. Strands is useful for
the proposer: one `Agent` per component with `AnthropicModel`, `structured_output_model=Contract`, hooks that log
every model and tool call, and an optional `@tool` that lets a proposer run its local checks itself. A Strands
`Graph` *can* express the loop, because cycles and conditional edges are supported. For this problem it adds
boilerplate and turns structured data into text, without adding control. **Recommendation:** use a plain-Python
coordinator over Strands proposer agents, as in Section 5. A plain Anthropic-SDK loop is about as short (Section 6).
**Known blocker-class issue:** on `claude-opus-5-5` and `claude-sonnet-5-5`, two Strands code paths force
`tool_choice` and are expected to return HTTP 400 (Section 7).

## 1. Strands Agents SDK: package, provider, structured output, tools, state

| Item | Finding | Source |
|---|---|---|
| Package / version | `strands-agents` **1.61.1**, uploaded 2026-10-15; previous releases 1.61.0 (10-14), 1.60.0 (10-12), 1.59.0 (10-08), so about one minor release per week | https://pypi.org/pypi/strands-agents/json |
| Python | `>=3.10`. The project `.venv` is 3.12.13, so it is compatible | same |
| License | Apache-2.0 | same; https://github.com/strands-agents/harness-sdk |
| Repo | Monorepo `strands-agents/harness-sdk`; the Python SDK is in `strands-py/` (PyPI "Homepage") | https://github.com/strands-agents/harness-sdk |
| Install | `pip install 'strands-agents[anthropic]==1.61.1'` (extra pulls `anthropic>=0.21,<1.0`) | https://strandsagents.com/docs/user-guide/sdk/model-providers/anthropic/ |
| Core deps | Always installed: `boto3`, `botocore`, `mcp`, `opentelemetry-api/sdk`, `pydantic>=2.4`, `pyyaml`, `watchdog`, `jsonschema`, `httpx`. A dry `uv pip compile` with `z3-solver==5.3.1.0, numpy, scipy` resolves (55 pkgs, `anthropic==0.125.0`) | PyPI JSON `requires_dist`; tested locally (compile only) |

**Anthropic API directly: yes.** `strands.models.anthropic.AnthropicModel(client_args={...}, model_id=..., max_tokens=..., params={...})`
wraps `anthropic.AsyncAnthropic(**client_args)` (source `strands-py/src/strands/models/anthropic.py`, line 150). If
`client_args` has no `api_key`, the Anthropic SDK falls back to `ANTHROPIC_API_KEY`. That fallback is Anthropic-SDK
behaviour, not something Strands documents. `params` is spread into the request body, so
`params={"output_config": {"effort": "high"}}` is passed through (source lines 509 and 534). `claude-opus-5-5` and
`claude-sonnet-5-5` are listed in Strands' context-window table (`models/_defaults.py`, lines 45 and 49), and any
model id string is passed through. Docs: https://strandsagents.com/docs/user-guide/sdk/model-providers/anthropic/.
**Pitfall:** `Agent()` with no model, or with a *string* model, silently uses `BedrockModel` (`agent/agent.py`,
lines 365-368). Always pass an `AnthropicModel` instance.

**Structured output (Pydantic): yes.** Call `result = agent(prompt, structured_output_model=Contract)` and read
`result.structured_output`. The schema becomes a tool, and Pydantic validation errors (including `field_validator`
errors) go back to the model for a retry. A `StructuredOutputException` is raised on failure. The older
`agent.structured_output(...)` is deprecated.
https://strandsagents.com/docs/user-guide/sdk/agents/structured-output/

**Tools.** `@tool` builds the spec from the type hints and the docstring's `Args:` section. The decorated function is
still an ordinary callable (`DecoratedFunctionTool.__call__`). A return value that is a `str` becomes text, a `dict`
in `{"status","content":[{"json":...}]}` form is used as is, a Pydantic model is `model_dump_json()`'d, and an
exception becomes an error result. https://strandsagents.com/docs/user-guide/sdk/tools/custom-tools/,
https://strandsagents.com/docs/user-guide/sdk/tools/tool-results/; source `tools/decorator.py`, lines 687-715. Tools
can also be called directly as `agent.tool.verify(contract=...)`.
https://strandsagents.com/docs/user-guide/sdk/tools/using-tools/. `@tool(context=True)` gives access to
`tool_context.invocation_state`. A tool is exactly as deterministic as its Python body, so a Z3 tool with a fixed
`random_seed` is deterministic for a fixed Z3 version.

**Hooks, for logging.** The events are `BeforeInvocationEvent`, `AfterInvocationEvent`, `MessageAddedEvent`,
`BeforeModelCallEvent`, `AfterModelCallEvent` (`.stop_response.message`, `.stop_reason`, `.exception`, `.retry`),
`BeforeToolCallEvent`, and `AfterToolCallEvent` (`.tool_use`, `.result`, `.duration`, `.retry`). For multi-agent
runs there are also `BeforeNodeCallEvent` and `AfterNodeCallEvent`. Register them with
`agent.add_hook(cb, EventType)` or with a `Plugin`. https://strandsagents.com/docs/user-guide/sdk/agents/hooks/,
https://strandsagents.com/docs/user-guide/sdk/agents/hooks-events/; source `hooks/events.py`, lines 261 and 348.

**State, sessions and conversation.** These are `agent.messages`, the key-value `agent.state`, and per-call
`invocation_state` (https://strandsagents.com/docs/user-guide/sdk/agents/state/). For sessions,
`SnapshotSessionManager` is now recommended, and `FileSessionManager`/`S3SessionManager` remain supported
(https://strandsagents.com/docs/user-guide/sdk/agents/session-management/). Snapshots are plain JSON
(https://strandsagents.com/docs/user-guide/sdk/agents/snapshots/). The conversation managers are
`NullConversationManager`, `SlidingWindowConversationManager` (the default) and `SummarizingConversationManager`
(https://strandsagents.com/docs/user-guide/sdk/agents/conversation-management/). The default retry strategy retries
model calls up to 6 times (`agent/agent.py`, line 327), and `retry_strategy=None` disables it
(https://strandsagents.com/docs/user-guide/sdk/agents/retry-strategies/).

## 2. Multi-agent patterns

Overview and comparison table: https://strandsagents.com/docs/user-guide/sdk/multi-agent/multi-agent-patterns/

* **Graph** (https://strandsagents.com/docs/user-guide/sdk/multi-agent/graph/,
  https://strandsagents.com/docs/user-guide/sdk/multi-agent/graph-components/). **Cycles are allowed** ("Graphs
  support both acyclic (DAG) and cyclic topologies, so you can build feedback loops"). The API:
  `b = GraphBuilder(); b.add_node(executor, "id")`, where the executor is an `Agent`/`AgentBase` or a
  `MultiAgentBase`, then `b.add_edge("a","b", condition=fn)`.
  * An edge condition is a Python predicate `fn(state: GraphState) -> bool`. It can also be
    `fn(state, *, invocation_state, **kw)`. It reads `state.results["node"].result`.
  * Loop bounds are `b.set_max_node_executions(n)` (a total over all nodes), `set_execution_timeout(s)`,
    `set_node_timeout(s)` and `reset_on_revisit(True)`. Leaving both bounds unset logs a warning that "execution is
    unbounded" (`graph.py`, line 498).
  * You must call `set_entry_point` explicitly when a loop gives every node an incoming edge.
  * Data flow is **text**: a node receives the original task plus the outputs of its completed dependencies. Shared
    non-prompt data goes through the `invocation_state` dict.
  * The Python SDK uses **OR semantics** for multiple incoming edges, so AND joins need a condition helper. It also
    runs nodes in batches.
  * A deterministic node such as the verifier must be written as a `MultiAgentBase` subclass (the docs'
    `FunctionNode` example). The Python SDK ships no ready-made function node.
* **Swarm** (https://strandsagents.com/docs/user-guide/sdk/multi-agent/swarm/). The LLM decides the handoffs. Its
  limits are `max_handoffs`, `max_iterations`, `execution_timeout` and repetitive-handoff detection. It is the wrong
  fit here: routing counterexamples must be deterministic.
* **Workflow** (https://strandsagents.com/docs/user-guide/sdk/multi-agent/workflow/). It is "a pattern you implement
  in code by chaining agents together", and the comparison table says it allows **no cycles**.
* **Agents-as-tools** (https://strandsagents.com/docs/user-guide/sdk/multi-agent/agents-as-tools/). An LLM
  orchestrator calls sub-agents as tools, so an LLM would be the coordinator. That breaks determinism, so it is not
  recommended.
* **GoalLoop plugin** (https://strandsagents.com/docs/user-guide/sdk/plugins/goal-loop/). It re-invokes one agent
  until a validator passes. The validator can be a plain Python function returning `{"passed", "feedback"}`, and
  `max_attempts` bounds the loop. It suits a *per-proposer* local check (ports, receptiveness, causality). It does
  not suit the global (V1)/(V2) check, which needs every proposal.

**Match.** Only the Graph has a deterministic loop. A Graph version would have one `Agent` node per proposer, a
`FunctionNode` verifier with an edge from every proposer and an AND-condition, and conditional back-edges from the
verifier to proposer *i*. Each back-edge would test "verdict failed and a failure names *i*". The verdict and the
counterexamples would live in `invocation_state`, because node outputs are text. The bound would come from
`set_max_node_executions`, and the stop from "verdict passed" making no back-edge true. This works on paper
(**untested**), but every routing decision is still a Python predicate. The Graph only wraps a `for` loop in
batch-scheduling semantics, and that makes the log harder to read.

## 3. Strands Labs

Labs is "the experimental arm of Strands Agents". Its projects "move faster ... expect more frequent changes", and
the page gives no stability guarantee (https://strandsagents.com/docs/labs/). The org is
https://github.com/strands-labs. The projects listed on 2026-10-19 are:

| Project | What | Link |
|---|---|---|
| Robots | NL control/simulation of robots (MuJoCo or hardware) | https://github.com/strands-labs/robots |
| Strands for Cosmos | NVIDIA Cosmos video/physics reasoning | https://github.com/strands-labs/strands-for-cosmos |
| Benchmark Harnesses | agents for SWE-Bench / Terminal Bench | https://github.com/strands-labs/benchmark-harnesses |
| Harness Optimizer | tunes harness "Formulas" from rollouts | https://github.com/strands-labs/harness-optimizer |
| **AI Functions** | Python functions evaluated by agents, with runtime post-conditions | https://github.com/strands-labs/ai-functions |
| PyWebRTC Audio | WebRTC audio bindings | https://github.com/strands-labs/pywebrtc-audio |
| Strands Decider | small fast decision model | https://github.com/strands-labs/strands-decider |
| robots-sim | archived | https://github.com/strands-labs (org listing) |

**AI Functions** (`pip install strands-ai-functions`; 0.5.0 uploaded 2026-09-25; Python `>=3.12`; Apache-2.0; depends
on `strands-agents>=1.24.0` and `smolagents`, `textual`, `cloudpickle`, ...; https://pypi.org/pypi/strands-ai-functions/json).
`@ai_function` turns a typed signature plus a docstring template into an agent call that returns a validated
Pydantic instance. `post_conditions=[...]` are plain Python functions (an `assert` or a `PostConditionResult`). On
failure the model is re-prompted with the errors, up to `max_attempts` times (default 10). A post-condition "can
consume one of the original input arguments by naming it in their signature"
(https://github.com/strands-labs/ai-functions/blob/main/docs/tutorial.md). The default model is **Bedrock**, and you
pass `model=AnthropicModel(...)` to change it (README).

**Usefulness here.** AI Functions fits a `propose_contract(component, ports, query, counterexamples) -> Contract`
whose post-condition is the *local* verifier, which checks ports, syntax, (R) and (K). It is the same idea as
GoalLoop, but typed. It does not replace the coordinator, because (V1)/(V2) are global. It adds a heavy dependency
tree for one decorator, and it is Labs-grade (0.x, no stability statement). `ai_functions.experimental.verified`
(Lean proofs) and `experimental.economics` (cost-aware routing) are interesting but not needed. Verified uses Lean,
not Z3.

**Evaluation and reproducibility.** Nothing in Labs targets replay. The core `strands-agents-evals` 1.6.0
(https://pypi.org/pypi/strands-agents-evals/json) has *deterministic evaluators* (`Equals`, `Contains`, tool-call
checks, state comparison; https://strandsagents.com/docs/user-guide/evals-sdk/evaluators/deterministic_evaluators/).
Its LLM-judge evaluators default to Bedrock (https://strandsagents.com/docs/user-guide/evals-sdk/quickstart/). The
project's own replay script is simpler than any of this.

## 4. Observability and reproducibility

* **OpenTelemetry.** Install `strands-agents[otel]`, then `StrandsTelemetry().setup_otlp_exporter()` or
  `.setup_console_exporter(**kw)`, which forwards its arguments to OTel's `ConsoleSpanExporter`
  (https://strandsagents.com/docs/user-guide/sdk/observability-evaluation/traces/; source `telemetry/config.py`,
  line 130). OTel's `ConsoleSpanExporter(out=<file>)` therefore writes spans to a file (OTel API; **unverified** with
  Strands). The spans carry `gen_ai.request.model`, the messages, `gen_ai.tool.name`, the tool results and token
  usage.
* **Simpler.** One `AfterModelCallEvent` hook and one `AfterToolCallEvent` hook append JSON lines to the run log
  (Section 5). Every model call, including structured-output retries and SDK retries, passes through
  `AfterModelCallEvent`.
* **Temperature and seed.** On `claude-opus-5-5`, "Omit `temperature`, `top_p`, and `top_k`, or leave them at their
  defaults: any other value is rejected" (https://platform.claude.com/docs/en/models/opus-5-5/migration-guide). The
  Anthropic Messages API has no seed parameter. Live runs are therefore **not reproducible**, by design of the
  provider. The Strands Anthropic page's example `params={"temperature": 0.7}` would be rejected on these models.
* **Replay without a model: possible.** A proposal is a Pydantic object whose formulas are SMT-LIB2 strings, so it is
  plain JSON. Replay parses the log, rebuilds the Z3 terms, and re-runs `verify`. I tested that
  `z3.parse_smt2_string(src, decls=own_ports)` rejects any symbol that is not one of the component's ports
  ("unknown constant d_0"), so the port check comes for free. Pin `z3-solver==5.3.1.0`.
* **What replay should check.** Replay should compare *verdicts*. For a logged counterexample it should check that
  it really violates the formula. It should not check that the counterexample is identical, because which model Z3
  returns can change across versions (the README already notes that Z3's printed output is version-dependent). Set
  `random_seed` (tested: `Solver().set('random_seed', 0)` is accepted).

## 5. Minimal skeleton (98 lines; Strands part UNTESTED; strands-agents[anthropic]==1.61.1, z3-solver==5.3.1.0, Python 3.12)

Relay instance, H = 0. The causality check (K) for H > 0 is left as a call into the existing procedure.

**What was tested.** The file passes `py_compile`. I ran `verify()` in a throwaway `uv run --with pydantic --with
z3-solver==5.3.1.0` environment, not `.venv`, on four relay delegations:

* $D$ (`m=r`, `d=m`): passes.
* `d=0`: fails (V1), with counterexamples projected to each component (Radio `r_0=1, m_0=1`; Display `m_0=1, d_0=0`).
* Radio mentioning `d_0`: fails the port check.
* Display also constraining its input (`m_0=0`): fails (R).

The Strands `run()` path was not executed, because that requires installing Strands and calling the API.

```python
# UNTESTED sketch. Live: python loop.py run run.jsonl   Replay (no model calls): python loop.py replay run.jsonl
import json, sys, time
from pydantic import BaseModel, Field
from z3 import (Real, BoolVal, And, Or, Not, ForAll, Exists, Solver, sat, unsat,
                parse_smt2_string, Z3Exception)

COMPS = {"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}      # name -> (inputs, outputs)
H = 0
AP = "(assert (<= r_0 1.0)) (assert (<= (- r_0) 1.0))"
GP = "(assert (<= (- d_0 r_0) 0.5)) (assert (<= (- r_0 d_0) 0.5))"

def syms(vs): return {f"{v}_{t}": Real(f"{v}_{t}") for v in vs for t in range(H + 1)}
ALL = syms({v for i, o in COMPS.values() for v in i + o})
def parse(src, decls):
    return And(*parse_smt2_string(src, decls=decls)) if src.strip() else BoolVal(True)

class Contract(BaseModel):
    """Local contract of one component: SMT-LIB2 (assert ...) lines over its own timed ports v_t only."""
    assumption: str = Field(description="SMT-LIB2 asserts over own ports; empty string means true")
    guarantee: str = Field(description="SMT-LIB2 asserts over own ports; verifier forms S = not A or G")

def project(m, c):
    keep = syms(COMPS[c][0] + COMPS[c][1])
    return {k: str(m.eval(z, model_completion=True)) for k, z in keep.items()}

def witness(phi):
    s = Solver(); s.set("random_seed", 0); s.add(phi)
    return s.model() if s.check() == sat else None

def verify(props: dict) -> dict:
    """Deterministic. Checks ports/syntax, (V1), (V2), (R); returns failures with projected counterexamples."""
    fails, A, S = [], {}, {}
    for c, k in props.items():
        d = syms(COMPS[c][0] + COMPS[c][1])
        try:
            A[c], G = parse(k.assumption, d), parse(k.guarantee, d)
        except Z3Exception as e:
            fails.append({"check": "ports/syntax", "component": c, "msg": str(e)}); continue
        S[c] = Or(Not(A[c]), G)
    if fails: return {"ok": False, "failures": fails}
    ap, gp = parse(AP, ALL), parse(GP, ALL)
    if (m := witness(And(ap, *S.values(), Not(gp)))) is not None:                    # (V1)
        fails += [{"check": "V1", "component": c, "cex": project(m, c)} for c in COMPS]
    for j in COMPS:                                                                  # (V2)
        if (m := witness(And(ap, *S.values(), Not(A[j])))) is not None:
            fails.append({"check": "V2", "component": j, "cex": project(m, j)})
    for c, (ins, outs) in COMPS.items():                                             # (R)
        i, o = list(syms(ins).values()), list(syms(outs).values())
        s = Solver(); s.add(Not(ForAll(i, Exists(o, S[c]))))
        if s.check() != unsat: fails.append({"check": "R", "component": c})
    # (K) for H > 0: call the existing check from scripts/delegate.py here.
    return {"ok": not fails, "failures": fails}

def run(path, budget=8):
    from strands import Agent
    from strands.models.anthropic import AnthropicModel
    from strands.agent.conversation_manager import NullConversationManager
    from strands.hooks import AfterModelCallEvent
    log = open(path, "a")
    def put(kind, **kw): log.write(json.dumps({"t": time.time(), "kind": kind, **kw}, default=str) + "\n"); log.flush()
    model = AnthropicModel(model_id="claude-opus-5-5", max_tokens=16000,          # ANTHROPIC_API_KEY from env
                           params={"output_config": {"effort": "high"}})          # no temperature: 400 on 5.5
    agents = {}
    for c, (ins, outs) in COMPS.items():
        a = Agent(name=c, model=model, callback_handler=None, retry_strategy=None,
                  conversation_manager=NullConversationManager(),                 # append-only history
                  system_prompt=(f"You propose a local assume-guarantee contract for component {c}. "
                                 f"Inputs {ins}, outputs {outs}, H={H}. Use only symbols {sorted(syms(ins+outs))}. "
                                 "Write SMT-LIB2 asserts over linear real arithmetic. For every input history some "
                                 "output must satisfy the guarantee, computed from inputs at times <= t."))
        a.add_hook(lambda e, c=c: put("model", agent=c, exc=repr(e.exception) if e.exception else None,
                   stop=e.stop_response.stop_reason if e.stop_response else None,
                   message=e.stop_response.message if e.stop_response else None), AfterModelCallEvent)
        agents[c] = a
    feedback = {c: [] for c in COMPS}
    for rnd in range(budget):
        props = {}
        for c, a in agents.items():
            msg = json.dumps({"round": rnd, "query": {"A_P": AP, "G_P": GP}, "counterexamples": feedback[c]})
            props[c] = a(msg, structured_output_model=Contract).structured_output
            put("proposal", round=rnd, component=c, contract=props[c].model_dump())
        v = verify(props); put("verdict", round=rnd, **v)
        if v["ok"]: return 0
        feedback = {c: [f for f in v["failures"] if f["component"] == c] for c in COMPS}
    return 1

def replay(path):
    rounds, bad = {}, 0
    for line in open(path):
        e = json.loads(line)
        if e["kind"] == "proposal": rounds.setdefault(e["round"], {})[e["component"]] = Contract(**e["contract"])
        if e["kind"] == "verdict":
            ok = verify(rounds[e["round"]])["ok"]; bad += ok != e["ok"]
            print(f"round {e['round']}: logged {e['ok']} recomputed {ok}")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(run(sys.argv[2]) if sys.argv[1] == "run" else replay(sys.argv[2]))
```

Notes:

* A V1 counterexample goes to every component, each seeing only its own ports. Routing it more finely (only to the
  components whose $S_i$ the counterexample uses) is a design choice for the coordinator.
* To give a proposer a self-check, wrap the local part of `verify` as a `@tool` taking a `Contract` and add it to
  `tools=[...]`. A `GoalLoop` or `@ai_function(post_conditions=...)` does the same job.
* The replay path imports no Strands code, so `replay` needs only `pydantic` and `z3`.

## 6. Alternative: plain Python plus the Anthropic SDK

It would be about as short. `client.messages.parse(...)` with a Pydantic model, which uses structured outputs (`output_config.format`) per the
Claude API skill notes, gives schema-constrained JSON without the forced-tool problem in Section 7. The exact
signature was not checked against `anthropic` 1.x. The
loop, the log and the replay stay identical. It also drops boto3, mcp and the OTel stack, and avoids an `anthropic<1.0`
pin: Strands 1.61.1 caps `anthropic<1.0.0`, while `anthropic` is at 1.15.0 on PyPI
(https://pypi.org/pypi/anthropic/json).

Strands would add:

* the provider switch: one line changes the model to Bedrock, OpenAI or Ollama;
* hooks and OTel spans without writing them yourself;
* session snapshots;
* Pydantic-validator retries;
* the Graph/Swarm vocabulary, if the author wants to say "built on Strands".

For a research artefact whose correctness rests on Z3, those additions are small. **Honest recommendation:** if the
author wants Strands, use it only for the proposer agents, with the coordinator in plain Python as in Section 5. If
not, the plain SDK loop is simpler and has fewer moving parts.

## 7. Risks

1. **Forced `tool_choice` on the 5.5 models (likely blocker in edge cases, unverified at runtime).** Claude Opus 5.5
   rejects `tool_choice` `any`/`tool` with a 400 (https://platform.claude.com/docs/en/models/opus-5-5/migration-guide),
   and the Claude API skill's model notes say the same of Sonnet 5.5. Strands uses forced tool choice in two places:
   * The deprecated `agent.structured_output()`, which is the form the Anthropic provider page still shows, always
     sends `{"any": {}}` (`models/anthropic.py`, line 1049).
   * `structured_output_model=` first runs with `auto`. Only when the model ends its turn without calling the schema
     tool does it retry with a forced `{"tool": ...}` (`event_loop/event_loop.py`, lines 368-376).

   So use `structured_output_model=`, catch `StructuredOutputException` and the API error, and log the failure as a
   failed proposal. AI Functions goes through the same Strands path. A cheap fix is to replace the structured output
   with a `submit_contract(contract: Contract)` tool and stop when it is called. Check the forced-tool behaviour
   against the live API before relying on it.
2. **API churn.** Strands releases about weekly (12 releases between 2026-09-08 and 2026-10-15). The docs moved
   (README links to `/docs/user-guide/concepts/...`, while the live pages are `/docs/user-guide/sdk/...`). Labs
   projects carry no stability promise. Semver applies to the core, except `strands.experimental` and the
   OTel/MCP/A2A integrations (https://strandsagents.com/docs/user-guide/sdk/versioning-and-support/). **Pin exactly:**
   `strands-agents[anthropic]==1.61.1`, `anthropic==0.125.0`, `z3-solver==5.3.1.0`, and lock with `uv pip compile`.
3. **Nondeterminism.** Temperature, top_p and top_k cannot be set and there is no seed, so a live run is a sample.
   Report results per run, with N runs, never as "the" result. The reproducible object is the log, not the run.
4. **Hidden model calls.** Structured-output retries, the SDK retry strategy (6 attempts by default) and any
   GoalLoop/AI-Functions retries all multiply calls. Log at `AfterModelCallEvent`, not at the proposal level, so that
   cost and counts are honest.
5. **Cost (estimate only).** Opus 5.5 costs $4 per million input tokens and $20 per million output tokens; Sonnet 5.5
   costs $2 and $10 (Claude API skill model table, cached 2026-10-06). Assume about 3k input and 5k output tokens per
   proposer call (thinking included). That is roughly $0.11 per Opus call and $0.06 per Sonnet call. The relay with 2
   components and 8 rounds is at most 16 calls, so under about $2 per run on Opus. The architectures in
   `docs/complete.tex` would scale linearly with the number of components and rounds.
6. **Bedrock credentials.** None are needed if an `AnthropicModel` is passed to every agent. `boto3` is still
   installed as a core dependency. Bedrock is the silent default in five places: `Agent()` without a model,
   `Agent(model="<string>")`, `aux_model` (it defaults to the main model, which is fine once that is Anthropic),
   AI Functions' default model, and the Evals LLM judges.
7. **Preserved thinking.** Opus 5.5 always thinks, and edited histories can be rejected on newer accounts (migration
   guide). Strands round-trips `thinking` blocks with their signature (`models/anthropic.py`, lines 232-237). Its
   default `SlidingWindowConversationManager` can trim history, so use `NullConversationManager` or a fresh agent per
   call. Not tested.
