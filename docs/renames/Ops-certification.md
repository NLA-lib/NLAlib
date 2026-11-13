# Canonical Ops certification

The canonical API now fixes the tree before runtime data and enforces complete accounting.

| Previous conditional interface | Explicit construction interface | Canonical interface |
| --- | --- | --- |
| `Ops.run` on a statement and environment | `Ops.eval` | `Ops.run` on a fixed `Program` |
| `Ops.exec` on statement state | `Ops.evalCounted` | `Ops.exec` on a fixed `Program`, mandatory structural counts |
| `Ops.Runs`, `Ops.RunsW`, `Ops.RunsL` | `Ops.ConditionalRuns`, `Ops.ConditionalRunsW`, `Ops.ConditionalRunsL` | `Ops.Runs p model specification` |
| `Ops.Impl.Meets R I mode contract` | `Ops.Impl.Triple` | `Ops.Impl.Meets R ins outs model specification` |
| `Ops.Profile.Certifies` | `Ops.Profile.Refines` | `Ops.Algorithm.link` checks the complete lower program |
| `Ops.staticCost`, `Ops.staticPeak` on statements | `Ops.stmtCost`, `Ops.stmtPeak` | `Ops.staticCost`, `Ops.staticPeak` on fixed programs |
| `Ops.RunsLaw` | `Ops.ConditionalRunsLaw` | `Ops.Algorithm.runsLaw` observes the certified output |

No compatibility aliases expose the earlier judgments under the canonical names.

## Format-aware resource follow-up

| Previous interface | Current interface |
| --- | --- |
| `Stmt.alloc` constructor | `Stmt.allocAs format len body`; `Stmt.alloc` is an abstract width1 helper |
| Allocation/release dimensions `[length]` | `[format.bytes, elementCount]` |
| Workspace expressed in scalar cells | Canonical `ResourceModel.workspace` and `queryWorkspace` use modeled payload bytes; rescale old cell workspace explicitly |
| `exec p I W tape d mem` | `exec p I resources formats tape d mem`, mandatory format/initial-arity guards |
| `run` / `Program.run` without layout | Both require resource model and initial format layout |
| `Problem` without storage declaration | Required fixed `Problem.formats`; `initialBytes` measures all supplied capacities |
| `AccessModel.workspace` field | Required `AccessModel.resources`; `workspace` remains the method projection |
| Count and scratch-only specification | Required count, scratch, work, span, resident-memory budgets and postcondition |
| `Algorithm.ofWp` without format/weighted proofs | Requires wellTyped, count, byte, full-work, full-span and initial-plus-scratch proofs |
| Fixed link with resource pushforward only | `Algorithm.link` rechecks full lower type/resource bounds |

Storage format checking does not establish finite encodability of opaque K or physical timing.
The abstract `.cell` helper is not silently mapped to a floating-point representation.
Span describes sequential composition of configured primitive critical paths, not work/P.
