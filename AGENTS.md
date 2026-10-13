# Agents working in this repository

1. Read `CONTRIBUTING.md` in full. It is the contract; §5.4 (interfaces), §8 (designing a stage),
   §10 (memory) and §11 (agent rules) are not optional.
2. Read the current brief (`docs/PORT_MATRIX.md` while the Matrix layer is being built) and the
   current stage's design note in `docs/design/`. If the note does not exist, the stage has not
   been designed: the orchestrator writes it and stops for approval before any proof is written.
3. Read `docs/port/status.md` to see what is in progress and where the last agent stopped.
4. Work is sequential: one stage, one file at a time. Do the one file you own. Search Mathlib,
   then `NLAlib/`, then the prototype files the design note names, before proving anything.
5. Build with `lake build -j 2 <your module>` and `lake env lean -M 8000 <file>`, output to a log
   file. Never a bare `lake build`. Never two builds at once.
6. Before stopping: update `docs/port/ledger.json` and `docs/port/status.md`, run the §9 checks,
   and leave the read-back for the PR. Do not commit or push unless asked.
7. If you orchestrate: you write the design notes, skeletons and file reviews yourself; you send
   each design note, each interface question you cannot settle, and each stage report to a
   `model: "fable"` agent for a bounded review before acting on it; you delegate every proof to a
   `model: "opus"` agent, one file at a time; you delegate mechanical passes to `model: "sonnet"`
   or `model: "haiku"`. Every `Agent` call passes `model` explicitly; there is no default (brief,
   "Models and delegation").
