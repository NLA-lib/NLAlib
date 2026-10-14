# Agents working in this repository

1. Read `CONTRIBUTING.md` in full. It is the contract; §5.4 (interfaces), §8 (designing a stage),
   §10 (memory) and §11 (agent rules) are not optional.
2. Read the current brief (`docs/PORT_MATRIX.md` for the Matrix layer, finished;
   `docs/PORT_PROBABILITY.md` for the Probability round) and the
   current stage's design note in `docs/design/`. If the note does not exist, the stage has not
   been designed: the orchestrator writes it and stops for approval before any proof is written.
3. Read `docs/port/status.md` to see what is in progress and where the last agent stopped.
4. Work is sequential: one stage, one file at a time. Do the one file you own. Search Mathlib,
   then `NLAlib/`, then the prototype files the design note names, before proving anything.
5. Build with `LEAN_NUM_THREADS=2 lake build <your module>` and `lake lean <file> -- -M 8000`, output to a log
   file. Never a bare `lake build`. Never two builds at once.
6. Before stopping: update `docs/port/ledger.json` and `docs/port/status.md`, run the §9 checks,
   and leave the read-back for the PR. Do not commit or push unless asked.
7. If you orchestrate: keep your own context small (maintainer, 2026-10-14; `docs/port/status.md`
   standing instructions): you make the decisions, write the agent briefs, read reports and commit;
   design notes and skeletons are drafted by Opus agents from your brief; you send
   each design note, each interface question you cannot settle, and each stage report to a
   `model: "fable"` agent for a bounded review before acting on it; you delegate every proof to a
   `model: "opus"` agent, one file at a time; you delegate mechanical passes to `model: "sonnet"`
   or `model: "haiku"`. Every `Agent` call passes `model` explicitly; there is no default (brief,
   "Models and delegation").
