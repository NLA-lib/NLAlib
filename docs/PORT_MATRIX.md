# Port brief: the Matrix layer

For the orchestrating agent building `NLAlib/Matrix/` in this repository. Read `CONTRIBUTING.md`
first and in full; it is the contract every file must meet, and §5.4 (interfaces), §8 (designing
a stage) and §11 (agent rules) are the parts this brief relies on.

## 0. What this is and is not

- **The goal** is a Matrix layer that makes proving new results in numerical linear algebra easy:
  the right objects, a small set of hypothesis interfaces that everything downstream takes, and
  headline statements in the form a new proof wants, each cited where it appears in print. It is
  not a reproduction of any textbook's chapter structure, and not a reproduction of the prototype.
- **The prototype** (`~/Documents/prove2me/lean/NLAlib/Matrix/`, about 450 files and 60k lines,
  grown by agents in a week, plus `…/ForMathlib/`) is **material, not a template**. It tells you
  what mathematics has been formalised and gives proofs to port. Its organisation, file names,
  interfaces and many of its statement shapes are things it got wrong: generic definitions with
  real-only theorems, `Complex*` twin files, "Toolkit" files of conjunction bundles, `*_fin`
  transport lemmas, paper-named theorems, five different spellings of orthonormality and of
  conclusions. Read it with `atlas/declarations.json` (every declaration with signature and
  docstring) and its `docs/STANDARDS.md` §3 on the working tree, which holds the vocabulary
  decisions that survived its last consistency round:
  ```
  cd ~/Documents/prove2me/lean
  python3 -c "import json;[print(x['name'],'::',x['module'],'::',x['signature'].replace(chr(10),' ')[:160]) for x in json.load(open('atlas/declarations.json')) if 'eigenvalues₀' in x['signature']]"
  ```
- **This repository** is new. Skeleton: `lakefile.toml` (Mathlib tag `v4.33.1`, the prototype's
  exact pin, so proofs transfer), `lean-toolchain`, CI, `scripts/`, `docs/references.bib`.
  `NLAlib/` and `NLAlibScaffold/` are empty.
- **Not in scope:** probability and measurability (a Probability-stage decision), random matrices,
  sketching, Krylov, polynomials, finite precision (none yet, by decision), the atlas JSON, the
  website.

## 1. Process: sequential stages, design first

The layer is built in the stages of §3, **strictly one after another**. Each stage:

1. **Design note** `docs/design/Matrix-<Stage>.md`, per CONTRIBUTING §8: objects, interfaces,
   headline signatures written out in Lean, consumers, file split, what prototype material is used
   and what is deliberately not reproduced, open questions with recommendations. Writing it means
   reading the prototype files for the stage, searching Mathlib for every object and statement,
   and thinking about how the next stages and the later layers (perturbation theory, sketching,
   low-rank approximation) will consume what this stage defines. Budget real time here; it is
   where the library is decided.
2. **Design review, then stop for approval.** Send the note to a `model: "fable"` agent for
   review ("Models and delegation" below), fold its comments in or record why not, then stop for
   the maintainer's approval. Do not start proofs before approval.
3. **Skeleton.** The stage's files with every definition, docstring and statement in place and
   every proof `sorry`, compiling (`lake lean <file> -- -M 8000`). Review the skeleton against
   the note; statements are easier to fix before they have proofs.
4. **Proofs**, one file at a time in the note's order, by the procedure in §2. A second agent
   may prove a file the note marks as independent of the one in progress; otherwise one at a time.
5. **Review** of each file by an agent that did not write it, with the question "would a Mathlib
   reviewer accept this file, and will a downstream user reach for these statements?"; then the
   PR with read-back.
6. **Stage report** appended to the design note: what changed from the design and why, what went
   to `NLAlibScaffold`, and anything the next stage's design should know.

The orchestrator keeps `docs/port/status.md` (stage, file, owner, state, notes) and
`docs/port/ledger.json` (prototype declaration → new name, or `null` with a reason) current at
every stopping point.

### Models and delegation

- **The orchestrator does itself:** the design notes, the skeletons (statements and docstrings),
  the reviews, the stage reports, and the status and ledger files. These are the design-bearing
  tasks and they need the full context of the stage.
- **Delegated to `model: "opus"` agents:** every proof. One file per agent, one agent at a time
  (two only when the design note marks the files independent). The agent gets the design note,
  the skeleton file, the prototype files named for that file, and CONTRIBUTING; it returns the
  file with proofs, the ledger entries, and a note of anything that did not fit the design.
- **Delegated to `model: "fable"` agents:** short, high-judgement design tasks with a bounded
  input and a page of output. Three fixed points: (a) review of each design note before the
  orchestrator stops for approval, with the questions "are these the interfaces people will reach
  for in five years, does any of this duplicate an existing notion or Mathlib, will the headline
  signatures be usable downstream?"; (b) adjudication of an interface question the orchestrator
  cannot settle (give it the alternatives written out in Lean and the downstream consumers, ask
  for a decision with reasons); (c) review of the stage report for what the next stage's design
  should change. The agent receives the note or the question plus `CONTRIBUTING.md`, never the
  prototype tree, and returns comments, not code. Fable has tighter usage limits than Opus, so it
  is never given proofs, skeletons, or anything long-running; a Fable task that needs more than
  one exchange is split or sent to Opus.
- **Delegated to `model: "sonnet"` or `model: "haiku"` agents:** mechanical passes with a
  checkable result: running `mk_all`, header and reference-key checks, docstring formatting,
  grep-based audits of the prototype (listing every declaration in a directory with its signature),
  updating the ledger from a diff.
- **Every `Agent` call passes `model` explicitly.** An agent launched without it inherits whatever
  model the orchestrator's session runs on, which may have different usage limits; in the
  prototype's last round four agents launched that way were killed mid-work. There is no default.
- Agents that spawn agents follow the same rules and pass `model` the same way.

## 2. Porting one file

1. **Read the prototype files the design note lists** for this file, and only those. List every
   public declaration: statement, generic or not, bundle, twin, transport lemma, paper-named.
2. **Check Mathlib for each statement** (`grep` the pinned Mathlib, `exact?` in a scratch file).
   Anything Mathlib has is not ported; a prototype proof that used it through a local copy now
   cites Mathlib directly.
3. **Write the statements from the design note**, not from the prototype. The prototype's
   statement is one input; the note's signature is the target. Where they differ, the note wins;
   where the note is silent, apply CONTRIBUTING §5 and record the choice in `status.md`.
4. **Port proofs** one declaration at a time, from the prototype proof when it exists, rewritten
   against the new statement. Generic proofs: the prototype's real proof usually goes through with
   `conjTranspose` for `transpose` and `RCLike.re` where a real inner product was used; when it
   does not, the ℂ twin's proof often does. Choose a shorter argument through Mathlib whenever one
   exists; no proof is owed to any source. Keep proofs under 80 lines; extract named lemmas.
5. **Never port:** `*Toolkit` files and `*_properties`/`*_and_*` bundles (useful conjuncts become
   their own theorems), `Complex*`/`Real*` twins (the generic statement replaces both), `*_fin`,
   `*Transport` and `*Reindex` lemmas (unnecessary with generic statements), paper-named theorems
   under their old names, private helper copies of library lemmas, local predicates that duplicate
   a §5.4 interface.
6. **Budget.** A declaration whose proof does not port within about an hour of agent time goes
   to `NLAlibScaffold/` at the same path, with the full docstring and a `Proof:` line saying what
   the prototype proof does and where it broke. Move on.
7. **Ledger and status**, then the CONTRIBUTING §9 checks, then the PR.

## 3. Stages and the mathematics each must cover

Each stage lists the mathematics it is responsible for, the prototype directories that hold
material for it, and the **design questions the note must answer**. The file split is the note's
to decide. Stage boundaries may move if the note argues for it.

### Stage M0: bootstrap

```
cd ~/Documents/NLA-lib/nlalib
lake update && lake exe cache get
lake exe mk_all --module --lib NLAlib && lake exe mk_all --module --lib NLAlibScaffold
LEAN_NUM_THREADS=4 lake build NLAlib NLAlibScaffold
mkdir -p docs/design docs/port && echo '{}' > docs/port/ledger.json
```

Then one trivial file under `NLAlib/Matrix/` to verify the `module` header, `public import`,
`@[expose] public section`, the header linter and `scripts/Lint.lean` end to end. If `mk_all` is
not exposed by Mathlib's lakefile in this version, vendor Mathlib's `scripts/mk_all.lean` as a
`lean_exe`. Record what you learned in `docs/port/status.md`.

### Stage M1: foundations (orthonormality, projectors, quadratic forms, Gram, rank, Schur complement)

- Covers: orthonormal columns and its API; orthogonal projectors, range projector, the projection
  residual, column space as a submodule; quadratic forms and Rayleigh quotients; Gram matrices
  (`Aᴴ A`: PSD, rank, kernel, invertibility ⇔ full column rank); rank bounds, complementary
  nullities, Sylvester's rank inequality; Schur complements (classical and pseudoinverse-free
  block forms), block determinants and inverses; selection matrices, plane rotations, dilations,
  determinant updates, compound matrices and Cauchy–Binet.
- Material: prototype `Matrix/Basic/*`, `Matrix/Subspaces/{Projections,RangeProjector,OrthonormalBasisMatrix}`.
- Mathlib: `Submodule.starProjection`, `Matrix.toEuclideanLin`, `Matrix.PosSemidef`, `Matrix.rank`,
  `LinearAlgebra/Matrix/SchurComplement`, `Matrix.det_*`.
- Design questions: What is the orthonormality interface, and does one predicate serve isometries,
  partial isometries and unitaries, or do unitaries use Mathlib's `unitary`? Is the residual
  `A − Q(QᴴA)` the right primitive or is it the projector `1 − QQᴴ` applied, and which spelling will
  range finders and Krylov theorems take? Should `quadForm` be `𝕜`-valued with `re` taken by real
  consumers (Mathlib's PSD form) or ℝ-valued? Which rank facts does Mathlib already have?

### Stage M2: norms

- Covers: Frobenius inner product and norm; spectral norm; their relations, submultiplicativity,
  invariance under orthonormal factors, block and entry bounds, the quadratic-form bound,
  ε-net characterisation of the spectral norm; the Schatten family, nuclear and Ky Fan norms;
  unitarily invariant norms and symmetric gauge functions; Fan dominance.
- Material: prototype `Matrix/Norms/*`.
- Mathlib: `Matrix.frobeniusNormedAddCommGroup`, `Matrix.instL2OpNormedAddCommGroup` and
  `Matrix.l2_opNorm_*`, `LinearMap.singularValues` (Schatten norms need singular values; decide
  whether the Schatten part belongs here or after M3).
- Design questions: Named functions versus Mathlib's scoped norm instances is settled (named);
  but should there be a **unitarily-invariant-norm interface** (a structure or class over which
  Mirsky, Eckart–Young, Davis–Kahan and perturbation bounds are proved once, with Frobenius,
  spectral and Schatten as instances), and if so what is its carrier? How are mixed inequalities
  stated so that `gcongr`/`calc` chains work? Is `frobSq` a separate definition or `frobNorm ^ 2`
  with simp lemmas?

### Stage M3: spectral core

- Covers: the API on `IsHermitian.eigenvalues₀` (trace, determinant, extremes, Rayleigh forms);
  `λ_max`/`λ_min` as functions; Courant–Fischer as equations and as inequalities; Cauchy
  interlacing for compressions and principal submatrices; eigenvalue monotonicity in the Loewner
  order; singular values, the rectangular diagonal, `IsSVD`, existence; consequences for norms,
  rank, invariance, products; Weyl for eigenvalues and singular values, Lidskii, Mirsky,
  Hoffman–Wielandt (Hermitian); Eckart–Young–Mirsky; interlacing under low-rank updates and the
  converse construction; singular-value interlacing.
- Material: prototype `Matrix/Spectral/{Core,SVD,CourantFischer,Weyl,EckartYoung,Interlacing*,SingularValue*,...}`,
  `Matrix/Inequalities/{Mirsky,Lidskii}`, `Matrix/Perturbation/HoffmanWielandtNormal`.
- Mathlib: `Analysis/Matrix/Spectrum` (`eigenvalues₀`, `eigenvalues₀_antitone`,
  `spectral_theorem`), `Analysis/InnerProductSpace/SingularValues`, `Analysis/Matrix/Order`.
- Design questions: Eigenvalue indexing, `ℕ` with zero padding versus `Fin (card n)`, and the
  bridge between them, chosen once for eigenvalues and singular values together. The SVD interface:
  `IsSVD` with `Fin`-indexed factors (the prototype's decision E′) versus an `OrthonormalBasis`
  formulation versus singular vectors as a family; which one do Eckart–Young, Davis–Kahan, Wedin and
  the randomized-SVD bounds want to consume? What is the **spectral-gap interface** (`δ > 0` with
  `eigenvalues₀ k − eigenvalues₀ (k+1) ≥ δ`, or a set-separation form) that Davis–Kahan and
  subspace-iteration convergence will take? Which perturbation results generalise to any unitarily
  invariant norm (M2's decision)?

### Stage M4: pseudoinverse and least squares

- Covers: the Penrose identities and uniqueness; the Moore–Penrose inverse for every matrix,
  its projector identities, rank, transformations, Hermitian and PSD cases; the full-rank formulas
  and their bridges; least-squares solutions, normal equations, minimum-norm solution, residual
  orthogonality; condition numbers (`ℝ≥0∞`-valued, and the pseudoinverse ratio), distance to
  singularity.
- Material: prototype `Matrix/Basic/{PenroseIdentities,MoorePenrose*,Pseudoinverse,LeastSquares}`,
  `Matrix/Perturbation/{ConditionNumber,Conditioning,MapConditioning,DistanceToSingularity}`.
- Design questions: One pseudoinverse or two (general plus full-rank formulas with `IsUnit`
  hypotheses)? The prototype kept both; is the full-rank formula a definition or a lemma about the
  general one? Where does the condition number live and what is its type? What do sketching
  theorems (`(SA)⁺`) and Kaczmarz need from this stage?

### Stage M5: subspaces

- Covers: orthogonal projector theory beyond M1 (blocks, trace = rank, gaps `‖P − Q‖`);
  principal angles via singular values of `Qᴴ W`, subspace distances and tangents, invariance,
  bridges to projector gaps; the CS decomposition; oblique projections; orthonormal completion,
  basis change, Stiefel set, polar frame, Gram isometry (`Aᴴ A = Bᴴ B ↔ A = W B`).
- Material: prototype `Matrix/Subspaces/*`.
- Design questions: **The subspace-distance interface.** Davis–Kahan, Wedin, subspace iteration,
  range finders and sketching all talk about how far two subspaces are; the prototype has
  `tanThetaMax`, `subspaceTangent`, `directedSubspaceGap`, projector gaps and principal angles as
  separate notions. Decide one primary notion (a projector-norm distance? the largest principal
  angle?) with the others as derived API, and the hypotheses in which it will appear downstream.

### Stage M6: perturbation theory

- Covers: inverse perturbation (Neumann series, relative bounds via condition number), linear
  systems; eigenvalue perturbation (Bauer–Fike absolute and relative, variation for normal
  matrices); simple eigenvalues (persistence, differentiability, Rayleigh derivative); Davis–Kahan
  in projector and top-eigenspace forms; Wedin; pseudoinverse perturbation (Wedin, projector
  differences, acute perturbations); least-squares perturbation.
- Material: prototype `Matrix/Perturbation/*` (unbundle the `*Bounds` files; the `DavisKahan`
  statement with a proof term in a hypothesis is the example of what not to do).
- Design questions: Davis–Kahan in which norm(s), with which gap interface (M3) and which
  subspace-distance interface (M5)? Which results generalise to any unitarily invariant norm?
  Relative versus absolute perturbation forms: which does the low-rank layer need?

### Stage M7: inequalities

- Covers: majorization (weak and strong, Hardy–Littlewood–Pólya, Schur-convexity, doubly
  stochastic characterisation), Schur–Horn, Ky Fan maximum principle, von Neumann's trace
  inequality, singular-value majorization; determinant inequalities (Hadamard, Fischer,
  Minkowski, Szász, principal-minor products); Hadamard products (Schur product theorem, order and
  norm inequalities); block inequalities, Kantorovich, quadratic condition bounds, Hermitian parts.
- Material: prototype `Matrix/Inequalities/*`.
- Design questions: Majorization on `Fin n → ℝ` or on `ℕ → ℝ` with finite support, chosen to
  match M3's eigenvalue indexing. Is there a Mathlib majorization already? What does the Ky Fan
  principle look like as an interface consumed by trace-estimation and low-rank optimality proofs?

### Stage M8: matrix functions

- Covers: the `cfc` API for Hermitian matrices (eigenvalues of `cfc f A`, polynomial and unitary
  calculus, inverse), exponential and logarithm, trace of the exponential; operator monotonicity
  and convexity (Loewner–Heinz, operator Jensen, operator concavity of log, perspectives);
  trace inequalities (convexity and monotonicity of `tr exp`, Golden–Thompson, Lieb, Klein, Young,
  power bounds, log-det concavity, entropy); pinching, diagonal filters, dilation identities,
  intrinsic dimension.
- Material: prototype `Matrix/Functions/*`.
- Design questions: `matrixExp` as `NormedSpace.exp` or as `cfc Real.exp`, and whether the named
  aliases earn their place over `cfc`. Which trace inequalities does the matrix-concentration layer
  consume and in what form (Tropp's statements take `tr exp` of Hermitian sums)? Over `𝕜` or ℂ?

### Stage M9: factorizations and algorithms

- Covers: QR (predicate, existence, uniqueness, Gram–Schmidt, Householder, Givens), LU
  (predicate, elimination recursion, success ⇔ leading minors nonzero), Cholesky (predicate,
  recursion, success ⇔ positive definite, uniqueness), polar decomposition and Procrustes,
  Hessenberg form, rank-revealing QR and maximum-volume submatrices.
- Material: prototype `Matrix/Factorizations/*` (its Cholesky realisation theorem is unproved;
  prove or scaffold).
- Design questions: **The algorithm interface.** The prototype's convention (factorization
  predicate, total recursion over `Fin n`, success predicate, realisation theorem) is reasonable;
  decide whether to keep it, whether recursions should be over `[Field K]` so they are executable,
  and how Krylov processes (later layer) will follow the same pattern. Decide what "rank-revealing"
  means as an interface before porting strong RRQR.

### Stage M10: structured matrices and remaining spectral theory

- Covers: Kronecker products (identities, spectrum, singular values, norms, rank), circulants
  and the Fourier diagonalization, Walsh–Hadamard matrices, Cauchy determinants; Schur
  triangularization, normal matrices, simultaneous triangularization and diagonalization, real
  Schur form; inertia, Sylvester's law, congruence, Sylvester's criterion; Gershgorin and diagonal
  dominance; spectral radius and matrix powers; definite pencils and generalized eigenproblems.
- Material: prototype `Matrix/Structured/*`, `Matrix/Spectral/{Schur*,Normal*,Simultaneous*,RealSchur*,Inertia*,*Congruence,Sylvester*,PrincipalMinor*,Gershgorin*,*DiagonalDominance*,MatrixPower*,PowerBounded*,Generalized*,*Pencil*,*QZ,DefinitePair*}`,
  `ForMathlib/Analysis/{Schur*,Pencil*,Simultaneous*,Fourier*}`.
- Design questions: Which of this is needed by later layers at all (Kronecker and Walsh by
  sketching; spectral radius by Krylov; the rest is completeness)? Prioritise by consumer; what has
  none may be scaffolded as statements or left out of the first release.

## 4. Decisions already made

Settled unless a design note argues otherwise and the maintainer agrees:

- Scalars `[RCLike 𝕜]`, index types `[Fintype]`, `ᴴ` only, no transpose twins (CONTRIBUTING §5.1).
- Matrix norms are named functions; `‖A‖` does not appear in statements (§5.1).
- Orthonormality is one predicate taken as a hypothesis everywhere (§5.3).
- Eigenvalues of Hermitian matrices are Mathlib's `eigenvalues₀`; no separate `lamMin`/`sigmaMin`
  functions; extremes are the first and last index.
- Lemmas about Hermitian/PSD hypotheses live in `Matrix.IsHermitian` / `Matrix.PosSemidef`.
- Algorithms are exact-arithmetic; no finite precision.
- Constants: explicit, named when not the source's; tails before sample sizes (§5.2).
- Measurability of matrices is not a Matrix-layer concern; it is designed with Probability.

## 5. Sequencing and memory

- One stage at a time, one proving agent at a time unless the design note marks files independent;
  never more than two Lean-building processes on the machine (8 cores, 31 GB). Each uses
  `LEAN_NUM_THREADS=2 lake build <module>` and `lake lean <file> -- -M 8000` with output to a log file. A full
  `LEAN_NUM_THREADS=4 lake build NLAlib NLAlibScaffold` runs only with nothing else building.
- Opus for the orchestrator and every proof-bearing agent; Fable for the bounded design reviews
  and adjudications of §1; Sonnet or Haiku for ledger, status, `mk_all`, reference-key and header
  checks.
- `docs/port/status.md` is updated at every stopping point, so a usage-limit cut-off loses nothing.

## 6. Done

The Matrix layer is done when every stage's design note is approved and implemented,
`LEAN_NUM_THREADS=4 lake build NLAlib NLAlibScaffold` is green, `scripts/Audit.lean` reports zero violations,
`scripts/Lint.lean` is clean, `check_refs.py` passes, `docs/port/ledger.json` accounts for every
public declaration of the prototype's `Matrix/` (ported, dropped with reason, or scaffolded), and
`docs/port/status.md` lists what is in `NLAlibScaffold` with a difficulty estimate for each item.
The orchestrator then writes `docs/design/Matrix-REPORT.md`: the interfaces the layer exports
(the §5.3 rows and §5.4 predicates it added, each with its intended consumers), counts (files,
declarations, scaffolds), and what CONTRIBUTING should say differently before the Probability
layer is designed.
