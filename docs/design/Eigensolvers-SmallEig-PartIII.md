# SmallEig on the operation core: Hessenberg shifted QR III (SMALLEIG)

Stage SMALLEIG formalizes [BanksGarzaVargasSrivastava2025] (Part III, arXiv 2205.06804:
"Global convergence of Hessenberg shifted QR III: approximate Ritz values via shifted inverse
iteration"). Its algorithm becomes the `SmallEig` routine that the merged finite-precision
shifted QR of Part II (PR #149, [Eigensolvers-ShiftedQR-FiniteOps](Eigensolvers-ShiftedQR-FiniteOps.md))
assumes through the kernel hypothesis `NLAlib.ShiftedQR.IsRandomSmallEig`. With it, the shifted QR
headline holds with no algorithmic oracle, conditional only on two random-matrix theorems (the
eigenvalue gap and the eigenvector condition number of a complex Gaussian perturbation), which an
outside collaborator proves ([spec](#11-material)) and which this stage takes as hypotheses.

This note is the design only: no Lean is written, no target, check, allowlist, CI file or build
pin changes, and nothing in `*Targets.lean` or `docs/targets.*`. Base: `origin/main` @6f049b04.
Inputs: the sizing study `Sizing-BGS-PartIII.md` (cited "sizing §n"), the collaborator spec
`Spec-RandomMatrix-GinibreGapKappaV.md` ("spec"), the independent errata review
`Review-Fable-PartIII-Errata.md` ("review"), the Part III and Part II LaTeX, and the merged Lean.
Targets: `~/nlalib-harness/pilot/smalleig-targets.json` (92 targets, plus 4 optional and 5 of the
collaborator's, listed for the dependency graph). Revised after Fable's design review
(`Review-Fable-SMALLEIG-Design.md`, verdict "revise, then approve for skeleton"): §12 lists every
item and its fix.

**Superseded in part by SCHUR** ([Eigensolvers-DenseSchur](Eigensolvers-DenseSchur.md) §14.6,
§15–§17). The stage SCHUR rewrote the programs of this note in place in Schur mode: `smallEigProg`
is a small-block Schur solver `[d, nq, T] (Bk, Qw) → (Bk, Ub)` (the eigenvalues are the diagonal
of the triangular block, the accumulator is in `Ub`), `rhess`, `decoupleLast`, `smallEigDecoupler`
and the core record their rotations in a slotted Givens log, and the headlines (a)–(c) are
corollaries of the Schur theorems (`smallEigProg_pwrites_schur`,
`smallEigProg_randomSchurLeafContract`, `ShiftedQR.roundedShQRSchur_measureReal_not_schur_le`).
The eigenvalue-only programs and contracts named below are removed: the oracle-leaf `roundedShQR`
and its certificate `shqrAlgorithm`, `seLeaf`, `liftLeaf`, `solveRounded`,
`RandomLeafContract`, `RandomLeafRoutineContract`, `BackwardLeaf(Routine)Contract`,
`TerminatingLeaf`, and `copyLeaf` (now `identityLeaf`); the leaf contract is
`Schur.RandomSchurLeafContract`. The constants of §14 are updated there; the rest of this note is
the design record of SMALLEIG and is not rewritten.

## 0. Summary

* **Three headlines (§1).** (a) Part III's Theorem 1.1 as a program theorem: `smallEigProg` on any
  $n \times n$ complex input stores, with probability $\ge 1 - \varphi$, the spectrum of
  $\mathbf{M} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta$, under
  $\boldsymbol{u} \le \boldsymbol{u}_{\mathsf{SmallEig}}$ with $O(\log^2)$ bits, terminating on every
  tape, with an explicit static operation count. (b) Corollary 1.3: the forward-error contract on
  blocks of order $\le k$ and norm $\le \Sigma$. (c) The shifted QR headline T1c with
  `hSE : IsRandomSmallEig …` replaced by the program, conditional only on the two random-matrix
  hypotheses, at $\boldsymbol{u} \le \min(\boldsymbol{u}_{\mathrm{ShQR}}, \boldsymbol{u}_{\mathsf{SmallEig}})$.
* **One change to merged code is required (§2.1).** The `SmallEig` call in the merged programs has
  no operand for parameter words and no cap dimension (`run smallEigLeaf [k] (B, S)`,
  `run L [d] (W, Out[2 lo])`). A program needs both (its $\gamma, \omega, \eta_{1,2}$, loop caps
  depend on $\Sigma, \beta, \varphi$; they cannot be literals, since a program is fixed before the
  data). Every substitution mechanism, `Stmt.link` included, needs this operand. The words sit at
  the tail of the parameter list, viewed as `P[np - nq]`. Design: the
  routine becomes a parameter `SE : Stmt` of `…With` versions of the merged programs, and every
  merged program is re-defined as a thin wrapper at the kernel. **No merged theorem statement
  changes**; the only numerals that may move are the work constants of the certificate (RF7).
* **No probabilistic substitution rule exists for adaptive programs (§2.1).** `Interp.TapeLocal.link`
  and `Profile.Refines` need a static window (`Stmt.Straight`). The general rule is specified
  (OL1–OL4: stopping-time locality `Interp.TapeAdapted`, the `PWrites` rules over it, and
  `PWrites.link_iff`); the routine-parameter route does not need it, so it is optional (decision D2).
* **`IsRandomSmallEig` is kept (§2.2).** A new routine contract `RandomSmallEigContract` (orders
  $\le k_{\max}$, norm $\le \Sigma$, any number of streams) is consumed by the generalized chain;
  the kernel predicate implies it, so T1c is a corollary. The merged leaf contract
  `RandomLeafContract` quantifies every order, which no non-oracle leaf can meet; the bounded form
  follows the `nmax`/`Nmax` precedent of `RandomDecouplingContract`.
* **Errata (§3).** The review confirms P1–P16 (three with one sub-claim refuted) and finds N1–N8.
  The corrections used here are the confirmed ones; P1, P2, P11 disappear because the shattering
  vocabulary is not formalized (the class "$\kappa(\mathbf{V}) \le B$, gap $\ge g$" replaces it,
  sizing D10); P3/N1 disappear because the random vector is applied by rotations, not by the
  paper's reflector; Lemma 5.2 and Appendix A disappear because the random direction is a
  Gaussian vector (anti-concentration from the merged projected small ball).
* **Size (§5).** 92 targets: L1 21 (S 12, M 6, L 3), L2 41 (S 17, M 17, L 7), L3 10 (S 8, M 2),
  L4 20 (S 6, M 9, L 5); optional OL 4 (S 1, M 3); collaborator 5 (M 2, L 2, XL 1). Twelve waves
  (0–11) by longest dependency path; waves 0–2 hold 60 targets.
* **Open decisions (§8):** precision model (one `StdModel`), substitution mechanism (routine
  parameter), the hypothesis (new contract + bridge), wave order (refactor, every program
  definition and M11 first), a normalized tail record, the cap dimension with $m$ among the caps,
  the RHess-per-node algorithm.

## 1. The goal and the headlines

Notation: `S` is $\Sigma$ in Lean (`Σ` is reserved syntax), $\mathbf{H}$ order $n + 1$ as in Part II.
`PolyLogTail` is a record `(C a b c : ℝ)`; the random-matrix hypotheses take one each (§2.8).
Streams: $s_U$ uniform on $[0,1]$ (the merged disk sampler), $s_G$ standard real Gaussian (new).

### 1.1 (a) Part III, Theorem 1.1, as a program theorem

`smallEigProg sG : Stmt O Q`, interface `[d, nq, T] (Bk, Q) → (Ev)`: for $d \le 1$ copy the entry;
otherwise copy the block to scratch, perturb by $\gamma'\mathbf{G}$ with $\gamma' = \mathrm{fl}(\gamma/\sqrt d)$
computed in the program from $2d^2$ Gaussian draws (rounded), reduce to
Hessenberg form bottom-up (rounded Givens), and run the merged worklist `solveRoundedWith` at
$k = 1$ with the decoupler `smallEigDecoupler` (`RHess`; `OneEig`; `Decouple`) and the order-1
leaf `copyLeaf`. Parameter words in `Q` (`smallEigParams nmax …`, one list for every order
$\le n_{\max}$), loop caps $m = 2^q, t, m_2 \le T$ read from them by `bindIdx` ($q$ with bound $m$).

```lean
theorem smallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : PolyLogTail.BoundsGinibreGap c₁) (hB : PolyLogTail.BoundsGinibreCondition c₂)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg sG (O := O) (Q := Q))
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, o]) (Store.inBlock o.1 o.2 (2 * (n + 1)))
      (SmallEigSpectrum o M δ) μ} ≤ φ
```

`SmallEigInput` bundles live, room, apart, $\mathbf{M}$ stored at `w` and the words
`smallEigParams nmax S δ φ c₁ c₂` at `q`; `SmallEigSpectrum o M δ μ'` is
`∃ roots E, specNorm E ≤ δ ∧ IsEigenvalueListing (M + E) roots ∧ HoldsMatrix o (col roots) μ'.store`;
`smallEigDims n nmax … = [n + 1, nq, smallEigCap nmax …]`. The tail records enter only through their normalization (RMn), so `hb₁`, `hb₂` are the only side conditions on them. Companions: `smallEig_relative` (TH2: $\delta\|\mathbf{M}\|_2$
with $\|\mathbf{M}\|_2 \le \Sigma \le c\|\mathbf{M}\|_2$; the review's P9/N4: $\Sigma$ is an input of
Theorem 1.1 the paper does not state), `smallEigProg_terminates` (SE2, every tape, any input, cap words valid: `SmallEigCaps T qs`),
`logb_inv_uSmallEig_le` (PA4: $\log_2(1/\boldsymbol{u}_{\mathsf{SmallEig}}) \le c_1\log_2^2 Y + c_2$,
$Y = 4n_{\max}\Sigma/(\delta\varphi)$, with $c_1, c_2$ chosen after the tail records), `smallEig_work_le` (TH5: static count
$\le c(n+1)^4(T+1)^2$ on every tape; the review's N5 factor $n$ is inside) and the certificate
`smallEigAlgorithm` (TH6: cost and correctness on one counted run, no oracle in the model).

**Absolute, not relative** (sizing §3.3 item 4). Theorem 6.1 (`eig.tex:32`; "Theorem 5.1" in the
sizing study) assumes $\Sigma/2 \le \|\mathbf{M}\| \le \Sigma$; a zero or tiny block is outside
it. Here only $\|\mathbf{M}\|_2 \le \Sigma$ is assumed; $\gamma$, $\omega$ are set from $\delta$ and
$\Sigma$; the collaborator's range condition $2\gamma \le \|\mathbf{M}\|$ is met inside the proof by
no shift when $2\gamma \le \|\mathbf{M}\|$ and the shift $\mathbf{M} + 4\gamma\mathbf{I}$ otherwise
(norm in $[2\gamma, 6\gamma]$), which changes neither gap nor $\kappa(\mathbf{V})$ (M13, RM4).

**Failure budget** (review S2). The failure $\varphi$ of (a) is split once, in PA1:

| event | target | budget |
|---|---|---|
| gap of $\mathbf{M} + \gamma'\mathbf{G}$ below $t_1$ | RM4/RM5 (Theorem A) | $\varphi/4$ |
| no diagonalization with $\kappa \le t_2^{-1}$ | RM4/RM5 (Theorem B) | $\varphi/4$ |
| $\|\gamma'\mathbf{G}\| > \gamma W$ | RM6 | $\varphi/4$ |
| the worklist: $2(n+1)$ decoupler calls, each `RHess` + `OneEig` | CO1, D3b | $\varphi/4$, i.e. $\varphi_D = \varphi/(8(n+1))$ |

RM5 and RM6 take a free budget $\varphi'$ instead of the earlier hard-coded $\varphi/3$.

### 1.2 (b) Corollary 1.3, forward error on small blocks

```lean
theorem smallEigProg_randomSmallEigContract … (same machine, sampler and tape hypotheses;
    hA, hB, hb₁, hb₂) {kmax : ℕ} {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) (hqs : SmallEigCaps … qs) :
    RandomSmallEigContract law β φ kmax (smallEigForwardCap kmax S β φ c₁ c₂) S
      (smallEigForwardParams kmax S β φ c₁ c₂) (smallEigProg sG) I
```

The words are the ones of (a) at $n_{\max} = k_{\max}$: one list `qs` serves every order
$d \le k_{\max}$ (review B1). The backward accuracy is $\delta_b = \Sigma(\beta/(4(2k_{\max}+1)\Sigma))^{k_{\max}}$ up to a
constant (PA5), and the forward error comes from two matchings (M14): linear on the class from
$\mathbf{A} + \gamma\mathbf{G} + \mathbf{E}$ to $\mathbf{A} + \gamma\mathbf{G}$
(`norm_sub_le_of_matching`), and Ostrowski–Elsner with a matching (M11) from
$\mathbf{A} + \gamma\mathbf{G}$ to $\mathbf{A}$; the $k$-th root is paid only on $\gamma$ (sizing
§3.3 item 5). Bits $O(k_{\max}^2\log^2(k_{\max}\Sigma K/(\beta\varphi)))$, as Corollary 1.3. The
probability form for one input is TH4 `smallEig_measureReal_not_forward_le`.

### 1.3 (c) The shifted QR headline without the oracle

`roundedShQRSmallEig sG := roundedShQRWith (smallEigProg sG)`, interface
`[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`, parameter words
`shqrSmallEigParams = shqrParams ++ smallEigForwardParams k (4Σ) βse φse c₁ c₂` (the SmallEig words
at the tail, read as `P[np - nq]`) with
$\beta_{se}$ = `shqrSmallEigAccuracy`, $\varphi_{se}$ = `shqrSmallEigFailure` (both merged).

```lean
theorem roundedShQRSmallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : PolyLogTail.BoundsGinibreGap c₁) (hB : PolyLogTail.BoundsGinibreCondition c₂)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSmallEig n k B Γ S δ φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig sG (O := O) (Q := Q))
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ c₁ c₂) [a, t, p, out, f]) (shqrFp n a out f)
      (ShQRSpectrum out f H δ) μ} ≤ φ
```

Compared with the merged T1c (`RoundedTheorems.lean:163`): `hSE`, `hβse0`, `hse`, `hφse0`, `hφse`
are gone; new are `hSmp`, `hG` (the Gaussian stream), `hA`, `hB`, `hb₁`, `hb₂`; `hu` is against
$\min(\boldsymbol{u}_{\mathrm{ShQR}}, \boldsymbol{u}_{\mathsf{SmallEig}}^{\mathrm{fwd}})$ (HL1); the op
set no longer needs `[Has EigenvalueKernelOp O]`. Companions: HL3 termination (no $\boldsymbol{u}$,
class or random-matrix hypothesis), HL4 bits
$\log_2(1/\boldsymbol{u}) \le c_1 k\log_2 Y + c_2k^2\log_2^2Y + c_3$ with
$Y = 4(n+1)B\Sigma^2K/(\delta\min(\Gamma,\Sigma)\varphi)$ (T2's argument, scale-invariant), which with
the new `shqrDegree_le_log` ($k = O(\log B\log\log B)$; merged has only $k \le 512B^2$) is
$O(\log^4 Y)$ up to $(\log\log Y)^2$; HL5 work with `SmallEig` counted; HL6 the certificate with no
oracle in the model; HL7 the relative and Hermitian corollaries (optional).

**What is not claimed.** The random-matrix theorems (hypotheses `hA`, `hB` until the collaborator
delivers; RM3 then discharges them); a rounded disk sampler or rounded Gaussian sampler (the
draws are exact tape values, as Part II's disk sample; the rounding after the draw is modelled);
range safety (no under/overflow, `StdModel`); the paper's $O(n^3)$ question (sizing §6: the
per-node re-randomization is kept).

## 2. The hypothesis redesign (sizing §3.3)

### 2.1 SmallEig as a program in the kernel's place

**What Ops has (checked).** `Stmt.link`/`Interp.link`/`run_link` (`Ops/Link.lean`) substitute an
`Impl` for an operation, pointwise in the tape. `Algorithm.link` (`Ops/Cert.lean:370`) needs
the linked interpretation to meet the model's contracts (`Interp.link_satisfies`), i.e. a
deterministic or relational contract of the operation. The law-level transfer
`Profile.Refines.measureReal_not_runs_le` (`Ops/Law.lean`) needs the linked operation to be
`TapeLocal` with a fixed window, which `Interp.TapeLocal.link` (`Ops/Tape.lean:251`) gives only
for a `Stmt.Straight` implementation (no tests, no index binders). `SmallEig` is adaptive (capped
loops with early exit; the number of disk draws depends on earlier draws), so **no existing rule
substitutes it**. The merged composition rules (`PWrites.seq`, `.ite`, `.whileFuel`, `.loop`,
`.bindIdx`) take `hloc : ∀ o, I.TapeLocal o (win o)` and use it only through `run_follows`.

**The general rule, specified (OL1–OL4, optional; decision D2).** Stopping-time locality:

```lean
/-- A call reads the tape only from its start position up to its end position, and never moves
the position back. A tape-local operation is tape-adapted; an implementation over tape-adapted
operations induces a tape-adapted operation, whatever its control flow. -/
def Interp.TapeAdapted (I : Interp Op Tst K) (o : Op) : Prop :=
  ∀ d ins outs (τ τ' : Tape K),
    Follows τ τ' (I.callS o d ins outs τ) (I.callS o d ins outs τ')

theorem Interp.TapeLocal.tapeAdapted (h : I.TapeLocal o k) : I.TapeAdapted o
theorem run_follows_of_tapeAdapted (hI : ∀ o, I.TapeAdapted o) (τ τ') (s ρ) :
    Follows τ τ' (eval I τ s ρ) (eval I τ' s ρ)
theorem Interp.TapeAdapted.link (hI : ∀ o, I.TapeAdapted o) (T : Table Op₁ Op₂ Tst) :
    ∀ o, (I.link T).TapeAdapted o
theorem Interp.IsMeasurable.link (hI : I.IsMeasurable) (T : Table Op₁ Op₂ Tst) :
    (I.link T).IsMeasurable
theorem PWrites.link_iff : PWrites law I (s.link T) ρ F Pre Post φ ↔
    PWrites law (I.link T) s ρ F Pre Post φ
-- and PWrites.seq/ite/whileFuel/loop/bindIdx with (hA : ∀ o, I.TapeAdapted o)
```

"Independence of the substituted program's reads" is exactly `TapeAdapted`: the good set of the
caller after the substituted call is determined from the call's (random) end position on, which
`PWrites.seq` already handles by the strong Markov property at that stopping time
(`IsTapeLaw.measure_inter_shift_mem`). With OL1–OL4 a theorem proved against a `PWrites`
contract on an *operation* transfers to the linked program. But the merged Part II chain is
proved against the fixed-window kernel through `PWrites.of_window`, with `hloc` in about 28
theorems; the link route would restate all of them with `TapeAdapted`.

**The route recommended: the routine as a parameter (RF1–RF7).** The merged worklist is already
generic in its routines (`solveRounded D L`). The same pattern for `SmallEig`:

* `regularizeWith SE`, `shIterationWith SE`, `roundedDecoupleLoopWith SE`,
  `roundedDecoupleWith SE`, `solveRoundedWith D L`, `roundedShQRWith SE` (RF2a, RF3, RF5). Inside,
  `SE` is inlined, so every operation the proofs see is a base operation (scalar, index,
  sample, polar sampler), all tape-local: **`hloc` and every composition rule are used as they
  are**.
* Each merged name becomes a wrapper at `SE := smallEigKernel` (the kernel call, ignoring `Q`),
  `nq = T = 0`: its interface, and the text of every merged statement, are unchanged; its proofs
  become corollaries of the `…With` theorems through RF1's bridge.

**The required change, exactly.** The routine needs (i) its parameter words and (ii) a cap
dimension:

* (i) $\gamma, \omega, \eta_1, \eta_2$, the thresholds and the caps depend on
  $(k, \Sigma, \beta_{se}, \varphi_{se})$ and the tail constants. `ScalarOp.lit` takes rationals only,
  and a program family indexed by them would select the program from the data (forbidden,
  [programs](../contributing/programs.md) "fixed programs"). So the call must read words: the
  `SmallEig` interface widens from `[d] (Bk) → (Ev)` to `[d, nq, T] (Bk, Q) → (Ev)`, with `Q` the
  view `P[np - nq]` of the parameter words: the SmallEig words are the tail of `P` and `nq`, their
  fixed count, is a numeral of the program text (`opsIdx` accepts numerals and scoped names
  only, so it cannot be a Lean variable; PA1 states `(smallEigParams …).length = nq₀`). The length of `roundedDecoupleParams …` is
  $10 + 2|\mathrm{excNet}\,\varepsilon|$ (`RoundedDecouple.lean:102–112`), not a literal (review B2);
  `IExp.sub` is truncated and `np` is in scope at both call sites. The With theorems are stated for
  `roundedDecoupleParams … ++ qs`; the merged ones are the case `qs = []`.
* (ii) the caps $m, t, m_2$ are read by `bindIdx`, whose bound is an index expression; without a
  dimension `T` the static count (TH5, HL5) has no bound. The `DistSpec` degree $m = 2^q$ is itself a
  cap word: `IExp` has no power (`Ops/Syntax.lean:40`), and with only $q \le T$ the count would be
  $2^T$ (review B4). $q$ is read with bound $m$, as the merged programs carry $k$ and $\log_2 k$.
* The two call sites: `run smallEigLeaf [k] (B, S)` in `regularizeWithScratch`
  (`RoundedRegularize.lean:137`) and `run L [d] (W, Out[2 lo])` in the worklist round
  (`RoundedSolve.lean:186`). The second also forces a **bounded** leaf contract: the merged
  `RandomLeafContract` quantifies every order $d$, so a leaf that is not an oracle (`copyLeaf`
  handles $d \le 1$; `smallEigProg` is analysed for $d \le k$, $\|\mathbf{B}\| \le \Sigma$) cannot meet
  it. The bounded `RandomLeafRoutineContract law β φ kmax Nmax ps T L I` follows the precedent of
  `RandomDecouplingContract`'s `nmax`/`Nmax` (Part II note §2.1, found while proving P11p).
* Statement-level consequences in merged code: none in theorem text. The certificate
  (`RoundedCertification.lean`) states its work polynomial as numerals in a definition
  (`196017(n+1)^3(k+1)^3(n_p+1)(F+1) + 8b^4\bar w` before this stage); the wrapper's extra frame
  changed the static count, and with it the numeral, now `196218` (RF7, §14). T5's witness `2011` is inside a proof of `∃ c`.
  (Removed by SCHUR: the oracle program, its certificate and T5 are deleted; see the banner.)

### 2.2 `IsRandomSmallEig`: bounded orders and norm, any number of streams

`IsRandomSmallEig law s β φ I` (`RoundedKernels.lean:80`) is kept unchanged. The generalized chain
consumes instead (RF1):

```lean
def RandomSmallEigContract (law : ℕ → Measure ℝ) (β φ : ℝ) (kmax T : ℕ) (S : ℝ) (qs : List ℝ)
    (SE : Stmt O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w q o : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax →
    IsUpperHessenberg B → specNorm B ≤ S →
    PWrites law I SE (Env.frame [d, qs.length, T] [w, q, o]) (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock q.1 q.2 qs.length = some qs ∧
        μ.Live [w, q, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)) ∧
        Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ

def TerminatingSmallEig (T : ℕ) (qs : List ℝ) (SE : Stmt O Q) (I : Interp O Q ℝ) : Prop := …
  -- every tape, every input block: Writes .total … (fun _ => True)

theorem IsRandomSmallEig.randomSmallEigContract (h : IsRandomSmallEig law s β φ I) :
    RandomSmallEigContract law β φ kmax T S qs smallEigKernel I

-- the leaf bridge (review S7 i), as `IsRandomSmallEig.randomLeafContract`
-- (removed by SCHUR with `seLeaf` and `RandomLeafRoutineContract`; the leaf contract is now
-- `Schur.RandomSchurLeafContract`):
theorem RandomSmallEigContract.randomLeafRoutineContract (h : RandomSmallEigContract …) (hβ : 0 ≤ β) :
    RandomLeafRoutineContract law β φ kmax S ps T (seLeaf SE) I

-- the cap words (review B5): exact naturals, m = 2^q, m, t, m₂ ≤ T
def SmallEigCaps (T : ℕ) (qs : List ℝ) : Prop := …
```

`TerminatingSmallEig kmax T qs SE I` (orders $\le k_{\max}$) is claimed for `smallEigProg` only
under `SmallEigCaps T qs` and `IsExactNatLit id Mch kmax`:
`bindIdx` fails on a negative or too large word (`Ops/Exec.lean:127`), so a run with junk cap words
is not total.

The three mismatches of sizing §3.3 items 2, 3, 7 are resolved: orders $\le k_{\max}$ and norms
$\le \Sigma$ are hypotheses (the callers have them: the trailing $k \times k$ block of an iterate has
norm $\le$ the iterate's $4\Sigma$; a leaf block has order $\le k$ and norm $\le N_0 = 2\Sigma$, so
the contract is used at $k_{\max} = k$, $\Sigma_{se} = 4\Sigma$); the contract is a `PWrites`
statement, so the routine may read any number of streams adaptively; failure is a probability of
the run, not of one window. Restating `IsRandomSmallEig` in place with bounds (option D3b) would
still be a kernel predicate, which a program cannot meet; it would also change T1c's hypothesis.

### 2.3 Precision

One `StdModel u` for the whole run (recommended, D1): $\boldsymbol{u} \le
\min(\boldsymbol{u}_{\mathrm{ShQR}}, \boldsymbol{u}_{\mathsf{SmallEig}}^{\mathrm{fwd}})$ (HL1). The
merged T1c needs only `hu : u ≤ uShQR`, and `StdModel` hypotheses are used at one $\boldsymbol{u}$,
so nothing merged changes. The bit count becomes HL4:
$O(k\log Y) + O(k^2\log^2 Y)$, i.e. $O(\log^4 Y)$ up to $(\log\log Y)^2$ since
$k = O(\log B\log\log B)$, against $O(k\log Y)$ for Part II alone. Part II's remark that only
`SmallEig` needs the high precision is a **two-precision model** (D1b): a second scalar group
`ScalarOp ⊕ ScalarOp` with machines `Mch`, `Mch'`, conversion operations with their own
contracts, and the `SmallEig` program over the second group. Cost: every `IsScalar` hypothesis of
the merged chain is about the first group only, so the chain is unaffected, but the routine
contract, the conversion error at the call boundary (the block and the returned words), and a
second `StdModel` enter every `SmallEig` lemma; the certificate needs two word formats. Gain: the
shifted QR iterations keep $O(k\log Y)$ bits. Recommended as a follow-up, not now.

### 2.4 Gaussian draws on the tape

A second stream $s_G$ with `law sG = gaussianReal 0 1` (new headline hypothesis `hG`), drawn by the
catalog operation `SampleOp.draw sG` (`Ops/Catalog/Sampling.lean`, contract `IsSample I`: the
stored word is the tape entry). The tape law makes all entries independent across positions and
streams (`IsTapeLaw.indep`), so Gaussian and uniform draws compose by the merged `PWrites` rules.
Complex entries are $(x + iy)/\sqrt2$ with the rounding of
`Matrix/FinitePrecision/OpsSampling.lean` (`normalWords`, `normalSample_div_sqrt_two`,
`abs_sub_mul_sqrtHalf_le`), so the stored perturbation is the exact
$\gamma d^{-1/2}\mathbf{G}$ (law `complexGaussianMatrix`, RM8) plus a deterministic rounding error
absorbed in the backward error (GP2). The random direction of `RHess` is a Gaussian vector of
$2N$ draws, not a sphere sample: anti-concentration is the merged projected small ball with a
rank-one projector (RM7) and the norm from the Gaussian norm tail (RM6), so the paper's
Lemma 5.2, its sphere sampler (`preliminaries.tex:25`) and Appendix A are not needed.

### 2.5 Loop caps and failure words

| loop | paper | here |
|---|---|---|
| `SmallEig` retry `While cor = false` (`eig.tex:18`) | uncapped, not analysed | removed: one `OneEig` attempt per node, failure counted in $\varphi$ (review P13) |
| `OneEig` rounds | uncapped; $t$ too small (P6); start $H_{nn} + w$ | `whileFuel` $t = \lceil 2\log_2(5.2\Sigma/\beta')\rceil$, flag on failure (M4b); start at a polar disk sample $w_0$ of radius $\eta_2$ (review B3: an unperturbed start $s_0 = 0$ may be an eigenvalue) |
| `Decouple` steps (`decoupling.tex:68`) | uncapped | $m_2$ steps, flag at the cap (DC1) |
| `DistSpec` degree | $m$ any | $m = 2^q$, both cap words, $m \le T$, $q \le m$ (`sqrtIter`; review B4) |
| deflation recursion | unbounded tree | merged worklist, $2N$ rounds (`solveRounded`) |
| `RHess`, reduction | counted | counted |

Every cap is a parameter word read by `bindIdx` with bound `T`; the run is total on every tape
(SE2), the static count holds on every tape (TH5), and a flag makes the decoupler's
`RandomDecouplingContract` success branch false, so the worklist's union bound counts it.

### 2.6 Hessenberg inputs and the $1\times1$ base case

Part III takes any matrix; Part II calls it on Hessenberg blocks. The contract assumes Hessenberg
input (what the callers have); the program does not use it (the perturbation destroys the
structure and the bottom-up reduction restores it). Orders $0$ and $1$ are copied (review P13).

### 2.7 The class instead of shattering (sizing D10)

Not formalized: Definition 2.12, Lemmas 2.10–2.13, 6.3, 6.4, 6.5 and the contour integral. The
paper uses shattering only to carry "$\kappa_V \le n\zeta/\epsilon$, gap $\ge \zeta$" through
`RHess`, `Decouple` and `Deflate`. The merged library carries the class
`pseudoConditionNumber V ≤ B ∧ gap ≥ g` through perturbations and deflations
(`exists_pseudoConditionNumber_le_and_le_norm_sub`, `DeflationInv.exists_pseudoConditionNumber_subBlock_le`),
which is what the worklist theorem consumes. Effect on the errata: P1 (false Lemma 2.13), P2,
P11, N3 (one eigenvalue per disk) do not arise. The class doubles once per level, as Part II's
B3: perturbation $(2/t_2, t_1/2)$, after the top-level reduction $(4/t_2, t_1/4)$, worklist blocks
$(8/t_2, t_1/8)$, inside the decoupler after `RHess` $(16/t_2, t_1/16)$; only logarithms change.

### 2.8 The random-matrix hypotheses

The spec's two theorems are hypotheses through named predicates (rule 2), defined in the
collaborator's file `RandomMatrix/Shattering/GinibreClass.lean` with the *weak forms'* bodies
(RM1, RM2), parametrized by `PolyLogTail`. The weak forms are consumed because the preferred
forms imply them (RM3, when delivered) and the spec allows either. The two events are combined by
RM4 (ours, as the spec assigns): for every $\mathbf{M}$ (shift trick of §1.1), the probability
that $\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ has no diagonalization with $\kappa \le t_2^{-1}$ and
separation $t_1$ is at most the sum of the two tails (outer measure; the diagonalization's
$\mathbf{d}$ is a listing and two listings differ by a permutation). `PWrites.of_window` needs a
**measurable** bad set jointly in memory and window; the spec's events carry no measurability, so
the bad set is the complement of the class set, which is closed (M12) and contains the spec's
event. RM5 inverts the tails ($\log(1/t_i) = O_{a,b,c}(\log(n\Sigma K/(\gamma\varphi)))$, spec §2).

**Normalized record** (review S1). The weak forms give $(C, a, b, c)$ with only $0 < b$; RMn
derives each tail at $(\max(C,1), \max(a,0), b, \max(c,0))$, valid because $|n| \ge 1$ and the
base $K \ge 2$ in the range. Every parameter is defined from the normalized record, so
$\log_2(C/\varphi)$ is not junk and the tails are monotone in the order (needed for one word list at
$n_{\max}$) and in $K$. PA4 and HL4 quantify the records before their constants.

**Alignment with the spec** (checked against `Spec-RandomMatrix-GinibreGapKappaV.md` §3). RM1 and
RM2 copy the bodies, binders and universe (`Type`) of the spec's `exists_forall_…` weak forms, so
RM9's plug lemmas are `Iff.rfl` up to repackaging $(C, a, b, c)$ as a record, each with an `example`
restating the spec's binders verbatim (a binder drift fails at skeleton time). The preferred
forms imply the weak ones by RM3, at $(1, 3, 2, 0)$ for A and $(18, 3, 2, 2)$ for B (review S9). The
scaling is the spec's $\gamma\,|n|^{-1/2}\,\mathbf{G}$ with `complexGaussianMatrix`; since the
statements hold for every $\gamma > 0$, the program's rounded scale $\gamma' = \mathrm{fl}(\gamma/\sqrt d)$
is used as the $\gamma$ of the statement at order $d$ (review B1). HL8 is the final corollary with
`hA`, `hB` discharged, its statement fixed now.

## 3. Re-derivation table

Status: **correct** (the review checked it), **corrected** (confirmed erratum, correction
adopted), **avoided** (the design does not formalize the item), **pending** (not settled by the
review). "Review" = `Review-Fable-PartIII-Errata.md`.

| item | where | status | used as | target |
|---|---|---|---|---|
| Thm 1.1 | `intro.tex:7` | corrected: $\Sigma$ an input (P9c, N4), base case and caps (P13), absolute error | TH1 | TH1, TH2 |
| Lemma 1.2 (Bhatia–Elsner–Krause) | `intro.tex:20` | correct (review P17: not an error); constant $2n+1$ planned, 4 optional | M11 | M11 |
| Cor 1.3 | `intro.tex:34` | correct arithmetic ($\delta = (\beta/12)^n$, review); survives with the same asymptotics | TH3 | TH3, TH4 |
| $m$-th root | `preliminaries.tex:15` | avoided: $m = 2^q$, `sqrtIter` | K1 (merged) | — |
| samplers (sphere, disk, Ginibre) | `preliminaries.tex:25–40` | avoided: tape draws, rotations, Gaussian direction | §2.4 | GD1, RM7, RM8 |
| IQR backward error | `preliminaries.tex:65` | corrected (G16: $m\nu\boldsymbol{u} \le 1/4$; implied here, review) | merged Q2 | — |
| IQR forward error | `preliminaries.tex:82` | corrected (G8 $(2+2C)^{-m}$, 33; N1 phase; N5 base; N6 Frobenius) | merged Q4 | — |
| `Tau` (Part II Lemma 3.9) | `preliminaries.tex:113` | corrected (G9, review: $+O(\log)$ bits) | merged Q5, `IsHalfTau` | M17 |
| approximate functional calculus | `preliminaries.tex:49` | correct | merged `EigenvectorWeights` | M1a, M1b |
| regularization of shifts | `preliminaries.tex:128` | correct ($\eta_2 \ge \eta_1$ unnecessary, Part II L3.10) | merged D3 | OE2 |
| pseudospectral perturbation and Bauer–Fike (2.10, 2.11) | `preliminaries.tex:149,163` | avoided (§2.7); P2 confirmed typo | — | — |
| Def 2.12, Lemma 2.13 | `preliminaries.tex:173,183` | avoided; P1 confirmed false as stated | — | — |
| Prop 3.1 (`DistSpec`) | `oneig.tex:27` | correct (0.998, 1.003; review) | M1a, M1b, M17 | DS2 |
| Obs 3.2 (six points) | `oneig.tex:66` | corrected: needs $\eta_2 \le 0.039\tau$; the algorithm's $\eta_2 = \beta/5$ breaks Lemma 3.8 (P5); $\eta_2 = \beta'/40$ | M3 | M3, M4c |
| "$m$ is large enough" | `oneig.tex:124` | correct; $\log = \log_2$ (P7) | M4a | M4a |
| $\eta_1 + \eta_2 \le \operatorname{gap}/2$ | `oneig.tex:146` | correct with P5's $\eta_2$; N6 typo ($\eta_1$ for $\eta_2$) | M4c | M4c |
| Prop 3.5 (`OneEig`) | `oneig.tex:159` | corrected: $\eta_2$ (P5), $t$ (P6), $\log_2$ (P7), "Requires $\beta \le 1/2$" dropped (P13) | OE2 | OE2 |
| accuracy of the $\tau_i$, reach $10\Sigma$ | `oneig.tex:187,199` | correct (review: $2.222 \le 2.3$, $1.222 \le 1.3$, $8.79 \le 8.8$) | M5 | M5 |
| Lemma 3.8, guaranteeing the flag | `oneig.tex:226` | corrected: statement garbled (N6), fails with P5's $\eta_2$; restated on an abstract run | M6 | M6 |
| Lemma 4.1 (exact decoupling) | `decoupling.tex:7` | correct | M2 | M2 |
| Lemma 4.2, Prop 4.3 (`Decouple`) | `decoupling.tex:34,77` | correct (choice of $m$, $\omega/4$ budget, $C = 1.5$; review); cap added (P13); N8 typo | M7, DC2 | DC2 |
| Def 5.1 (stable bottom-up Hessenberg form) | `randhess.tex:29` | corrected: **proved** for a Givens program, not assumed | HR2 | HR1–HR3 |
| Lemma 5.2 (anti-concentration) | `randhess.tex:43` | correct (review), P15 typos; avoided: Gaussian direction | RM7 | RM7 |
| Prop 5.3 (`RHess`) | `randhess.tex:68` | corrected: P3/N1 (reflector phase; false *statement*) avoided by rotations; P4 (eigenvectors depend on $u$) fixed by applying anti-concentration to $\mathbf{A}$'s eigenvectors and transferring (M10); P14 absorbed; backward error constants correct (review) | M8–M10, RH3 | RH3 |
| Thm 6.1 (quantitative; "5.1" in sizing) | `eig.tex:32` | corrected: class form (§2.7), the worklist at $k = 1$ | CO1 | CO1 |
| Lemma 6.2 (preservation) | `eig.tex:60` | corrected: hypothesis N2 (needs `RHess`'s event); carried by `PWrites.seq`; norm and class by merged lemmas | D3b, D3d | D3b |
| Lemmas 6.3, 6.4 | `eig.tex:72,80` | avoided (§2.7); P11 confirmed proof gap, "$\epsilon \le \Sigma$" refuted | — | — |
| Lemma 6.5 (shattering) | `eig.tex:197` | avoided: replaced by RM4/RM5; P8 constants moot | RM4, RM5 | RM4, RM5 |
| Proof of Thm 1.1 | `eig.tex:206` | corrected: $\epsilon/2$ (P9a), $\Sigma$ for $\|\mathbf{M}\|$ (P9b, c); "$\delta\|M\|(1+\delta/4)$" refuted (P9); $\delta \le 2/3$ (N4) moot in the absolute form; N7 typos | TH1 | TH1 |
| Running time | `eig.tex:49` | corrected: on every tape by caps (P13); factor $n$ in the last term (N5) | TH5 | TH5 |
| Lemma B.1 (gap) | `shattering.tex:6` | pending: not checked against BGKS (review P17); hypothesis RM1 | RM1 | CR7 |
| Lemma B.2 ($\kappa_V$) | `shattering.tex:13` | correct statement; P10 typo in the proof (review, spec) | RM2 | CR6 |
| Lemma B.3 (Davies) | `shattering.tex:23` | pending: not checked against BKMS (review P17) | via RM2 | CR5 |
| App. A ($\lvert u_1\rvert^2 \sim$ Beta) | `randvector.tex` | avoided (Gaussian direction) | — | — |

Inherited Part II items G8, G9, G16, N1, N5, N6: the merged lemmas are the corrected ones; the
review checked that $\boldsymbol{u}_{\mathsf{SmallEig}}$ implies their corrected hypotheses ("no
impact" or $+O(\log)$ bits). Sizing §6's one-step-decoupling variant is research and not used.

## 4. Layers

### L0 — imported (merged, no targets)

Rounded steps and their analysis: `multiStepStable`, `multiStepStable_isStableQRChain`
(`Eigensolvers/ShiftedQR/StableStep.lean`), `IsStableQRChain.isPerturbedUnitarySimilar`,
`IsStableQRChain.exists_frobNorm_conj_sub_le` (`Matrix/QRIteration/StableStep*.lean`),
`IsStableQRChain.abs_prod_last_sub_le`; `stepComptau`, `comptauHalf`, `repeatBlock`, `IsHalfTau`
(`RoundedFind.lean`); `sqrtIter`, `Ops.StdModel.abs_sqrtIter_sub_le`
(`Matrix/FinitePrecision/RootsRounded.lean`); rounded Givens G1–G5
(`Matrix/FinitePrecision/GivensRounded.lean`), rotation loops (`RotationLoops.lean`,
`RowRotation.lean`); `bottomScan`; the worklist `solveRounded`,
`solveRounded_measureReal_not_spectrum_le`, `RandomDecouplingContract`; weights
`lastRowWeights`, `sum_lastRowWeights_mul_sq_le`, `norm_mul_diagonal_mul_inv_last_sq_le`
(`Matrix/QRIteration/EigenvectorWeights.lean`); class perturbation
`exists_pseudoConditionNumber_le_and_le_norm_sub`, `norm_sub_le_of_matching`,
`exists_pseudoConditionNumber_add_le_and_norm_sub_le` (`Matrix/Perturbation/EigenvalueBackward.lean`),
`DeflationInv.*`; forward ⇒ backward `IsEigenvalueListing.exists_specNorm_sub_le`; disk law
`measureReal_diskUniform_closedBall_le`, `measureReal_exists_norm_add_sub_lt_le`, `polarDisk`,
`map_polarDisk_eq_diskUniform`, `IsPolarDiskSampler`; Gaussian
`measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix`,
`measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector`,
`complexGaussianMatrix_eq_map_gaussianMatrix`; samples `SampleOp`, `IsSample`, `OpsSampling`;
the probability logic `PWrites` with `of_window`, `seq`, `ite`, `whileFuel`, `loop`, `bindIdx`,
`allocs`, `in_frame`, `measureReal_not_writes_le` (`Ops/Logic/Probabilistic.lean`), `IsTapeLaw`
(`Ops/TapeLaw.lean`), the certificate bridge `Algorithm.measureReal_not_accepts_le_of_wp`
(`Ops/Probability.lean`), static counts `stmtWorkMono`, `size_stmtCost_le_stmtWorkMono`.

### L1 — exact mathematics (21 targets)

Distance to the spectrum by inverse iteration (M1a, M1b, Prop 3.1 in row form, no roots), exact
decoupling (M2), the hexagonal net (M3), the parameter arithmetic (M4a–c), the abstract `OneEig`
run (M5, M6, as the merged abstract while loop S6), rounded decoupling on chains (M7), weights
after a unitary similarity fixing $\mathbf{e}_n$ (M8, M9), weights under perturbation (M10, the P4
fix), Ostrowski–Elsner with a matching by compactness (M11a continuity of listings, M11b Elsner's
per-root bound, M11c homotopy and matching), the closed class set (M12), shift invariance (M13),
forward error through a class matrix (M14), rotation of $\mathbf{e}_N$ to a computed vector (M15),
DistSpec's composite error (M17). All but M4a–c, M5, M6, M17 are general and go in topic files
(§6); M5, M6 carry this algorithm's constants (0.66, 4.6, 10) and live in
`Eigensolvers/SmallEig/OneEigMath.lean` (review S6). Under the six-point net lemma M3 is general,
with the radii as parameters.

### L2 — the solver on the class (41 targets)

Programs, each with its word-level `Writes`, its guarantee and its termination: the rounded
bottom-up Hessenberg reduction (HR1–HR3, general), Gaussian draws (GD1), the perturbation
(GP1–GP3), `RHess` (RH1–RH4), `DistSpec` (DS1–DS3), `OneEig` (OE1–OE3), `Decouple` (DC1–DC3),
the decoupler and its `RandomDecouplingContract` at $k = 1$ (D3a–D3d), the order-1 leaf (LF1,
LF2), the core = merged worklist at $k = 1$ (CO1, CO2: Theorem 6.1 in class form), the program
(SE1, SE2), parameters and precision (PA1–PA5), and the theorems (TH1–TH6).

### L3 — the random-matrix interface (10 targets; collaborator R3–R7)

Ours: the hypothesis predicates RM1, RM2; their normalization RMn; the plug lemmas RM9; RM3 (preferred ⇒ weak, when delivered); the glue RM4;
the inversion RM5; the rescaled norm tail RM6 (R1); anti-concentration RM7 (R2); the law of a
window RM8. The collaborator's (spec §4): CR3 shifted $\sigma_{\min}$, CR4 area formula, CR5 Davies,
CR6 Theorem B, CR7 Theorem A. Sizing's R8 (shattering) is replaced by RM4.

### L4 — the link to shifted QR (20 targets; 4 optional)

The refactor RF1–RF8 (§2.1, statements unchanged; RF4 split by file group into RF4a–d, RF8 the
leaf bridge), the combined parameters and precision HL1,
the headline HL2, termination HL3, bits HL4, work HL5, certificate HL6, corollaries HL7, the discharged placeholder HL8; optional
OL1–OL4 (§2.1, decision D2).

## 5. Target table

Generated from the same data as `~/nlalib-harness/pilot/smalleig-targets.json`. Waves are the
longest dependency path (every target strictly after the theorems it uses; program definitions,
`kind = program`, are written with the skeleton and delay nothing). Kinds: `gen` general library
(topic file, stage-free docstring), `stage` this algorithm, `refactor` merged files, `hyp`
hypothesis interface, `program` definition only, `optional` decision D2. The collaborator's CR3–CR7
are in the JSON only.

| id | statement | file | size | depends_on | wave | kind |
|---|---|---|---|---|---|---|
| M1a | `NLAlib.norm_lastRow_inv_pow_le` — H V d, IsUnit V, H * V = V * diagonal d, (∀ i, s ≠ d i), 1 ≤ m: ‖toLp 2 ((s • 1 - H)⁻¹ ^ m) (Fin.last n)‖ ≤ pseudoConditionNumber V * (⨅ i, ‖s - d i‖)⁻¹ ^ m  (Prop 3.1, lower bound on τ, row form) | Matrix/QRIteration/InverseIteration.lean (new) | S | — | 0 | gen |
| M1b | `NLAlib.sqrt_lastRowWeights_mul_le_norm_lastRow_inv_pow` — same hypotheses, every i: √(lastRowWeights V i) * ‖s - d i‖⁻¹ ^ m ≤ pseudoConditionNumber V * ‖toLp 2 ((s • 1 - H)⁻¹ ^ m) (Fin.last n)‖  (Prop 3.1 upper bound on τ, row form) | Matrix/QRIteration/InverseIteration.lean (new) | S | — | 0 | gen |
| M3 | `NLAlib.exists_norm_hexNet_add_sub_le` — Covering lemma for the six-point net of an annulus, radii as parameters (review S6): 0 < r₁ ≤ r ≤ r₂, ρ(r₁, r₂, r) an explicit covering radius of {s + r e^{iπj/3}} for r₁ ≤ ‖z - s‖ ≤ r₂, ‖w‖ ≤ η ⇒ ∃ j : Fin 6, ‖s + r e^{iπj/3} + w - z‖ ≤ ρ + η. Instance (Obs 3.2 corrected, P5): r₁ = τ/1.1, r₂ = τ/0.9, r = τ gives ρ ≤ 0.561 τ, so 1.1(ρ + η) ≤ 0.66 τ for η ≤ 0.039 τ | Matrix/QRIteration/InverseIteration.lean (new) (P9 review warning: ℂ geometry; ForMathlib candidate) | S | — | 0 | gen |
| M4a | `NLAlib.SmallEig.distSpecDegree_spec` — 'm is large enough' (`oneig.tex:124`): m = 2^q ≥ m₁ = ⌈12 log₂ κ + 6 log₂(1/p)⌉ gives 0.998 ≤ κ^{-1/m} and κ^{1/m} p^{-1/(2m)} ≤ 1.003 (log = log₂, P7) | Eigensolvers/SmallEig/Parameters.lean | S | — | 0 | stage |
| M4b | `NLAlib.SmallEig.oneEigRounds_spec` — P6 corrected: t = ⌈2 log₂(5.2 S/β)⌉ gives 4.6·0.66^t/0.9 ≤ β/S and 6t + 1 ≤ 12 log₂(7.8 S/β), for 0 < β ≤ S | Eigensolvers/SmallEig/Parameters.lean | S | — | 0 | stage |
| M4c | `NLAlib.SmallEig.oneEigRadii_spec` — `oneig.tex:146` with P5, P6: η₂ = β/40 ∧ g/3, η₁ = η₂ (φ/(12 log₂(8S/β)))^{1/2}: for 0 < β ≤ 0.8 S (true at β' = ω/20; review S4): η₁ + η₂ ≤ g/2, η₂ ≤ 0.02 S, (6t+1)(η₁/η₂)² ≤ φ | Eigensolvers/SmallEig/Parameters.lean | S | — | 0 | stage |
| M8 | `NLAlib.lastRowWeights_conjTranspose_mul` — A * V = V * diagonal d, x a unit vector, Q with last column c • x, ‖c‖ = 1 (as built: no unitarity hypothesis): lastRowWeights (Qᴴ * V) i = ‖star x ⬝ᵥ V.col i‖² / ‖toLp 2 (Vᴴ *ᵥ x)‖²  (Prop 5.3, deterministic part; P3 phase handled by c) | Matrix/QRIteration/EigenvectorWeights.lean | S | — | 0 | gen |
| M10 | `NLAlib.exists_lastRowWeights_ge_of_norm_sub_le` — P4 fix (review: confirmed; direct eigenvector perturbation route): class (V, d, κ ≤ B, gap g) for A, ‖E‖ ≤ g/(16(n+1)B) · θ: ∃ V' d' diagonalizing A + E with κ(V') ≤ 2B and, for every Q (as built: no unitarity hypothesis) with Q e_n = c x, lastRowWeights (Qᴴ V') i ≥ lastRowWeights (Qᴴ V) i / 4 - c₀ n B² ‖E‖/g | Matrix/Perturbation/EigenvalueBackward.lean | L | — | 0 | gen |
| M11a | `NLAlib.exists_tendsto_isEigenvalueListing` — Continuity of eigenvalue listings by compactness (review S5: no Rouché, no root continuity in the pinned Mathlib): A_j → A, ev_j listings of A_j ⇒ a subsequence and permutations σ_j with ev_j ∘ σ_j → ev, a listing of A (listings bounded by ‖A_j‖; `∏ (X - C (d i))` continuous in d; `charpoly` continuous; uniqueness of the factorization over ℂ) | Matrix/Perturbation/EigenvalueMatching.lean (new) | M | — | 0 | gen |
| M11b | `NLAlib.exists_norm_sub_le_rpow_of_mem_spectrum` — Elsner's per-root bound: every eigenvalue λ' of A' (order N) has an eigenvalue λ of A with ‖λ' - λ‖ ≤ (‖A‖ + ‖A'‖)^{1 - 1/N} ‖A' - A‖^{1/N} | Matrix/Perturbation/EigenvalueMatching.lean (new) | S | — | 0 | gen |
| M12 | `NLAlib.isClosed_setOf_exists_pseudoConditionNumber_le_and_le_norm_sub` — IsClosed {A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ \| ∃ V d, IsUnit V ∧ A * V = V * diagonal d ∧ pseudoConditionNumber V ≤ B ∧ ∀ i j, i ≠ j → g ≤ ‖d i - d j‖} | Matrix/Spectral/Diagonalizable.lean | M | — | 0 | gen |
| M13 | `NLAlib.mul_eq_mul_diagonal_add_smul_one_iff` — (A + c • 1) * V = V * diagonal (d + c) ↔ A * V = V * diagonal d; gap and κ(V) unchanged (the shift trick for the collaborator's ‖M‖ ≥ 2γ hypothesis) | Matrix/Spectral/Diagonalizable.lean | S | — | 0 | gen |
| M15 | `NLAlib.Ops.StdModel.exists_hasOrthonormalCols_rotateTo` — Rounded rotation of e_N to a computed unit vector: N−1 rounded Givens rotations from the words of g give exact unitary Q with Q e_N = c · g/‖g‖, ‖c‖ = 1, and the computed similarity is within c₁ N u ‖A‖ of Qᴴ A Q | Matrix/FinitePrecision/GivensRounded.lean | M | — | 0 | gen |
| M17 | `NLAlib.SmallEig.abs_distSpecWord_sub_le` — Composite error of DistSpec: computed product within 0.0011 (IsHalfTau) and q rounded square roots (3u each, `abs_sqrtIter_sub_le`) give τ̂ ∈ [0.998, 1.003]·τ under 30000(m+1)u ≤ 1 | Eigensolvers/SmallEig/DistSpec.lean | S | — | 0 | stage |
| M2 | `NLAlib.exists_le_norm_subdiag_shiftedQR_pow` — Lemma 4.1: H upper Hessenberg, diagonalizable (V, d), s ∉ spec, 1 ≤ m, H_ℓ the exact shifted QR iterates with shift s: ∃ ℓ ∈ [1, m], ‖(H_ℓ) (last) (last-1)‖ ≤ κ(V)^{1/m} · ‖s - d i⋆‖ · w_{i⋆}^{-1/(2m)} for the nearest i⋆ (stated with powers: ‖·‖^m ≤ κ · dist^m / √w) | Matrix/QRIteration/InverseIteration.lean (new) | M | M1b | 1 | gen |
| M5 | `NLAlib.SmallEig.OneEigRun.dist_le_and_norm_le` — Lemma 3.7 on an abstract run (sequence s_i, τ_i with 0.9 dist(s_i) ≤ τ_i ≤ 1.1 dist(s_i), s_{i+1} ∈ net(s_i, τ_i) + w_i, τ_{i+1} ≤ 0.66 τ_i): start ‖s₀‖ ≤ η₂, dist(s₀) ≤ ‖H‖ + η₂ (review B3); τ_i ≤ 4.6·0.66^i S_0 and ‖s_i‖ ≤ 10 S (reach D(0, 10S)) | Eigensolvers/SmallEig/OneEigMath.lean | M | M3 | 1 | stage |
| M9 | `NLAlib.le_lastRowWeights_conjTranspose_mul` — x = g/‖g‖ with ‖g‖ ≤ R, ‖star g ⬝ᵥ V.col i‖ ≥ s‖V.col i‖ ⇒ s² / (R² · pseudoConditionNumber V ²) ≤ lastRowWeights (Qᴴ * V) i  (any column scaling of V) | Matrix/QRIteration/EigenvectorWeights.lean | S | M8 | 1 | gen |
| M11c | `NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow` — Ostrowski–Elsner with a matching (Lemma 1.2; constant 2N − 1 = 2n + 1 for order n + 1): for every listing ev of A there is a listing ev' of A' with ‖ev' i - ev i‖ ≤ (2n+1)(‖A‖ + ‖A'‖)^{1-1/(n+1)}‖A' - A‖^{1/(n+1)} | Matrix/Perturbation/EigenvalueMatching.lean (new) | L | M11a, M11b | 1 | gen |
| M6 | `NLAlib.SmallEig.OneEigRun.exists_le_of_rounds` — Lemma 3.8 + success paragraph (P6 t): if every net point of every round is at distance ≥ η₁ from the spectrum, some round i ≤ t has τ_i ≤ 0.9β, hence dist(s_i) ≤ β; and the accepted point has dist ≥ η₁ | Eigensolvers/SmallEig/OneEigMath.lean | M | M3, M5, M4b | 2 | stage |
| M7 | `NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_dist` — Lemmas 4.2/Prop 4.3 math: H Hessenberg, class (V, d, κ ≤ B), weight w_{i⋆} ≥ p, η₁ ≤ dist(s) ≤ β', chains of ℓ ≤ m₂ rounded degree-1 steps with shift s under mx ≤ 1/4 (G16) and the corrected forward-error hypothesis (G8, Q4 with Hessenberg H): some ℓ ≤ m₂ has computed \|(Ĥ_ℓ)_{n,n-1}\| ≤ ω | Matrix/QRIteration/StableStepForward.lean | L | M2 | 2 | gen |
| M14 | `NLAlib.exists_isEigenvalueListing_norm_sub_le_of_class` — Forward error through a class matrix: A arbitrary, A₁ = A + E₁ in class (κ ≤ B, gap g), roots a listing of A₁ + E₂ with ‖E₂‖ ≤ g/(16(n+1)B): ∃ ev listing of A, ∀ i, ‖roots i - ev i‖ ≤ B‖E₂‖ + (2n+1)(2‖A‖+‖E₁‖)^{1-1/(n+1)}‖E₁‖^{1/(n+1)} | Matrix/Perturbation/EigenvalueMatching.lean (new) | S | M11c | 2 | gen |
| HR1 | `NLAlib.hessenbergReduceLast, hessenbergReduceLast_writes_word` — New because the merged exact `hessenbergReduction` (`Matrix/Factorizations/Hessenberg.lean:239`) is top-down, fixes e₁ and is not a program (review S11). Program `[N] (A) → (A)`: bottom-up reduction to upper Hessenberg form by rounded Givens rotations acting on both sides, fixing e_N; word-level Writes (stored words = the machine evaluation) | Eigensolvers/HessenbergReduction.lean (new, general) | M | — | 0 | gen |
| GD1 | `NLAlib.SmallEig.gaussDraws, gaussDraws_writes` — `[m] () → (G)`: m samples of the stream sG (`SampleOp.draw sG`, IsSample); stores the window; advances the position by m | Eigensolvers/SmallEig/Draws.lean | S | — | 0 | stage |
| DS1 | `NLAlib.SmallEig.distSpec, distSpec_writes_word` — `[N, m, q] (H, s) → (τ)`: copy H, `repeatBlock` the shift m times, `stepComptau` (multiStepStable + product of \|R̂_nn\|), `sqrtIter` q; m = 2^q is a parameter word read by `bindIdx` with bound T and q with bound m (review B4: `2^q` is not an `IExp`; the merged programs carry k and log₂ k the same way); Writes on scratch | Eigensolvers/SmallEig/DistSpec.lean | M | — | 0 | stage |
| DC1 | `NLAlib.SmallEig.decoupleLast, decoupleLast_writes_word` — `[N, m₂] (H, λ̃, Q) → (H, Fl)`: ≤ m₂ rounded degree-1 steps with shift λ̃ (`multiStepStable` at m = 1), `bottomScan` (k = 1) with the loop threshold t_L after each; Fl = 1 if the cap is reached (P13) | Eigensolvers/SmallEig/Decouple.lean | M | — | 0 | stage |
| D3a | `NLAlib.SmallEig.smallEigDecoupler` — `[n+1, 1, np, F] (W, P) → (W, Fl)` (the decoupler interface of `solveRoundedWith`): rhess; oneEig; if Fl = 0 then decoupleLast; caps m, t, m₂ read from P by `bindIdx` (bound F), q with bound m | Eigensolvers/SmallEig/Decoupler.lean | S | RH1, OE1, DC1 | 0 | program |
| D3d | `NLAlib.SmallEig.class_of_rhess` — A block in class (2B, g/2) and ‖Ĥ - QᴴAQ‖ ≤ g/(32(n+1)B) ⇒ Ĥ in class (4B, g/4) | Eigensolvers/SmallEig/Decoupler.lean | S | — | 0 | stage |
| SE1 | `NLAlib.SmallEig.smallEigProg` — `[d, nq, T] (Bk, Q) → (Ev)`: if d ≤ 1 copy; else copy the block to allocated scratch (review S8: GP1 and HR1 work in place, the footprint is Ev only), ginibrePerturb; hessenbergReduceLast; smallEigCore (words from Q, threshold word from Q). Computable [E2] | Eigensolvers/SmallEig/Program.lean | S | GP1, HR1, D3a, LF1 | 0 | program |
| HR2 | `NLAlib.hessenbergReduceLast_isPerturbedUnitarySimilar` — StdModel u, (N+1)u small: the run stores Ĥ upper Hessenberg with ∃ Q unitary, Q e_N = e_N, ‖Ĥ - Qᴴ A Q‖ ≤ c_H N² u ‖A‖ (Def 5.1 'C-stable bottom-up Hessenberg form', proved, not assumed) | Eigensolvers/HessenbergReduction.lean (new, general) | L | HR1, M15 | 1 | gen |
| HR3 | `NLAlib.hessenbergReduceLast_terminates` — Total on every tape (no tape reads) | Eigensolvers/HessenbergReduction.lean (new, general) | S | HR1 | 1 | gen |
| GP1 | `NLAlib.SmallEig.ginibrePerturb, ginibrePerturb_writes_word` — `[N, nq] (A, Q) → (A)`: reads γ from Q and computes γ' := fl(γ / √N) in the program (index literal N, `sqrt`, `div`; γ' = γN^{-1/2}(1 + θ), \|θ\| ≤ 3u), draws 2N² Gaussians and stores fl(A + γ' · normalSample(x, y)); word-level Writes (review B1) | Eigensolvers/SmallEig/Perturb.lean | M | GD1 | 1 | stage |
| RH1 | `NLAlib.SmallEig.rhess, rhess_writes_word` — `[N] (A) → (A)`: 2N Gaussian draws g, the N−1 rotations taking e_N to g/‖g‖ (up to phase) on both sides, then `hessenbergReduceLast`; word-level Writes | Eigensolvers/SmallEig/RandomHessenberg.lean | M | GD1, HR1 | 1 | stage |
| DS2 | `NLAlib.SmallEig.distSpec_accuracy` — Prop 3.1 and 'm is large enough' (correct per review): H Hessenberg in class (κ ≤ B, weights ≥ p), s ∈ D(0, 10S), dist(s) ≥ η₁, m = 2^q per M4a, u ≤ u_DS: 0.9 dist(s) ≤ τ̂ ≤ 1.1 dist(s) | Eigensolvers/SmallEig/DistSpec.lean | M | DS1, M1a, M1b, M4a, M17 | 1 | stage |
| DS3 | `NLAlib.SmallEig.distSpec_terminates` — Total on every tape | Eigensolvers/SmallEig/DistSpec.lean | S | DS1 | 1 | stage |
| OE1 | `NLAlib.SmallEig.oneEig, oneEig_writes_word` — `[N, q, t] (H, Q) → (λ̃, Fl)`: s₀ = w₀, a polar disk sample of radius η₂ (review B3: the paper starts at a perturbed point, `oneig.tex:87`, the '+1' of 6t+1), τ₀ = distSpec; ≤ t rounds (`whileFuel` t): one polar disk sample w (radius η₂), the six points s + τ e^{iπj/3} + w (rounded; cos/sin of π/3 from `sqrt` of 3), six distSpec calls, keep the argmin if ≤ 0.66τ else set Fl = 1 and exit; exit with Fl = 0 when τ ≤ 0.9β'. One attempt, no retry loop (P13) | Eigensolvers/SmallEig/OneEig.lean | L | DS1 | 1 | stage |
| DC3 | `NLAlib.SmallEig.decoupleLast_terminates` — Total on every tape | Eigensolvers/SmallEig/Decouple.lean | S | DC1 | 1 | stage |
| GP2 | `NLAlib.Ops.StdModel.specNorm_perturbWords_sub_le` — ‖Â - (A + (γ/√N) G)‖ ≤ c N u (‖A‖ + γ‖G‖/√N), G the exact complex Gaussian of the window | Matrix/FinitePrecision/OpsSampling.lean | S | GP1 | 2 | gen |
| RH2 | `NLAlib.SmallEig.rhess_isPerturbedUnitarySimilar` — All tapes: Ĥ Hessenberg, ∃ Q unitary with Q e_N = c·g/‖g‖, ‖Ĥ - Qᴴ A Q‖ ≤ c_R N² u ‖A‖ | Eigensolvers/SmallEig/RandomHessenberg.lean | M | RH1, HR2, M15 | 2 | stage |
| RH4 | `NLAlib.SmallEig.rhess_terminates` — Total on every tape | Eigensolvers/SmallEig/RandomHessenberg.lean | S | RH1, HR3 | 2 | stage |
| OE3 | `NLAlib.SmallEig.oneEig_terminates` — Total on every tape (capped) | Eigensolvers/SmallEig/OneEig.lean | S | OE1, DS3 | 2 | stage |
| LF1 | `NLAlib.SmallEig.copyLeaf, copyLeaf_randomLeafRoutineContract` — `[d, np, T] (Bk, P) → (Ev)` copying the single entry; for d ≤ 1 meets `RandomLeafRoutineContract law 0 0 1 Nmax ps T` | Eigensolvers/SmallEig/Leaf.lean | S | RF2a | 2 | stage |
| TH5 | `NLAlib.SmallEig.smallEig_work_le` — ∃ c, ∀ n nq T, Count.size (stmtCost smallEigProg [n+1, nq, T]) ≤ c (n+1)^4 (T+1)^2 (true with m, t, m₂ ≤ T: N·(N³ + 6t·m·N² + m₂N²), review B4) (static: on every tape; review N5: the t·m·log m term carries the factor n) | Eigensolvers/SmallEig/Theorems.lean | M | SE1, RF2a | 2 | stage |
| GP3 | `NLAlib.SmallEig.ginibrePerturb_pwrites` — At every order N ≤ nmax, words at nmax (review B1). PWrites: from A with ‖A‖ ≤ S, except with probability tail(t₁) + tail(t₂) + φ_norm ≤ 3φ/4 (budget table §1.1, review S2), the stored Â is in the class (κ ≤ 2/t₂, gap ≥ t₁/2), ‖Â‖ ≤ S + 2γW, and Â = A + E₁ with ‖E₁‖ ≤ γW + c N u(...) | Eigensolvers/SmallEig/Perturb.lean | M | GP1, GP2, RM4, RM5, RM6, RM8, M12 | 3 | stage |
| RH3 | `NLAlib.SmallEig.rhess_pwrites` — Prop 5.3 corrected (P3, P4, N1): A in class (κ ≤ B, gap g), ‖A‖ ≤ S, u ≤ u_RH: except with probability ≤ N s² + e^{-…} (RM7, RM6), Ĥ is in class (2B, g/2) with a diagonalization whose last-row weights are all ≥ p = s²/(64 R² B²) | Eigensolvers/SmallEig/RandomHessenberg.lean | L | RH2, M8, M9, M10, RM7, RM6, RM8 | 3 | stage |
| OE2 | `NLAlib.SmallEig.oneEig_pwrites` — Prop 3.5 corrected (P5 η₂ = β'/40, P6 t, P7 log₂; perturbed start, review B3): H in class with weights ≥ p, ‖H‖ ≤ S, u ≤ u_OE: except with probability ≤ (6t+1)(η₁/η₂)², Fl = 0 and η₁ ≤ dist(λ̃) ≤ β' | Eigensolvers/SmallEig/OneEig.lean | L | OE1, DS2, M3, M5, M6, M4b, M4c | 3 | stage |
| DC2 | `NLAlib.SmallEig.decoupleLast_spec` — Prop 4.3 (correct per review; G8, G16 corrected inputs): H Hessenberg in class with weights ≥ p, η₁ ≤ dist(λ̃) ≤ β' = ω/20, u ≤ u_DC: on every tape, Fl = 0, Ĥ' Hessenberg, IsPerturbedUnitarySimilar H Ĥ' (3.5 m₂ ‖H‖ ν u) and \|Ĥ'_{N,N-1}\| ≤ ω | Eigensolvers/SmallEig/Decouple.lean | M | DC1, M7 | 3 | stage |
| D3c | `NLAlib.SmallEig.smallEigDecoupler_terminatingDecoupler` — TerminatingDecoupler | Eigensolvers/SmallEig/Decoupler.lean | S | D3a, RH4, OE3, DC3 | 3 | stage |
| LF2 | `NLAlib.SmallEig.copyLeaf_terminates` — TerminatingLeafRoutine | Eigensolvers/SmallEig/Leaf.lean | S | LF1 | 3 | stage |
| D3b | `NLAlib.SmallEig.smallEigDecoupler_randomDecouplingContract` — `RandomDecouplingContract law (2B) (g/2) φ_D 1 F nmax Nmax ps ω (fun N => ε_D N) smallEigDecoupler I` with φ_D = φ_RH + φ_OE, ε_D N = (c_R N² + 3.5 m₂ ν) u N, under u ≤ u_D (nmax, Nmax) | Eigensolvers/SmallEig/Decoupler.lean | L | D3a, RH3, OE2, DC2, D3d | 4 | stage |
| CO2 | `NLAlib.SmallEig.smallEigCore_terminates` — Total on every tape | Eigensolvers/SmallEig/Core.lean | S | D3c, LF2, RF2b | 4 | stage |
| CO1 | `NLAlib.SmallEig.smallEigCore_measureReal_not_spectrum_le` — Theorem 6.1 (`eig.tex:32`; 'Theorem 5.1' in the sizing study) in the class form: `smallEigCore := solveRoundedWith smallEigDecoupler copyLeaf` at k = 1 on an upper Hessenberg A of order n+1 with κ ≤ B, gap ≥ g, ‖A‖ ≤ S, threshold and params of PA1, u ≤ u_core: fails to store the spectrum of A + E, ‖E‖ ≤ 2(n+1)(c + ε_D + 0), with probability ≤ 2(n+1)φ_D | Eigensolvers/SmallEig/Core.lean | M | RF2b, D3b, LF1 | 5 | stage |
| SE2 | `NLAlib.SmallEig.smallEigProg_terminates` — `SmallEigCaps T qs → IsExactNatLit id Mch kmax → TerminatingSmallEig kmax T qs smallEigProg I` (review B5: `bindIdx` fails on a negative or too large word, so not for every qs): every tape, any input matrix; no literal above the order is written, so `IsExactNatLit id Mch kmax` suffices | Eigensolvers/SmallEig/Program.lean | M | SE1, CO2, HR3 | 5 | stage |
| PA1 | `NLAlib.SmallEig.smallEigParams, smallEigParams_spec` — Words (γ, ω, β' = ω/20, η₁, η₂, threshold, t_L, m, q, t, m₂) from (nmax, S, δ, φ, c₁, c₂) at an outer order bound nmax, valid at every order ≤ nmax (review B1); failure budget φ/4 each to gap, κ, norm and core (review S2) and the side conditions of GP3, RH3, OE2, DC2, D3b, CO1 at once; Lemma 6.5 replaced by RM4/RM5 (no shattering vocabulary) | Eigensolvers/SmallEig/Parameters.lean | L | RM5, M4a, M4b, M4c, CO1, D3b, GP3 | 6 | stage |
| PA2 | `NLAlib.SmallEig.smallEigParams_pos, smallEigCaps_le` — Positivity of every word and of u_SmallEig; caps m, t, m₂ ≥ 1 and ≤ T := smallEigCap, q ≤ m, m = 2^q (review B4, D6); the words satisfy `SmallEigCaps T qs` (they are read by `bindIdx` with bound T from exact parameter words, so no literal above the order is written: `IsExactNatLit id Mch (n + 1)` suffices, as PAR1 checked for Part II) | Eigensolvers/SmallEig/Parameters.lean | M | PA1 | 7 | stage |
| PA3 | `NLAlib.SmallEig.uSmallEig, uSmallEig_spec` — u_SmallEig nmax … := min(u_GP, u_HR, u_RH, u_DS, u_DC) (u_core removed, §14.1) closed form at the outer bound nmax (review B1) (P12/G8/G9/G16 corrected inputs); spec: u ≤ uSmallEig ⇒ every u-hypothesis of GP3 … CO1 | Eigensolvers/SmallEig/Precision.lean | L | PA1 | 7 | stage |
| PA4 | `NLAlib.SmallEig.logb_inv_uSmallEig_le` — ∀ normalized tail records c₁' c₂', ∃ c₁ c₂, ∀ …, log₂(1/uSmallEig nmax S δ φ c₁' c₂') ≤ c₁ · log₂(Y)² + c₂, Y = 4 nmax S/(δ φ) (review S1: the tail constants are quantified before ∃ c, their exponents enter c₁): Theorem 1.1's O(log²) bits | Eigensolvers/SmallEig/Precision.lean | M | PA3 | 8 | stage |
| PA5 | `NLAlib.SmallEig.forwardBackwardError, uSmallEigForward` — δ_b(kmax, S, β) := S (β/(4(2kmax+1)S))^{kmax}·…: backward δ_b at order ≤ kmax gives forward β by M14; uSmallEigForward := uSmallEig at δ_b | Eigensolvers/SmallEig/Precision.lean | S | PA3, M14 | 8 | stage |
| TH1 | `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le` — Headline (a), §1.1: order n + 1 ≤ nmax, words and u₀ at nmax | Eigensolvers/SmallEig/Theorems.lean | M | CO1, GP3, SE1, PA1, PA3, HR2, RMn | 8 | stage |
| TH2 | `NLAlib.SmallEig.smallEig_relative` — Relative form: ‖M‖ ≤ S ≤ c‖M‖ (S a word, review P9/N4: Σ is an input of Theorem 1.1), error δ‖M‖ | Eigensolvers/SmallEig/Theorems.lean | S | TH1 | 9 | stage |
| TH3 | `NLAlib.SmallEig.smallEigProg_randomSmallEigContract` — Headline (b), §1.2: forward contract on orders ≤ kmax, norms ≤ S | Eigensolvers/SmallEig/Theorems.lean | M | TH1, PA5, M14 | 9 | stage |
| TH6 | `NLAlib.SmallEig.smallEigAlgorithm, smallEig_algorithm_measureReal_not_accepts_le` — Canonical certificate (confined, uniform, no oracle) and the accepts bound: cost and correctness on one counted run | Eigensolvers/SmallEig/Certification.lean | M | TH1, TH5, SE2 | 9 | stage |
| TH4 | `NLAlib.SmallEig.smallEig_measureReal_not_forward_le` — Corollary 1.3 as a probability statement for one input of order n+1 ≤ kmax | Eigensolvers/SmallEig/Theorems.lean | S | TH3 | 10 | stage |
| RM1 | `NLAlib.PolyLogTail.BoundsGinibreGap` — def PolyLogTail.BoundsGinibreGap (c : PolyLogTail) : Prop := ∀ {Ω : Type} {mΩ} {μ} {n : Type} [Fintype n] [DecidableEq n] {G}, HasLaw G (complexGaussianMatrix n n) μ → ∀ M {γ t}, 0 < γ → 2γ ≤ specNorm M → 0 < t → t ≤ γ → μ.real {ω \| ¬ ∃ d, IsEigenvalueListing (M + (γ/√card n) • G ω) d ∧ ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤ c.C · card n ^ c.a · (t/γ)^c.b · (specNorm M/γ + log(γ/t))^c.c  (the body of the spec's weak form A; `PolyLogTail` = (C a b c : ℝ)) | RandomMatrix/Shattering/GinibreClass.lean (new; collaborator's file, ours: defs + glue) | S | — | 0 | hyp |
| RM2 | `NLAlib.PolyLogTail.BoundsGinibreCondition` — def PolyLogTail.BoundsGinibreCondition (c : PolyLogTail) : Prop := (the body of the spec's weak form B: … 0 < t → t ≤ 1 → μ.real {ω \| ¬ ∃ V d, IsUnit V ∧ (M + (γ/√card n) • G ω) * V = V * diagonal d ∧ pseudoConditionNumber V ≤ t⁻¹} ≤ c.C card n^c.a t^c.b (specNorm M/γ + log t⁻¹)^c.c) | RandomMatrix/Shattering/GinibreClass.lean (new; collaborator's file, ours: defs + glue) | S | — | 0 | hyp |
| RM6 | `NLAlib.measureReal_specNorm_ge_mul_le_of_hasLaw_complexGaussianMatrix` — R1 rescaled, free budget (review S2): P[‖(γ/√n) G‖ ≥ γ W] ≤ φ' for W = 2√2 + √(log(1/φ')/n), 0 < φ' ≤ 1 | RandomMatrix/Gaussian/Complex.lean | S | — | 0 | gen |
| RM7 | `NLAlib.measureReal_norm_dotProduct_le_le_of_hasLaw_complexGaussianVector` — R2 without the sphere: g complex Gaussian vector, ‖v‖ = 1: P[‖star v ⬝ᵥ g‖ ≤ s] ≤ s²; with RM6 for ‖g‖ (n × 1 matrix) this replaces Lemma 5.2 and Appendix A | RandomMatrix/Gaussian/Complex/LeastSingularValue.lean | S | — | 0 | gen |
| RM8 | `NLAlib.hasLaw_complexGaussianMatrix_windowFn` — Under IsTapeLaw with law sG = gaussianReal 0 1, the matrix built from a window of 2N² entries of sG at a fixed position by (x + i y)/√2, column-major, has law complexGaussianMatrix (Fin N) (Fin N); likewise a vector from 2N entries | RandomMatrix/Gaussian/Tape.lean | S | — | 0 | gen |
| RMn | `NLAlib.PolyLogTail.normalize, PolyLogTail.BoundsGinibreGap.normalize, PolyLogTail.BoundsGinibreCondition.normalize` — Normalized record (review S1): PolyLogTail.BoundsGinibreGap c ⇒ PolyLogTail.BoundsGinibreGap c.normalize with c.normalize = (max C 1, max a 0, b, max c 0) (valid: card n ≥ 1 and the base K ≥ 2 in the range); same for the condition tail. Every parameter is defined from the normalized record: log₂(C/φ) is not junk, tails are monotone in the order and in K | RandomMatrix/Shattering/GinibreClass.lean (new; collaborator's file, ours: defs + glue) | S | RM1, RM2 | 1 | gen |
| RM4 | `NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix` — For every M (no norm condition), every γ > 0 (the program's rounded scale γ'/√d is a valid γ, review B1), 0 < t₁ ≤ γ, 0 < t₂ ≤ 1, RM1 c₁, RM2 c₂: μ.real {ω \| ¬ ∃ V d, IsUnit V ∧ (M + (γ/√n) G ω) V = V diag d ∧ κ(V) ≤ t₂⁻¹ ∧ ∀ i ≠ j, t₁ ≤ ‖d i - d j‖} ≤ tail c₁ n (K/…) + tail c₂ …, K = (‖M‖ + 4γ)/γ | RandomMatrix/Shattering/GinibreClass.lean (new; collaborator's file, ours: defs + glue) | M | RM1, RM2, M13, RMn | 2 | gen |
| RM5 | `NLAlib.SmallEig.ginibreClass_spec` — At an outer order bound nmax (review B1) and a free failure budget φ' (review S2): t₁(φ', nmax, S, γ, c₁), t₂(φ', nmax, S, γ, c₂) with each tail ≤ φ' at every order ≤ nmax (normalized record, a ≥ 0), 0 < t₁ ≤ γ, 0 < t₂ ≤ 1, and log₂(1/t_i) ≤ (a log₂(4 nmax) + log₂(C/φ') + c log₂ K + 1)/(b/2) | Eigensolvers/SmallEig/Parameters.lean | M | RM1, RM2, RMn | 2 | stage |
| RF1 | `NLAlib.ShiftedQR.RandomSmallEigContract, TerminatingSmallEig, smallEigKernel, IsRandomSmallEig.randomSmallEigContract, IsRandomSmallEig.terminatingSmallEig` — `RandomSmallEigContract law β φ kmax T S qs SE I`: ∀ d ≤ kmax, B Hessenberg, specNorm B ≤ S, PWrites law I SE (frame [d, qs.length, T] [w, q, o]) (inBlock o (2d)) (B, qs stored, live, room, apart) (∃ roots ev, IsEigenvalueListing B ev ∧ ∀ i, ‖roots i - ev i‖ ≤ β ∧ HoldsMatrix o (col roots)) φ; `TerminatingSmallEig kmax T qs SE I` the all-tape total run on orders ≤ kmax (elaboration: an unbounded order would need exact natural literals of every size); `smallEigKernel : [d, nq, T] (Bk, Q) → (Ev)` calls the kernel and ignores Q; bridges: IsRandomSmallEig law s β φ I → RandomSmallEigContract law β φ kmax T S qs smallEigKernel I (any kmax, T, S, qs) and → TerminatingSmallEig | Eigensolvers/ShiftedQR/RoundedKernels.lean | S | — | 0 | refactor |
| RF2a | `NLAlib.ShiftedQR.solveRoundedWith, liftLeaf; solveRounded as a wrapper` — `solveRoundedWith D L : [N, k, np, F, T] (A, Thr, P) → (Out, Fl)`, leaf call `run L [d, np, T] (W, P, Out[2 lo])`; `liftLeaf L : [d, np, T] (Bk, P) → (Ev) := run L [d] (Bk, Ev)`; `solveRounded D L := ops% [N,k,np,F] … { run (solveRoundedWith D (liftLeaf L)) [N,k,np,F,0] … }` (interface and every merged statement unchanged); contracts `RandomLeafRoutineContract law β φ kmax Nmax ps T L I`, `BackwardLeafRoutineContract`, `TerminatingLeafRoutine` (leaf frame [d, ps.length, T] [w, p, o], d ≤ kmax, norm ≤ Nmax) with bridges from the merged ones through liftLeaf | Eigensolvers/ShiftedQR/RoundedSolve.lean | M | RF1 | 1 | refactor |
| RF3 | `regularizeWith, regularizeWithScratchWith, shIterationWith, roundedDecoupleLoopWith, roundedDecoupleWith; merged names as wrappers` — Each program gains the routine `SE : Stmt O Q`, the operand `Q` (the view `P[np - nq]`: the SmallEig words are the tail of P; `nq` is the fixed word count of `smallEigParams`, a literal; review B2: the merged `roundedDecoupleParams` has length 10 + 2·\|excNet ε\|, not a literal) and the dimension `T`; `run smallEigLeaf [k] (B, S)` becomes `run SE [k, nq, T] (B, Q, S)`; the merged `regularize`, `shIteration`, `roundedDecouple` are wrappers at `SE := smallEigKernel`, `nq = T = 0` | Eigensolvers/ShiftedQR/RoundedRegularize.lean, RoundedIteration.lean, RoundedDecouple.lean | M | RF1 | 1 | refactor |
| RF2b | `solveRoundedWith_pwrites, solveRoundedWith_backward, solveRoundedWith_terminates; merged solveRounded_* as corollaries` — The worklist theorems for `solveRoundedWith` with `RandomLeafRoutineContract … n N₀ ps T` (the leaf gets blocks of order ≤ k and norm ≤ N₀); `solveRounded_pwrites`, `solveRounded_backward`, `solveRounded_measureReal_not_spectrum_le`, `solveRounded_terminates` re-derived, statements unchanged | Eigensolvers/ShiftedQR/RoundedHeadline.lean, RoundedSolveBackward.lean, RoundedSolveTermination.lean, RoundedWorklistTermination.lean | L | RF2a | 2 | refactor |
| RF4a | `With versions: regularizeWith_pwrites (P10, P14) with the SmallEig contract at d = k, ‖trailingBlock k H‖ ≤ ‖H‖ ≤ S_it` — regularizeWith_pwrites (P10, P14) with the SmallEig contract at d = k, ‖trailingBlock k H‖ ≤ ‖H‖ ≤ S_it; the parameter list is `roundedDecoupleParams … ++ qs` (review B2); the merged statements are the case `qs = []`, re-derived unchanged | Eigensolvers/ShiftedQR/RoundedRegularize.lean, Eigensolvers/ShiftedQR/RoundedRegularizeTrial.lean | L | RF3, RF1 | 2 | refactor |
| RF4b | `With versions: shIterationWith contract (P10b) threading SE` — shIterationWith contract (P10b) threading SE; the parameter list is `roundedDecoupleParams … ++ qs` (review B2); the merged statements are the case `qs = []`, re-derived unchanged | Eigensolvers/ShiftedQR/RoundedIteration.lean, Eigensolvers/ShiftedQR/RoundedSh*.lean | L | RF3, RF1 | 2 | refactor |
| RF4c | `With versions: roundedDecoupleWith_randomDecouplingContract (P11p) with ps = roundedDecoupleParams … ++ qs` — roundedDecoupleWith_randomDecouplingContract (P11p) with ps = roundedDecoupleParams … ++ qs; the parameter list is `roundedDecoupleParams … ++ qs` (review B2); the merged statements are the case `qs = []`, re-derived unchanged | Eigensolvers/ShiftedQR/RoundedDecouple.lean, Eigensolvers/ShiftedQR/RoundedDecoupleSpec.lean | L | RF3, RF1 | 2 | refactor |
| RF4d | `With versions: termination of the With versions from TerminatingSmallEig` — termination of the With versions from TerminatingSmallEig; the parameter list is `roundedDecoupleParams … ++ qs` (review B2); the merged statements are the case `qs = []`, re-derived unchanged | Eigensolvers/ShiftedQR/RoundedRegularizeTermination.lean, Eigensolvers/ShiftedQR/RoundedDecoupleTermination.lean, Eigensolvers/ShiftedQR/RoundedSolveTermination.lean | L | RF3, RF1 | 2 | refactor |
| RF8 | `NLAlib.ShiftedQR.RandomSmallEigContract.randomLeafRoutineContract, TerminatingSmallEig.terminatingLeafRoutine` — 0 ≤ β, RandomSmallEigContract law β φ kmax T S qs SE I ⇒ qs.length = nq₀ (the numeral of the program text) ⇒ RandomLeafRoutineContract law β φ kmax S (ps₀ ++ qs) T (seLeaf SE) I (forward ⇒ backward by `IsEigenvalueListing.exists_specNorm_sub_le`), and the termination bridge (review S7 i) | Eigensolvers/ShiftedQR/RoundedKernels.lean | S | RF1, RF2a | 2 | refactor |
| RF5 | `roundedShQRWith, roundedShQRWith_measureReal_not_spectrum_le, roundedShQRWith_terminates` — `roundedShQRWith SE := solveRoundedWith (roundedDecoupleWith SE) (seLeaf SE)` with dims [n+1, k, np, F, T]; T1c and T1d for it, with the contract at (k, T, 4Σ, βse, φse) in place of `hSE : IsRandomSmallEig` | Eigensolvers/ShiftedQR/RoundedTheorems.lean | M | RF2b, RF4a, RF4b, RF4c, RF4d, RF8 | 3 | refactor |
| RF6 | `roundedShQR_* re-derived (T1c, T1d, T3, T4, T5)` — `roundedShQR := wrapper of roundedShQRWith smallEigKernel at T = 0`; every merged headline re-proved from RF5, statement text unchanged; T5's witness constant (2011) re-computed by `kernel_rfl` if the wrapper frame changes the static count (the statement is ∃ c, unchanged) | Eigensolvers/ShiftedQR/RoundedTheorems.lean | S | RF5 | 4 | refactor |
| HL5 | `NLAlib.ShiftedQR.roundedShQRSmallEig_work_le` — ∃ c, static count of roundedShQRSmallEig at [n+1, k, np, F, T] ≤ c (n+1)^4 (k+1)^5 (np+1)(F+1)(T+1)^2 — SmallEig's cost now counted | Eigensolvers/ShiftedQR/RoundedSmallEig.lean (new) | M | RF5, TH5 | 4 | stage |
| RF7 | `shqrSpecification constants re-checked; shqrAlgorithm unchanged in shape` — The explicit work polynomial `196218(n+1)^3(k+1)^3(np+1)(F+1) + 8b^4 w̄` (was `196017`) and the kernel-call polynomial are recomputed by `kernel_rfl` for the wrapper body; if a numeral changes, the change is the only statement change of this stage in merged code (recorded in the PR read-back) | Eigensolvers/ShiftedQR/RoundedCertification.lean | M | RF6 | 5 | refactor |
| OL1 | `NLAlib.Ops.Interp.TapeAdapted, TapeLocal.tapeAdapted, run_follows_of_tapeAdapted` — def Interp.TapeAdapted I o := ∀ d ins outs τ τ', Follows τ τ' (I.call o d ins outs τ) (I.call o d ins outs τ'); TapeLocal ⇒ TapeAdapted; `run_follows` from ∀ o, TapeAdapted | Ops/Tape.lean | M | — | opt | optional |
| OL4 | `NLAlib.Ops.PWrites.link_iff, PWrites.call_link` — PWrites law I (s.link T) ρ F Pre Post φ ↔ PWrites law (I.link T) s ρ F Pre Post φ; a call of a substituted operation meets the PWrites spec of its implementation body | Ops/Logic/Probabilistic.lean | S | — | opt | optional |
| HL3 | `NLAlib.ShiftedQR.roundedShQRSmallEig_terminates` — Every tape; no u, class or RMT hypothesis; needs `hin` only (the stored words satisfy SmallEigCaps by PA2), as the merged `roundedShQR_terminates` | Eigensolvers/ShiftedQR/RoundedSmallEig.lean (new) | S | RF5, SE2, PA2 | 8 | stage |
| OL2 | `NLAlib.Ops.PWrites.seq_of_tapeAdapted (and ite, whileFuel, loop, bindIdx)` — The composition rules with `hA : ∀ o, I.TapeAdapted o` in place of `hloc`; old rules as corollaries | Ops/Logic/Probabilistic.lean | M | OL1 | opt | optional |
| OL3 | `NLAlib.Ops.Interp.TapeAdapted.link, Interp.IsMeasurable.link` — Substitution: over adapted (resp. measurable) operations, the interpretation induced by any table is adapted (resp. measurable) — no `Straight` requirement (contrast `Interp.TapeLocal.link`) | Ops/Tape.lean, Ops/Logic/Probabilistic.lean | M | OL1 | opt | optional |
| HL1 | `NLAlib.ShiftedQR.shqrSmallEigParams, uShQRSmallEig, shqrSmallEigCap` — words := shqrParams ++ smallEigForwardParams at (k, 4Σ, βse = shqrSmallEigAccuracy, φse = shqrSmallEigFailure); uShQRSmallEig := min (uShQR …) (uSmallEigForward k (4Σ) βse φse c₁ c₂); T := smallEigCap; positivity | Eigensolvers/ShiftedQR/RoundedSmallEig.lean (new) | M | PA3, PA5 | 9 | stage |
| HL2 | `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le` — Headline (c), §1.3 | Eigensolvers/ShiftedQR/RoundedSmallEig.lean (new) | M | HL1, TH3, RF5, SE2 | 10 | stage |
| HL4 | `NLAlib.ShiftedQR.logb_inv_uShQRSmallEig_le, shqrDegree_le_log` — ∃ c₁ c₂ c₃, log₂(1/uShQRSmallEig) ≤ c₁ k log₂ Y + c₂ k² (log₂ Y)² + c₃, Y = 4(n+1)BS²K/(δ min(Γ,S) φ); with k ≤ c (log₂ 4B + 1)(log₂ log₂ 16B + 1) this is O(log⁴ Y) up to (log log)² | Eigensolvers/ShiftedQR/RoundedSmallEig.lean (new) | M | HL1, PA4 | 10 | stage |
| HL6 | `NLAlib.ShiftedQR.shqrSmallEigAlgorithm, …_measureReal_not_accepts_le` — Certificate without a SmallEig oracle (the model is scalar + index + samples + polar sampler) | Eigensolvers/ShiftedQR/RoundedSmallEigCertification.lean (new) | M | HL2, HL5, TH6 | 11 | stage |
| HL7 | `NLAlib.ShiftedQR.roundedShQRSmallEig_relative, _hermitian` — Optional: the T3/T4 corollaries for the unconditional program | Eigensolvers/ShiftedQR/RoundedSmallEig.lean (new) | S | HL2 | 11 | stage |

**Totals.**

| layer | targets | S | M | L | XL |
|---|---|---|---|---|---|
| L1 | 21 | 12 | 6 | 3 | 0 |
| L2 | 41 | 17 | 17 | 7 | 0 |
| L3 (ours) | 10 | 8 | 2 | 0 | 0 |
| L4 | 20 | 6 | 9 | 5 | 0 |
| **core** | **92** | **43** | **34** | **15** | **0** |
| optional OL1–OL4 | 4 | 1 | 3 | 0 | 0 |
| collaborator CR3–CR7 | 5 | 0 | 2 | 2 | 1 |

Waves (core): 0: 27, 1: 16, 2: 17, 3: 7, 4: 4, 5: 3, 6: 2, 7: 2, 8: 4, 9: 4, 10: 3, 11: 3.
Critical path: M3 → M5 → M6 → OE2 → D3b → CO1 → PA1 → PA3 → TH1 → TH3 → HL2 → HL6 (PA1 closes
after the statements whose side conditions it collects, review S10); the second path is
M11a → M11c → M14 → TH3. Against the sizing estimate (115–125 with about a third random-matrix
theory): 92 core + 5 collaborator items that expand to the
spec's roughly 30; the program side is smaller than sized (about 45 instead of 53) because the
worklist, `DistSpec`'s pieces and the sampler are reused and the sphere sampler disappears.

## 6. Placement and shared machinery (rule 10)

### 6.1 Files

| file | declarations | why there |
|---|---|---|
| `Matrix/QRIteration/InverseIteration.lean` (new) | M1a, M1b, M2, M3 | inverse iteration estimates and the six-point net (radii as parameters), next to `Dichotomy`, `Strategy` |
| `Matrix/QRIteration/EigenvectorWeights.lean` | M8, M9 | weights |
| `Matrix/QRIteration/StableStepForward.lean` | M7 | forward error of chains |
| `Matrix/Perturbation/EigenvalueBackward.lean` | M10 | eigenvector perturbation (the proof is already there) |
| `Matrix/Perturbation/EigenvalueMatching.lean` (new) | M11a–c, M14 | eigenvalue matchings; no file named after the theorem |
| `Matrix/Spectral/Diagonalizable.lean` | M12, M13 | the diagonalization class |
| `Matrix/FinitePrecision/GivensRounded.lean` | M15 | rounded rotations |
| `Matrix/FinitePrecision/OpsSampling.lean` | GP2 | rounding of sampled words |
| `Eigensolvers/HessenbergReduction.lean` (new) | HR1–HR3 | a general rounded program (consumers: SmallEig, any dense eigensolver); the merged exact `hessenbergReduction` (`Matrix/Factorizations/Hessenberg.lean:239`) is top-down, fixes $\mathbf{e}_1$ and is not a program, so any exact bottom-up statement goes next to it (review S11) |
| `RandomMatrix/Shattering/GinibreClass.lean` (new) | RM1–RM4, RMn, RM9, the instances `boundsGinibreGap_ginibreGapTail`, `boundsGinibreCondition_ginibreConditionTail` | the solver-facing records; the tails that discharge them are in `RandomMatrix/Shattering/` (design note `RandomMatrix-Shattering.md`) |
| `RandomMatrix/Gaussian/Complex.lean`, `…/LeastSingularValue.lean`, `…/Gaussian/Tape.lean` | RM6, RM7, RM8 | Gaussian facts |
| `Eigensolvers/SmallEig/` (new folder): `Draws`, `Perturb`, `OneEigMath`, `RandomHessenberg`, `DistSpec`, `OneEig`, `Decouple`, `Decoupler`, `Leaf`, `Core`, `Program`, `Parameters`, `Precision`, `Theorems`, `Certification` | GD1 … TH6, M4a–c, M5, M6, M17, RM5 | the algorithm |
| `Eigensolvers/ShiftedQR/Rounded*.lean` (merged) | RF1–RF7 | the refactor |
| `Eigensolvers/ShiftedQR/RoundedSmallEig.lean`, `RoundedSmallEigCertification.lean` (new) | HL1–HL7 | the linked headline |
| `Ops/Tape.lean`, `Ops/Logic/Probabilistic.lean` | OL1–OL4 (optional) | the general rule |

Placement flags: M3 is a statement about points of $\mathbb{C}$ only (a P9 review warning); its
home is a `ForMathlib` file named after its Mathlib target if the reviewer prefers. `docs/references.bib`
gains `BanksGarzaVargasSrivastava2025` (Part III, SIMAX 46(2), 2025; `…2022` is Part II's key), `BhatiaElsnerKrause1990`, and the spec's sources if RM3
cites them. No Mathlib deviation is introduced (§2.8's predicates are hypotheses, not parallel
notions).

### 6.2 Vocabulary rows (review S12)

| object | meaning | Mathlib bridge |
|---|---|---|
| `PolyLogTail` | record $(C, a, b, c)$ of a tail $C n^a\tau^b K^c$; `PolyLogTail.normalize` | none (data) |
| `PolyLogTail.BoundsGinibreGap c`, `PolyLogTail.BoundsGinibreCondition c` | the collaborator's weak-form bodies as hypotheses | `HasLaw … complexGaussianMatrix`; RM9 to the spec's statements |
| `RandomSmallEigContract law β φ kmax T S qs SE I` | a randomized routine's forward contract on orders $\le k_{\max}$, norms $\le \Sigma$ | `PWrites`; bridge from `IsRandomSmallEig` |
| `TerminatingSmallEig T qs SE I`, `SmallEigCaps T qs` | all-tape totality; valid cap words | `Writes .total` |
| `RandomLeafRoutineContract`, `BackwardLeafRoutineContract`, `TerminatingLeafRoutine` | the merged leaf contracts with bounds and a parameter view | bridges from the merged contracts through `liftLeaf` |
| `SmallEigInput`, `SmallEigSpectrum` | the memory of the input; the spectrum of a nearby matrix | as `ShQRInput`, `ShQRSpectrum` |

### 6.3 Shared machinery

| repeated argument | handled by | status |
|---|---|---|
| a randomized routine in a merged program | the routine parameter `SE : Stmt` + `RandomSmallEigContract` (RF1–RF4) | new |
| merged name kept, body generalized | wrapper frame + bridge (one lemma per program, `PWrites.in_frame`) | new pattern, RF2a/RF3 |
| union bound over calls and rounds | `PWrites.seq`, `.whileFuel` | merged |
| a call whose bad event is a window | `PWrites.of_window` with a **closed** class set (M12) | merged + M12 |
| class through perturbations | `exists_pseudoConditionNumber_le_and_le_norm_sub` (one doubling per level, §2.7) | merged |
| rounded unitary sweeps | `BackwardStep.loop_rel` with G1–G5 (HR2, M15, RH2) | merged |
| decisions from computed quantities | "computed within relative error" hypotheses (DS2, OE2 take $\hat\tau \in [0.9, 1.1]\tau$, never the program) | as Part II S1–S5 |
| abstract iterations | M5, M6 on sequences, as the merged S6 | new |
| scan with a rounded threshold | P11p's $(1+\boldsymbol{u})^2t \le (1-\boldsymbol{u})^2t_L$ (DC2) | merged lemma |
| parameter side conditions | one structure per parameter set (PA1, as `shqrParams_spec`) | pattern |
| static counts | `stmtWorkMono` + `kernel_rfl` (TH5, HL5) | merged |
| substituting an adaptive program for an operation | OL1–OL4 | optional |

## 7. Edge cases and junk values

Per statement, to be checked in the skeleton (the Part II lessons in brackets):

* **Orders.** $d = 0$: empty listing, `copyLeaf` writes nothing; $d = 1$: copy, no draw, failure
  $0$, no division by $\sqrt{d}$ or $d - 1$ (P15's $n = 1$ division); $d \le k_{\max}$ and the worklist
  at $k = 1$ needs $k \le n$ in `RandomDecouplingContract`, i.e. order $\ge 2$ for the decoupler.
  `hessenbergReduceLast` loops over `N - 2` columns: guard $N \ge 2$ (no truncated subtraction in a
  statement, V2). M1a/M1b on `Fin (n + 1)` (`Fin.last n`).
* **Division by zero.** Shifts equal to eigenvalues: Lean's inverse is $0$, so M1a/M1b, M2, DS2,
  DC2 take $s \ne d_i$ or $\operatorname{dist} \ge \eta_1 > 0$ explicitly [S5 `hd`]. A zero weight
  makes M1b's bound vacuous (its left side is $0$), but M2/DS2 use $w^{-1/(2m)}$: take $p > 0$ and
  state with powers, not `rpow` of $0$. $\gamma = 0$: excluded ($\gamma > 0$ from $\delta > 0$).
  $\Sigma = 0$: excluded by $0 < \delta \le \Sigma$; `smallEig_relative` needs $0 < S$, so
  $\mathbf{M} \ne 0$ [T3].
* **Signs of the tail constants** (review S1): $C \le 0$, $a < 0$, $c < 0$ are normalized away (RMn).
* **$\eta_2 \le 0.02\Sigma$** needs $\beta \le 0.8\Sigma$ (review S4; true at $\beta' = \omega/20$), a hypothesis of M4c.
* **Logs.** $\log_2$ throughout (P7); arguments $\ge 1$ by $\beta \le \Sigma$, $\varphi \le 1$; tails
  with $\log(\gamma/t)$, $\log t^{-1}$ need $t \le \gamma$, $t \le 1$ (RM5 chooses them so);
  T2-type bounds argued at $\ge 4$ [T2 scale invariance: $\Sigma^2/(\delta\Gamma)$, not
  $\Sigma/(\delta\Gamma)$].
* **Positivity** of every parameter and of $\boldsymbol{u}_{\mathsf{SmallEig}}$ (PA2), else the
  headline is vacuous through $0 \le \boldsymbol{u} \le \boldsymbol{u}_0$ [PAR1p]; caps $\ge 1$
  (a zero cap makes the decoupler's contract false) [P11p `F = 0`].
* **Words and orders** (review B1). The words depend on the order through $t_1, t_2$ and $\gamma/\sqrt d$;
  they are fixed at an outer bound $n_{\max}$ and valid at every order $\le n_{\max}$ (tails monotone
  in the order after normalization), and the scale $\gamma/\sqrt d$ is computed by the program.
* **Cap words** (review B5). `bindIdx` on a negative or too large word fails: termination is
  claimed under `SmallEigCaps T qs`, which PA2 discharges for the stored words.
* **Start of `OneEig`** (review B3). $s_0 = 0$ may be an eigenvalue (Lean's inverse is $0$ there);
  the start is a disk sample, covered by the $+1$ of $6t + 1$.
* **Quantifiers.** $k_{\max}$, $\Sigma$, $T$, `qs`, $\beta$, $\varphi$ fixed outside the `∀ d B` of
  the contract [C1: a parameter inside the quantifier made a contract false]; failure bounds
  $\ge 0$ wherever `PWrites.seq` needs them [E1 $\beta \ge 0$].
* **The random-matrix scope.** The spec's statements need $2\gamma \le \|\mathbf{M}\|$ (weak) or
  $\gamma < \|\mathbf{M}\|$ (Theorem B): no shift or a shift by $4\gamma$ (M13, RM4; review S3); their events are not measurable by
  contract: closed superset (M12); strict $t < |d_i - d_j|$ vs the class's $\Gamma \le$: the class
  event contains the spec's, so its complement is smaller. Normalization: $\gamma n^{-1/2}\mathbf{G}$
  with `complexGaussianMatrix` ($\mathbb{E}|g|^2 = 1$), matched by RM8's $(x+iy)/\sqrt2$.
* **Hessenberg.** Q4's lesson: forward error of Givens QR only for Hessenberg $\mathbf{H}$; every
  chain lemma (M7, DS2, DC2) takes `IsUpperHessenberg`; the reduction's output is Hessenberg by
  writing exact zeros (`clearBelowSubdiagonal` pattern), not by rounding [HR1].
* **Phase.** The computed $\widehat{\mathbf{R}}_{nn}$ is complex [G8']: moduli in `Tau` (merged
  `stepComptau`); $\mathbf{Q}\mathbf{e}_N = c\,\mathbf{g}/\|\mathbf{g}\|$ with $|c| = 1$ in M8/M15.
* **Precision forms.** $m\nu\boldsymbol{u} \le 1/4$ [G16], base $\|\mathbf{H}\| + |s|$ [D3.4],
  $(2+2C)^{-m}$ [G8]: all inside the merged lemmas the targets call.
* **Scan thresholds.** The decoupling scan certifies $|h| \le \omega$ only through $t_L$ with
  $(1+\boldsymbol{u})^2t \le (1-\boldsymbol{u})^2t_L$ [P11p].
* **Measurability.** `I.IsMeasurable` is a hypothesis (not `Mch.IsMeasurable`) [PROB-LOGIC review
  item 1]; the new program adds no kernel, so PL4's catalog meanings suffice and the joint
  realizability caveat of the merged §15.3 (a measurable `SmallEig` oracle) disappears.
* **Tape.** Streams share the position counter; every draw advances it; the window of a call is
  fresh because positions only increase (`run_follows`); `polar` and `SampleOp.draw` are
  tape-local, so `hloc` holds with the merged `win`.

## 8. Open decisions for the maintainer

* **D1 Precision model.** (a) One `StdModel u`, $\boldsymbol{u} \le \min(\boldsymbol{u}_{\mathrm{ShQR}},
  \boldsymbol{u}_{\mathsf{SmallEig}})$, bits $O(k^2\log^2 Y) = O(\log^4 Y)$ up to $(\log\log)^2$; (b) two
  precisions (§2.3). **Recommend (a)**; (b) later as its own stage if the bit count matters.
* **D2 Substitution mechanism.** (a) Routine parameter `SE : Stmt` with wrappers (RF1–RF7), no new
  Ops logic; (b) `Stmt.link` + the general rule OL1–OL4 and the merged chain restated over
  `TapeAdapted` (about 28 theorems' `hloc`). Both need the parameter operand (§2.1). **Recommend
  (a)**; OL1–OL4 are specified and optional: land them when a second adaptive routine must be
  substituted (rule 10: shared machinery when an argument repeats), not for this stage.
* **D3 The hypothesis.** (a) Keep `IsRandomSmallEig`; add `RandomSmallEigContract` (bounded,
  routine-level) with a bridge, so T1c is a corollary; (b) restate `IsRandomSmallEig` in place
  with $d \le k$ and $\|\mathbf{B}\| \le \Sigma$ (changes T1c's hypothesis, still a kernel).
  **Recommend (a).**
* **D4 Wave order.** (a) By dependency (§5), with RF1–RF3 and every program definition first and
  M11a/M11b started in wave 0 (review); refactor RF1–RF4, L1 and the L3 definitions in
  waves 0–2 (RF5–RF7 in 3–5), programs and their guarantees in 0–5, the standalone theorems (a), (b) in waves 6–8 (TH1 6, TH3 7), the link HL1–HL7 in 4–9;
  (b) SmallEig standalone first as its own milestone (M2 of the sizing), the refactor after.
  **Recommend (a)** with RF first inside wave 0–2: the refactor touches merged files that later
  waves import, and the inner worklist needs the bounded leaf contract (RF2a) anyway, so (b) does
  not avoid it.
* **D5 Names of the random-matrix predicates and the tail record.** (a) `PolyLogTail.BoundsGinibreGap`,
  `PolyLogTail.BoundsGinibreCondition`, `PolyLogTail` (law in the name, N9-style); (b) consume the
  collaborator's `exists_forall_…` statements directly (then $\boldsymbol{u}_0$ is not explicit).
  **Recommend (a)** with the record normalized once (RMn), so the headlines take `hA`, `hB` (and
  $0 < b$) only; names to be confirmed against naming.md.
* **D6 Cap dimension.** (a) thread `T` through the generalized programs (merged wrappers pass
  `0`), with $m$ among the caps ($m, t, m_2 \le T$, $q \le m$; review B4); (b) bound the caps by `F` of the decoupler interface only (inner worklist) and by a word
  elsewhere (no static count). **Recommend (a)**: TH5/HL5 need it.
* **D7 Algorithm variant.** (a) The paper's `RHess` at every node ($O(n^4)$; independent fresh
  randomness and a union bound); (b) sizing §6(c)1, one random Hessenberg form and one-step
  decoupling ($O(n^3)$), unproved. **Recommend (a)** (sizing §6(d): the $n^4$ is subdominant in
  Corollary 1.3, and $k$ is small in shifted QR).
* **D8 Ostrowski–Elsner constant.** $2n + 1$ (component argument) or Bhatia–Elsner–Krause's 4.
  **Recommend $2n+1$**; only its logarithm enters.

## 9. Risks

* **M11.** Mathlib searched (grep of the pinned Mathlib, review S5): no Rouché, no
  argument-principle zero count, no continuity of `Polynomial.roots`; `Topology/Algebra/Polynomial`
  has only coefficient bounds. Planned by compactness instead (M11a, M, same technique as M12),
  Hadamard (M11b) and the homotopy (M11c, L): L in total. It gates TH3 and HL2, so it starts in
  wave 0.
* **The collaborator's CR7** (gap) is XL with no checked elementary route (spec §4); the headline
  stays conditional until it lands. Nothing in this stage waits for it.
* **RF7**: if the wrapper changes the static count, the certificate's numerals change (the only
  merged statement-level change). Measured at the RF7 step.
* **RF4** touches the largest merged files (`RoundedRegularize*`, `RoundedDecouple*`, up to 981
  lines): the With versions must stay under the file-length rule (F10), possibly by moving the
  generic proofs to new files and keeping the wrappers.
* **Constants.** `uSmallEig` assembles the corrected constants of six subroutines; PA3 is L only
  if defined once and bounded once (as `uShQR`).
* **PL4 coverage.** `IsSample`'s operation must be in the measurable catalog (`ScalarMeasurable`)
  for the joint realizability of the hypotheses; checked at TH6.

## 10. Checks run

Design only: no Lean file was added or changed, so `lake build`, `check_rules --files` and
`stage_check.sh` were not run for this note. The key statements were **elaborated** (§13).
`docs/design/` notes are not inputs of the rules checker.

## 11. Material

Part III LaTeX (`src3/*.tex`), Part II LaTeX (`src2`), the Part II design note, the merged Lean
(`Eigensolvers/ShiftedQR/Rounded*.lean`, `Ops/Link.lean`, `Ops/Tape.lean`, `Ops/Law.lean`,
`Ops/Cert.lean`, `Ops/Logic/Probabilistic*.lean`, `Ops/Catalog/Sampling.lean`,
`Matrix/FinitePrecision/OpsSampling.lean`, `RandomMatrix/Gaussian/*`),
[Ops-Probabilistic-Specs](Ops-Probabilistic-Specs.md), [Ops-BackwardError](Ops-BackwardError.md);
harness reports `Sizing-BGS-PartIII.md`, `Spec-RandomMatrix-GinibreGapKappaV.md` (the collaborator
spec), `Review-Fable-PartIII-Errata.md`, `Errata-BGS-ShiftedQR.md`. Sources: BGKS 2020/2023
(Prop D.5), BKMS 2021 (Thm 1.5), Bhatia–Elsner–Krause 1990, Higham 2002 (Ch. 19).

## 12. Changes after review (Fable, `Review-Fable-SMALLEIG-Design.md`)

Verdict "revise, then approve for skeleton". Every blocker and should-fix is applied in this
note and in `~/nlalib-harness/pilot/smalleig-targets.json`.

| item | finding | fix |
|---|---|---|
| B1 | the words depend on the order ($\gamma/\sqrt N$, $t_1$, $t_2$), but TH3's contract fixes one `qs` for every $d \le k_{\max}$ | TH1, PA1, PA3, GP3, RM5 at an outer bound $n_{\max}$; the program computes $\gamma' = \mathrm{fl}(\gamma/\sqrt d)$ (GP1), a valid $\gamma$ of the spec's statements; TH3 at $n_{\max} = k_{\max}$ (§1.1, §1.2) |
| B2 | the offset of the SmallEig words in `P` is not a literal ($10 + 2\lvert\mathrm{excNet}\,\varepsilon\rvert$) | the words are the tail of `P`, viewed as `P[np - nq]`; With theorems on `roundedDecoupleParams … ++ qs`, merged = `qs = []` (§2.1, RF3, RF4a–d) |
| B3 | `OneEig` started at $s_0 = 0$, so OE2 was false | start at a polar disk sample of radius $\eta_2$; M5's start bound adjusted (OE1, OE2, M5, §2.5) |
| B4 | `2^q` is not an `IExp`, and with only $q \le T$ TH5/HL5 were false | $m$ a cap word $\le T$, $q$ read with bound $m$; `distSpec : [N, m, q]` (DS1, PA2, D3a, §2.1, §2.5) |
| B5 | SE2 "for every `qs`" was false (`bindIdx` fails on junk words) | `SmallEigCaps T qs` hypothesis; no literal above the order, so `IsExactNatLit (n + 1)` stays; HL3 needs `hin` only (SE2, HL3, §2.2) |
| S1 | signs of the tail constants; PA4's quantifiers | normalized record RMn; all parameters from it; tail records quantified before $\exists c$ (RMn, RM5, PA4, HL4, §2.8) |
| S2 | GP3 spent all of $\varphi$ | budget table $\varphi/4$ × 4 (§1.1); RM5, RM6 with a free budget |
| S3 | RM4's $K$ wrong for the shift used | no shift if $2\gamma \le \lVert M\rVert$, else shift by $4\gamma$; $K = (\lVert M\rVert + 4\gamma)/\gamma$ |
| S4 | $\eta_2 \le 0.02\Sigma$ false at $\beta = \Sigma$ | M4c assumes $\beta \le 0.8\Sigma$ |
| S5 | Mathlib not searched for M11; no root continuity, no Rouché | M11 split: M11a compactness (M), M11b Elsner (S), M11c homotopy (L); started in wave 0 (§9) |
| S6 | M5, M6 (algorithm constants) in a topic file importing a stage file | M5, M6 moved to `Eigensolvers/SmallEig/OneEigMath.lean`; M3 general with radii as parameters |
| S7 | missing leaf bridge, plug lemma, discharged corollary | RF8, RM9 (with `example`s), HL8 |
| S8 | GP1, HR1 work in place but the footprint is the output | SE1 copies the block to scratch first |
| S9 | RM3's constant 8 for Theorem B not derivable | 18 |
| S10 | RF4 too large; PA1 too early; M7, M10 undersized; TH5's dependency | RF4a–d (L each); PA1 after CO1, D3b, GP3; M7, M10 → L; TH5 depends on RF2a |
| S11 | merged exact `hessenbergReduction` not mentioned | cited (§6.1, HR1) |
| S12 | no vocabulary rows | §6.2 |
| nits | `I.callS` in OL1; M8/M9 unit vector; HL1's word list; TH3's SE2 dependency | `I.call`; unit $x$, $x = g/\lVert g\rVert$; `smallEigForwardParams`; dropped |
| decisions | D1–D8 as recommended; D4 programs and M11 first; D5 normalized record; D6 $m$ among the caps | §8 |

Counts after review: 92 core (was 83): L1 21, L2 41, L3 10, L4 20; S 43, M 34, L 15; twelve
waves (0–11). The collaborator spec was re-read: L3 is aligned with its §3 statements (§2.8).

## 13. Elaboration (scratch, not in the repo)

File `/home/ubuntu/.claude/jobs/59127b8e/tmp/smalleig-elab/SmallEigStatements.lean` (seed of the
skeleton), checked with `lake env lean` against the built `NLAlib` of @6f049b04: **no errors**;
new definitions are stubs, proofs `sorry` (except RM9, proved by repackaging). Elaborated:
`PolyLogTail`, `PolyLogTail.normalize`, `PolyLogTail.BoundsGinibreGap`, `PolyLogTail.BoundsGinibreCondition`
(RM1, RM2, the spec's weak-form bodies verbatim), `PolyLogTail.BoundsGinibreGap.normalize` (RMn),
`exists_complexGaussianGapTail_iff` (RM9: the spec's `exists_forall_…` statement, verbatim, ↔ the
record form; proved), the preferred Theorem A and RM3's statement, M12, M11c;
`RandomSmallEigContract`, `TerminatingSmallEig`, `RandomLeafRoutineContract`, `smallEigKernel`
(an `ops%` program), `IsRandomSmallEig.randomSmallEigContract`, `seLeaf` (an `ops%`
program with the view `P[np - 12]`), `RandomSmallEigContract.randomLeafRoutineContract`;
signatures of `solveRoundedWith`, `regularizeWith`, `roundedDecoupleWith`, `roundedShQRWith`;
headline (a) `smallEig_measureReal_not_spectrum_le`, headline (b)
`smallEigProg_randomSmallEigContract`, `smallEigProg_terminates`, and headline (c)
`roundedShQRSmallEig_measureReal_not_spectrum_le` with `shqrSmallEigParams`, `shqrSmallEigDims`,
`uShQRSmallEig`, `ShQRSmallEigInput`.

Fixes from elaboration:

* **`nq` is a numeral, not a variable.** `opsIdx` (`Ops/Logic/Builder.lean:82–101`) accepts
  numerals, scoped names and arithmetic only, so `P[np - nq]` is written with the fixed word count
  (12 in the scratch). PA1 gains `length_smallEigParams`, and RF8's bridge takes
  `qs.length = nq₀` (§2.1, RF8, PA1).
* **`TerminatingSmallEig` gets an order bound `kmax`.** With every order inside the quantifier,
  SE2 needed `∀ d, IsExactNatLit id Mch d` (literals of every size exact), which would make the
  termination theorem nearly vacuous for a rounded machine. Now `d ≤ kmax` and SE2 takes
  `IsExactNatLit id Mch kmax` (RF1, SE2).
* No vacuity found in (a)–(c): the tail predicates are false only for $C < 0$ at order $1$, which
  RMn's normalization excludes; at order $0$ their range ($2\gamma \le \|\mathbf{M}\| = 0$) is empty.

## 14. As built: program changes after the review and the current numbers

The program and statements changed in five places while the targets were proved; the review of
the paper's errata (`Review-Fable-PartIII-Errata.md`) is unchanged by them.

* **Zero-fill.** `smallEigProg` first zeroes its output `Ev` (`NLAlib.Ops.fillMap`), so that the
  output is stored on every tape, also when the core stops early. Termination (SE2) then states
  that the output is stored, not only that the run ends.
* **The threshold word in scratch.** The block is copied to scratch (review S8), and the threshold
  word read from `Q` is copied to a scratch word `Th` as well, before the perturbation; the core
  reads it there (`smallEigCoreInput_of_scratch`).
* **`12 ≤ qs.length`.** The termination statements (SE2, `smallEigCore_terminates`,
  `smallEigDecoupler_terminatingDecouplerRoutine`) take at least twelve words, not exactly
  twelve; the contract statements keep the words `smallEigParams …` (PA1, `length = 12`).
* **The stored-output leaf contract.** The leaf contracts keep their output stored, and the
  worklist keeps output words that are stored before it runs
  (`NLAlib.ShiftedQR.solveRoundedWith_terminates_stored`, used by
  `NLAlib.SmallEig.smallEigCore_terminates_stored`). This is what the zero-fill needs.
  (Superseded by SCHUR: the output is the block and its accumulator, so `identityLeaf` stores
  $\mathbf{U}_b = \mathbf{I}$ first in place of the zero-fill, and the `_stored` variants are
  removed.)
* **CO1's literal bound.** CO1 (`smallEigCore_pwrites`) and D3b
  (`smallEigDecoupler_randomDecouplingRoutineContract_of_le`) take exact natural literals up to the
  block order $n + 1$ only, not up to $n_{\max} + 1$.

Current constants of the static counts (all kernel-checked by `kernel_rfl`), after SCHUR
(Schur-mode programs; [Eigensolvers-DenseSchur](Eigensolvers-DenseSchur.md) §15):

| statement | constant (after SCHUR) | at the end of SMALLEIG |
|---|---|---|
| RF7, `stmtWorkMono_shqrProgram` (merged certificate) | removed with the oracle program | $196218\,b_0^3b_1^3b_2b_3$ (196017 on `main` before) |
| TH5, `smallEig_work_le` (instrumented, explicit) | $80390\,(n+1)^4(T+1)^2$ | $\exists c$, witness $3473$, uninstrumented |
| HL5, `roundedShQRSmallEig_work_le` (instrumented, explicit, log dims $F(k+1+n_p)$, $k(n+1)$) | $369224\,(n+1)^3(k+1)^4(n_p+1)(F+1)(T+1)^2$ | $\exists c$, witness $15895$, uninstrumented |
| TH6, `smallEigWork` (certificate, instrumented) | $517058\,(n+1)^4(T+1)^2$ | $373483$ |
| HL6, `shqrSmallEigWork` (certificate, instrumented) | $967736\,(n+1)^3(k+1)^4(n_p+1)(F+1)(T+1)^2$ | $675307$ |

The certificates' constants are larger than TH5 and HL5 because they also count the frame of the
program. HL5's exponent of $k + 1$ is $4$, not the $5$ of the target row.

The random-matrix tails (RM1, RM2) are proved (`NLAlib.boundsGinibreGap_ginibreGapTail`,
`NLAlib.boundsGinibreCondition_ginibreConditionTail` at the records $(10000e, 5, 1/2, 2)$ and $(128e, 3, 2, 2)$), so
every headline has an `_unconditional` form without the tail hypotheses.

### 14.1 Changes after the stage review (Fable, `Review-Fable-SMALLEIG-Stage.md`)

* **B-1.** The tail record and the two predicates live in
  `RandomMatrix/Shattering/GinibreClass.lean` with the class event and the tail inversion, named
  `PolyLogTail.BoundsGinibreGap` and `PolyLogTail.BoundsGinibreCondition` (they no longer end in
  `Tail`); the proved records are named `ginibreGapTail` and `ginibreConditionTail` and are
  registered in `docs/constants.toml`; every `_unconditional` corollary states them by name.
* **B-2.** `ShiftedQR.TerminatingLeaf` keeps its merged meaning (no claim on the output), so the
  merged `solveRounded_terminates` keeps its statement. (Removed by SCHUR: `TerminatingLeaf` and
  `solveRounded` are deleted; the worklist's termination is `solveRoundedWith_terminates`, and
  its completion with no rounding model `solveRoundedWith_completes`.) The worklist's termination lemmas take a
  leaf routine that keeps its output stored under the same condition as the output words
  (`TerminatingLeafRoutineIf rd`): at `rd = False` a merged leaf, at any `rd` a leaf that keeps its
  output (the small-eigenvalue program's leaves).
* **Scaffolding removed**: the preferred-form predicates, their implications, the asymptotic
  `exists_…_iff` forms with their `example`s (RM3, RM9) and the conditional headline HL8.
* **S-3.** The term `uSmallEigCore` of the precision threshold was never consumed (the backward
  error of the core is within $\delta/8$ by the `Decouple` term) and is removed; every headline
  gets a larger admissible $\boldsymbol{u}$.
* **S-4.** `smallEigVectorRadius` is the radius `RHess` uses, $\sqrt2\,(3\sqrt{n_{\max}} +
  \sqrt{2\log(4/\varphi_D)})$, and `smallEigWeight` is written as the bound of `rhess_pwrites`,
  $s^2/(64R^2(2B_c)^2)$ (the same value as before).
* **S-7.** `roundedDecoupleLoop_terminates` is restored, as a corollary of the `With` form.

