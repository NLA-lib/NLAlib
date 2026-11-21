# A dense Schur solver on the operation core (SCHUR)

Stage SCHUR builds an end-to-end dense eigensolver whose output is a Schur form: for any complex
$\mathbf{A}$ of order $n + 1$ it computes words $\widehat{\mathbf{U}}$, $\widehat{\mathbf{T}}$
with $\widehat{\mathbf{T}}$ exactly upper triangular. It is built from the finite-precision shifted
QR of [BanksGarzaVargasSrivastava2022] (Part II,
[Eigensolvers-ShiftedQR-FiniteOps](Eigensolvers-ShiftedQR-FiniteOps.md), the template of this
note) and the `SmallEig` program of [BanksGarzaVargasSrivastava2025] (Part III,
[Eigensolvers-SmallEig-PartIII](Eigensolvers-SmallEig-PartIII.md)). The papers compute
eigenvalues only. Part I's introduction (`src1/intro.tex:176`) says, without proof, that the
full Schur form "can be obtained directly from our results and will have the same asymptotic
running time". This stage proves it.

**Status: built.** Every statement below is proved, with no `sorry`. The note was written as a
design and revised after the design review and the maintainer's decisions (§11, §14). It now
records the stage as built: the final statements (§1, §2), the programs (§3), the constants and
certificate numerals (§6, §15), the statement fixes found while proving (§16) and the
strengthenings made after the stage review (§17). Where the design and the build differ, the
section says so. Nothing in the checks, CI, the lakefile, the allowlists, `*Targets.lean` or
`docs/targets.*` changed in this stage.

Decisions taken before the design: S1 full Schur form; S2 accuracy in computed form, with the
exact-unitary form as a corollary; S3 the algorithm computes $\|\mathbf{A}\|_{\mathsf F}$; S4
full-mode generalizations of the merged programs. S4 was later sharpened by the maintainer to
"Schur is the program" (§14.6): the Schur-mode programs replace the eigenvalue-only programs in
place. The modularity requirement (§2) is met: every pipeline stage is a routine parameter with
its own contract, and one generic composition theorem covers any components that meet them.

## 0. Summary

* **Headline (§1).** For every $\mathbf{A} \in \mathbb{C}^{(n+1)\times(n+1)}$, $0 < \delta \le 1$
  and $0 < \varphi \le 1$, at a unit roundoff $\boldsymbol{u} \le \boldsymbol{u}_0(n,\delta,\varphi)$
  with $\log_2(1/\boldsymbol{u}_0) \le c_1L^4(\log_2 L + 1)^2 + c_2$,
  $L = \log_2(4(n+1)/(\delta\varphi))$, the program `denseSchur` stores, except with probability
  at most $\varphi$, the flag $0$ and words $\widehat{\mathbf{U}}$, $\widehat{\mathbf{T}}$ with
  $\widehat{\mathbf{T}}$ exactly upper triangular,
  $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2
  \le \delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
  \mathbf{I}\|_2 \le 58R\boldsymbol{u} \le \delta$, $R$ an explicit static bound on the rotations
  (and rotation-equivalents) accumulated on $\widehat{\mathbf{U}}$. **On every tape** the run
  terminates and the orthogonality bound holds. There is no hypothesis on $\mathbf{A}$; exact
  naturals are needed only up to $n + 1$. Static count
  $384547(n+1)^3(k+1)^4(n_r+n_q+1)(F+1)(T+1)^2 \le C(n+1)^3L^{15}$.
* **Modular (§2).** Four pipeline stages (norm estimate, regularizer, Hessenberg reducer, Schur
  core), each a routine parameter with a contract, and one generic composition theorem (backward
  errors add, accumulator errors compose as $(1 + a)(1 + b) - 1$, failures and static counts add).
  The core's small-block Schur solver (the leaf) is a routine parameter too, with its own contract.
* **Schur is the program (§3, §14.6).** The merged finite-precision shifted QR chain and Part III's
  programs record every committed rotation in a slotted Givens log; the worklist replays the logs on
  the coupling blocks and on $\widehat{\mathbf{U}}$, writes exact zeros at the cuts and multiplies by
  the leaves' accumulators. The eigenvalue-only programs are deleted; every merged eigenvalue
  theorem is a corollary of the Schur theorem of its program and keeps its name.
* **Why the merged chain changes (§4.1).** A Schur form needs the backward error with the unitary
  *named*; the only probability bounds for it are inside the merged chain. So every backward
  statement of the chain now names its unitary (`givensLog` of the log).
* **Constants that moved (§1, §15, §16).** $\delta' = \delta/(16\sqrt{n+1})$ (design:
  $\delta/(32\sqrt{n+1})$); norm bounds $4$ (regularizer) and $8$ (core) after normalization by an
  estimate with constants $(1/2, 2)$; a nine-term precision threshold; the power of $k + 1$ in the
  static count is $4$ (design: $5$); the polylog exponent is $p = 15$ (design: about $12$).

## 1. The headlines, in Lean

Notation as in Part II/III: order $n + 1$, `S` for $\Sigma$. The two Ginibre tails are proved
(`ginibreGapTail`, `ginibreConditionTail`), so no tail hypothesis appears.

```lean
/-- The output: flag `0`, `T̂` upper triangular, the computed-form bounds. -/
def SchurOutput {n : ℕ} (a uo f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eA eU : ℝ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix uo U μ'.store ∧ T.IsUpperTriangular ∧
    specNorm (A - U * T * Uᴴ) ≤ eA * specNorm A ∧ specNorm (Uᴴ * U - 1) ≤ eU

/-- HD1: the dense Schur theorem. Result: dense-schur-backward-error -/
theorem denseSchur_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseSchur n δ φ)
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ} (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A δ (58 * denseSchurRotations n δ φ * u)) μ} ≤ φ
```

The program is `denseSchur sG = denseSchurWith sG (smallEigProg sG)`, and `denseSchurWith sG L`
is `schurPipelineWith frobNormStage (ginibrePerturb sG) hessenbergReduceQ (roundedShQRSchurWith L)`
(interface `[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`; `Algorithm: dense-schur`).

Companions, all in the `NLAlib.Schur` namespace:

* **HD1'** `denseSchurWith_measureReal_not_schur_le` (Result: dense-schur-small-block-oracle):
  the same theorem for any leaf `L` meeting `RandomSchurLeafContract law εL βL φL
  (min k (n + 1)) 32 qs T L I` with twelve words, $0 \le \varepsilon_L \le (1 +
  24\boldsymbol{u})^{R_L} - 1$, $0 \le \beta_L \le$ `denseSchurLeafAccuracy`, $0 \le \varphi_L
  \le$ `denseSchurLeafFailure`, and $\boldsymbol{u} \le$ `uDenseSchurWith n δ φ np RL`; its
  rotation count is `denseSchurRotationsWith n δ φ np RL`. HD1 is its instance at the
  `SmallEig` leaf (`SmallEig.smallEigProg_randomSchurLeafContract`).
* **HD4** `denseSchur_terminates`: on every tape, for $0 < \delta \le 1$, any $\varphi$ and
  $\boldsymbol{u} \le \boldsymbol{u}_0$, the run is total, writes only $\mathbf{A}$,
  $\widehat{\mathbf{U}}$ and the flag, and stores $\widehat{\mathbf{U}}$ with
  $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}$
  (`SchurOrth`). The general form `denseSchur_writes_orth` needs only $400(n+1)^2\boldsymbol{u} \le 1$
  and gives $2\varepsilon + \varepsilon^2$, $\varepsilon = (1 + 27(n+1)^2\boldsymbol{u})(1 +
  24\boldsymbol{u})^{R_c} - 1$. Completion with no rounding model at all is `denseSchur_completes`.
* **PP3** corollaries: `denseSchur_measureReal_not_spectrum_le` (Result: dense-schur-eigenvalues),
  $\operatorname{diag}\widehat{\mathbf{T}}$ lists the spectrum of $\mathbf{A} + \mathbf{E}$,
  $\|\mathbf{E}\|_2 \le 2\delta\|\mathbf{A}\|_2$; `denseSchur_measureReal_not_exact_schur_le`
  (Result: dense-schur-exact-unitary), an exact unitary $\mathbf{V}$ with
  $\|\widehat{\mathbf{U}} - \mathbf{V}\|_2 \le 58R\boldsymbol{u}$ and $\mathbf{A} + \mathbf{E} =
  \mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H}$, $\|\mathbf{E}\|_2 \le 2\delta\|\mathbf{A}\|_2$.
  Both from `SchurOutput.exists_isEigenvalueListing` / `SchurOutput.exists_hasOrthonormalCols`
  ($e_U \le 1/8$, $\|\mathbf{E}\|_2 \le (e_A + 4e_U(1 + e_A))\|\mathbf{A}\|_2$) and
  `denseSchur_orth_le` ($\delta + 4\cdot58R\boldsymbol{u}(1 + \delta) \le 2\delta$).
* **HD5** `logb_inv_uDenseSchur_le`: $\exists c_1, c_2$, $\log_2(1/\boldsymbol{u}_0) \le
  c_1L^4(\log_2L + 1)^2 + c_2$ (the shift degree is $\Theta(L\log L)$).
* **HD6** `denseSchur_work_le`: the instrumented static count at `[n + 1, nr, nq, k, F, T]` and zero
  offsets is $\le 384547(n+1)^3(k+1)^4(n_r+n_q+1)(F+1)(T+1)^2$; **HD7**
  `denseSchur_work_le_polylog`: $\exists C, p$ with count $\le C(n+1)^3L^p$; the proof finds $p = 15$
  ($(k+1)^4 \le (KL^2)^4$, $F + 1 \le KL$, $(T+1)^2 \le (KL^3)^2$; the paper's is $2$ for the
  eigenvalues alone, with a run-time count over the deflation tree).
* **CT2** `denseSchurAlgorithm`, `denseSchur_algorithm_measureReal_not_accepts_le` (Result:
  dense-schur-certificate-accuracy): one counted run over `SmallEig.smallEigModel`, work and span
  `denseSchurWork` (§6), the Schur output with probability $\ge 1 - \varphi$.

**The parameters** depend on $(n, \delta, \varphi)$ only. $\delta' =$ `denseSchurDelta n δ`
$= \delta/(16\sqrt{n+1})$. The regularizer runs at the words `smallEigParams (n+1) 4 δ' (φ/2)`
with the proved tails (only $\gamma$ is read), into the class $(B, \Gamma) = (2/t_2, t_1/2)$
(`denseSchurB`, `denseSchurΓ`), $t_1$ = `smallEigGap`, $t_2$ = `smallEigCond` at the same
arguments. The core runs at the class $(2B, \Gamma/2)$, $\Sigma = 8$, error $\delta'$, failure
$\varphi/2$: $k$ = `denseSchurDegree` = `shqrDegree (4 * (2B))`, $F$ = `denseSchurCap` =
`shqrCap n (2B) (Γ/2) 8 δ'`, the threshold word `shqrDeflationThreshold`, the words
`shqrParams`. The leaf runs at `smallEigForwardParams k 32 β φL` with $\beta$ =
`shqrSmallEigAccuracy n (2B) (Γ/2) 8 δ'` and $\varphi_L$ = `shqrSmallEigFailure …`, cap $T$ =
`denseSchurLeafCap`. The norm estimate is used with the constants $(1/2, 2)$
(`frobNormStage_frobNormEstimateContract_half`).

**The precision threshold.** `uDenseSchur n δ φ` is the minimum of nine terms: `uDenseSchurWith`
(eight terms) at the `SmallEig` leaf, and the leaf's own `uSmallEigForward k 32 β φL`. The eight:

1. `uSmallEigReduce (n+1) 4 δ' (φ/2)` (the regularizer);
2. $\delta'/(3200(n+1)^2)$ (the reducer's backward error $50(n+1)^2\boldsymbol{u} \le \delta'/64$);
3. $t_1t_2/(28800(n+1)^3)$ (the reducer keeps the class: its error $50(n+1)^2\boldsymbol{u}(4 +
   \delta'/2) \le \Gamma/(16(n+1)B)$, the hypothesis of MC1);
4. `uShQR n k (2B) (Γ/2) 8 δ' (φ/2)` (the core);
5. $1/100$;
6. `uShQRSchurReplay n k np F RL (2B) (Γ/2) 8 δ'` (the replays, the leaf products and the leaf
   accumulators, §4.3);
7. $\delta/(4096(n+1)R)$ (the accumulator: it gives $58R\boldsymbol{u} \le \delta$ and
   $24R\boldsymbol{u} \le 1/8$);
8. $\delta/(64(n+1))$ (the scaling and the glue $8(n+1)\boldsymbol{u} \le 1/4$).

`uDenseSchur_pos` holds, so HD1 is not vacuous.

**$\varepsilon_U$ and $R$.** Each replayed rotation moves $\widehat{\mathbf{U}}$ by at most
$24\boldsymbol{u}\|\widehat{\mathbf{U}}\|$ from its exact product (the merged one-sided bound,
coefficients recomputed). The reducer contributes the relative error $27(n+1)^2\boldsymbol{u}$, the
core $(1 + 24\boldsymbol{u})^{R_c} - 1$, so $\varepsilon = (1 + 27(n+1)^2\boldsymbol{u})(1 +
24\boldsymbol{u})^{R_c} - 1 \le 1/16$ and $2\varepsilon + \varepsilon^2 \le 58R\boldsymbol{u}$,
$R = (n+1)^2 + R_c$ (`denseSchur_errors_le`). The counts:

* $R$ = `denseSchurRotationsWith n δ φ np RL` $= (n+1)^2 + R_c$;
* $R_c$ = `shqrSchurRotations n k np F RL` $= 2(n+1)\bigl(n_sw + 2k(k+2)\bigr) + (n+1)R_L$, with
  the log of $n_s = F(k + 1 + n_p)$ slots of $w = k(n+1)$ entries (`shqrSchurLogSize`), the leaf
  products $2k(k+2)$ per round, and $n + 1$ leaves;
* $R_L$ = `smallEigLeafRotations k T` $= k^2 + 2(k+1)\bigl((T+k)k + 6\bigr)$ for the `SmallEig` leaf.

## 2. Modularity: stages, contracts, the generic pipeline

Each pipeline stage is a routine parameter `… : Impl O Q` with a contract in the stage-neutral
style. The contracts state the stored accumulator through one relation, the tracked similarity
`IsTrackedUnitarySimilar εU εT U A U' A'` $:= \exists \mathbf{V},$
`IsPerturbedUnitarySimilarBy V A A' εT` $\wedge \|\mathbf{U}' - \mathbf{U}\mathbf{V}\|_2 \le
\varepsilon_U\|\mathbf{U}\|_2$ (the accumulator error is **relative**, so compositions telescope as
$(1 + a)(1 + b) - 1$). The computed-form conclusion is one lemma at the end (MW4).

### 2.1 The contracts (as built)

```lean
def FrobNormEstimateContract (c₁ c₂ : ℝ) (nmax : ℕ) (Nm : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a s : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsMatrix a A μ.store → μ.Live [a, s] → s.2 + 1 ≤ μ.store.len s.1 →
    a.1 ≠ s.1 →
    Writes .total I tape Nm.body (Env.frame [N] [a, s]) (Store.inBlock s.1 s.2 1)
      (fun μ' => ∃ x : ℝ, μ'.store.get s.1 s.2 = some x ∧ c₁ * frobNorm A ≤ x ∧
        x ≤ c₂ * frobNorm A) μ

def RandomRegularizerContract (law : ℕ → Measure ℝ) (δ φ : ℝ)
    (C : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop) (nmax : ℕ) (S : ℝ)
    (ps : List ℝ) (Reg : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), n + 1 ≤ nmax →
    specNorm A ≤ S →
    PWrites law I Reg.body (Env.frame [n + 1, ps.length] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix a A μ.store ∧ μ.store.readBlock q.1 q.2 ps.length = some ps ∧
        μ.Live [a, q] ∧
        Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
          (Store.inBlock q.1 q.2 ps.length))
      (fun μ' => ∃ E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a (A + E) μ'.store ∧ specNorm E ≤ δ ∧ C (A + E)) φ

def HessenbergReducerContract (εU εT : ℝ) (nmax : ℕ) (Red : Impl O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {N : ℕ} {a uo : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A U : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsSchurPair a uo U A μ.store → μ.Live [a, uo] →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N))) →
    Writes .total I tape Red.body (Env.frame [N] [a, uo, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => ∃ U' H : Matrix (Fin N) (Fin N) ℂ, HoldsSchurPair a uo U' H μ'.store ∧
        IsUpperHessenberg H ∧ IsTrackedUnitarySimilar εU (εT * specNorm A) U A U' H) μ

def RandomSchurCoreContract (law : ℕ → Measure ℝ) (εU εT φ : ℝ)
    (C' : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop) (k F T nmax : ℕ)
    (S : ℝ) (ps : List ℝ) (Core : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    n + 1 ≤ nmax → IsUpperHessenberg H → specNorm H ≤ S → C' H →
    PWrites law I Core.body (Env.frame [n + 1, ps.length, k, F, T] [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => HoldsSchurPair a uo U H μ.store ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.Live [a, p, uo, f] ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧
        Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1])
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store ∧ Tm.IsUpperTriangular ∧
        IsTrackedUnitarySimilar εU εT U H U' Tm) φ

def RandomSchurLeafContract (law : ℕ → Measure ℝ) (εU εT φ : ℝ) (kmax : ℕ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) (L : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p ub : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax → specNorm B ≤ Nmax →
    PWrites law I L.body (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [w, p, ub] ∧ ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 ∧
        Fp.Apart [w, p, ub] [2 * (d * d), ps.length, 2 * (d * d)])
      (fun μ' => ∃ Ub Tb : Matrix (Fin d) (Fin d) ℂ, HoldsSchurPair w ub Ub Tb μ'.store ∧
        Tb.IsUpperTriangular ∧ IsTrackedUnitarySimilar εU εT 1 B Ub Tb) φ
```

`TerminatingSchurCore εU k F T nmax ps Core I` is the all-tape companion of a core: total, and
$\|\mathbf{U}' - \mathbf{U}\mathbf{V}\|_2 \le \varepsilon_U\|\mathbf{U}\|_2$ for an exact unitary
$\mathbf{V}$ whatever the shifts. `CompletingNormEstimate`, `CompletingReducer`,
`CompletingSchurCore` are the completion contracts with no rounding model, used by the
certificate's `wp` (§2.3).

Changes against the design (each found while proving, §16): the order bound `nmax` is a
parameter of the norm estimate and the reducer (a rounded estimate has constants that depend on
the order); the norm estimate writes to another buffer (`a.1 ≠ s.1`); the core's dims are the
fixed `[n + 1, np, k, F, T]` (the design's opaque `cd` was not needed); the core needs room for
the flag; the reducer's and core's `specNorm U ≤ 2` became unnecessary with the relative
$\varepsilon_U$; the leaf contract is the Schur leaf (`Tb` upper triangular, tracked from
$(\mathbf{I}, \mathbf{B})$), and the eigenvalues are its diagonal.

The class is a predicate `C`/`C'`; the instance is `IsConditionedDiagonalizable B Γ` (MC1), with
`IsConditionedDiagonalizable.of_isPerturbedUnitarySimilarBy` as the transfer. The regularizer is
a stage, not part of the core, because its contract is the only place where the class is
produced; a core for structured input can be paired with a trivial regularizer.

### 2.2 The generic composition theorem (PP2)

`schurPipelineWith Nm Reg Red Core : [N, nr, nq, k, F, T] (A, P) → (A, U, Fl)` runs: $s$ := `Nm`
(into a scratch word); if $s$ is not positive (only $\mathbf{A} = 0$ under the standard model,
§7), $\widehat{\mathbf{U}} := \mathbf{I}$ and flag $0$; otherwise $\mathbf{A} :=
\mathrm{fl}(\mathbf{A}\cdot\mathrm{fl}(1/s))$, `Reg` on `P[0]`, $\widehat{\mathbf{U}} :=
\mathbf{I}$, `Red`, `Core` on `P[nr]` (the threshold word first), $\mathbf{A} :=
\mathrm{fl}(s\mathbf{A})$.

```lean
theorem schurPipelineWith_measureReal_not_schur_le [Has ScalarOp O] [Has IndexOp O]
    [Has CmpTst Q] [Has IdxTst Q] {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Impl O Q} {k F T : ℕ}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ (n + 1) Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT (n + 1) Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' k F T (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hu0 : 0 ≤ u) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT) (hεHT : εHT ≤ 1 / 8) (hεHU : 0 ≤ εHU)
    (hεCU : 0 ≤ εCU) (hεU : (1 + εHU) * (1 + εCU) - 1 ≤ 1 / 16) (hφR : 0 ≤ φR) (hφC : 0 ≤ φC)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (schurPipelineWith Nm Reg Red Core).body
      (Env.frame [n + 1, qR.length, qC.length, k, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A
        (2 * c₂ * √((n : ℝ) + 1) * (δR + 3 * εHT / c₁ + εCT +
          8 * ((1 + εHU) * (1 + εCU) - 1) / c₁) + 8 * (n + 1) * u)
        (2 * ((1 + εHU) * (1 + εCU) - 1) + ((1 + εHU) * (1 + εCU) - 1) ^ 2)) μ} ≤
      φR + φC
```

The proof is composition only: `PWrites.seq` adds the failures, the tracked relations of `Red` and
`Core` compose by `trans` (relative errors), and the class step from `Reg` to `Core` is `hCC'`,
which at the instance is MC1 with only the reducer's error (the regularizer's perturbation is
already inside `C (A + E)`). The scaling to and from $s \le c_2\|\mathbf{A}\|_{\mathsf F} \le
c_2\sqrt{n+1}\|\mathbf{A}\|_2$ gives the factor $2c_2\sqrt{n+1}$. The all-tape form is
`schurPipelineWith_terminates`, the completion with no rounding model `schurPipelineWith_completes`.

### 2.3 Work and the certificate (PP4, CT1)

`size_stmtCost_schurPipelineWith_le`: the instrumented static count of the pipeline at
`[N, nr, nq, k, F, T]` and zero offsets is at most the sum of the stages' instrumented counts, each
at the offsets the pipeline passes to it (zero, and $n_r$ for the core's parameter words), plus
$120(N+1)^2$ for the glue (scaling loops, identity, branch, frames). Counting at the offsets the
pipeline actually passes (not at zero offsets) was a fix found while proving (§16).

CT1 is `schurPipelineAlgorithm sU Nm Reg Red Core …`, built with `Algorithm.ofWp` over
`SmallEig.smallEigModel` from component data: the four programs, the storage discipline, the
pipeline's `wp` (termination and frame, with no rounding model), and bounds $W_\bullet$ on the
stages' instrumented counts. Its work and span are `schurPipelineWork WNm WReg WRed WCore d` $=
W_{Nm} + W_{Reg} + W_{Red} + W_{Core} + 128(N+1)^2$, $N$ = `d 0 + 1`, so a swapped component
swaps its cost term. The every-tape claim (`good`) is the frame; the Schur form is the `Accepts`
postcondition. CT2 is the instance (§6).

### 2.4 Which programs meet which contract

| contract | this stage | later candidates |
|---|---|---|
| norm estimate | `frobNormStage` (`RoundedScalarBlas.nrm2` on the $2N^2$ words): $c_{1,2} = 1 \mp (2N_{\max}^2 + 2)\boldsymbol{u}$, used at $(1/2, 2)$ | any two-sided estimate, e.g. $\max_{ij}\lvert a_{ij}\rvert$ |
| regularizer | `ginibrePerturb` (`ginibrePerturb_randomRegularizerContract`: error $\delta/2$, failure $3\varphi/4$, class $(2/t_2, t_1/2)$) | real Ginibre, sparse perturbations, the trivial one on Hermitian input |
| reducer | `hessenbergReduceQ` (`hessenbergReduceQ_hessenbergReducerContract`: $(\varepsilon_U, \varepsilon_T) = (27N_{\max}^2\boldsymbol{u}, 50N_{\max}^2\boldsymbol{u})$ under $200N_{\max}^2\boldsymbol{u} \le 1$) | Householder reduction, blocked Householder |
| Schur core | `roundedShQRSchurWith L` (`roundedShQRSchurWith_randomSchurCoreContract`); `roundedShQRSchur` at the `SmallEig` leaf | other shifting strategies, spectral bisection with Schur vectors, Hermitian Jacobi |
| leaf | `smallEigProg` (`smallEigProg_randomSchurLeafContract`); `identityLeaf` for $d \le 1$ (`identityLeaf_randomSchurLeafContract`) | a dense $O(k^3)$ QR, any exact small solver |

## 3. The programs

Buffers are word pairs in column-major order (`HoldsMatrix`). $N = n + 1$.

| step | program | buffers | notes |
|---|---|---|---|
| norm | `frobNormStage [N] (A) → (S)` | $S$: 1 scratch word | `RoundedScalarBlas.nrm2` |
| scale | loop of `ScalarOp.mul` by $\mathrm{fl}(1/s)$ | in place | exact zeros stay zero |
| regularize | `ginibrePerturb sG [N, nr] (A, P[0]) → (A)` | scratch | merged, word 0 = $\gamma$ |
| identity | `PairMatrix.identity [N] (U)` | | |
| reduce | `hessenbergReduceQ [N] (A, U) → (A, U)` | scoped log of $N$ slots | `hessenbergReduceLast` with a log, then replay on $\widehat{\mathbf{U}}$'s columns |
| core | `roundedShQRSchurWith L [N, nq, k, F, T] (A, P[nr], U) → (A, U, Fl)` | §3.2 | Part II in Schur mode |
| unscale | loop of `ScalarOp.mul` by $s$ | in place | |

### 3.1 The Givens log layer

A reusable layer in `Matrix/FinitePrecision` (the O7 moves put `HoldsMatrix` in `StoredMatrix` and
the rotation programs in `GivensCoefficients`, `GivensRotation`, `GivensPrograms`):

* **Entries** `GivensEntry = ℕ × ℂ × ℂ`: the plane $r$ and the two **inputs** $(p, q)$ of
  `coefficients`. `givensAt n (r, p, q)` is the exact rotation (the identity if $r + 1 \ge n$,
  `givensAt_zero` for the padding), `givensLog n L` the product, so that conjugating by the entries
  in order is $\mathbf{Z} \mapsto \mathbf{V}^{\mathsf H}\mathbf{Z}\mathbf{V}$ (`hasOrthonormalCols_givensLog`,
  `givensLog_append`).
* **Storage** `HoldsSlottedLog lg ns w L P`: $n_s$ slots of $1 + 5w$ words, a valid word, then $w$
  self-describing entries; `L` the closed slots (`none` rejected, `some es` accepted), `P` the
  pending entries of the open slot; `slotEntries` the accepted entries in order. No count word: the
  layout is static, the plane word is an exact natural $\le n$, the validity test is `isPos`.
* **Programs** `slottedLogOpen` (zero-fill), `slottedLogWrite [w, j, i, r] (Pw, Qw) → (Lg)`,
  `slottedLogValidate`; trials write their own slot and acceptance validates it (no trial buffer, no
  copy).
* **Replay** `givensReplayRows`/`givensReplayColumns`: the valid slots in order, plane by
  `bindIdx`, rotation by `rotateRowsOn`/`rotateColumnsOn` on a range. MG4
  (`givensReplayRows_specNorm_sub_le`, `givensReplayColumns_specNorm_sub_le`): each replayed rotation
  moves its operand by $\le 24\boldsymbol{u}\|\cdot\|$ from the exact product, on every tape.
* **Products** `matMulOn` (strided, the left factor optionally conjugate-transposed):
  `specNorm_matMulWord_sub_le`, error $8(p+1)\boldsymbol{u}\|\mathbf{X}\|\|\mathbf{Y}\|$ (design:
  $(2d+4)\boldsymbol{u}$ Frobenius terms).

The design's sink abstraction (`IsGivensSink`, `skipSink`, `slotSink`) was dropped with §14.6:
there is one program per algorithm, and it always records.

### 3.2 The worklist in Schur mode

`solveRoundedWith D L : [N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)` is the merged worklist
rewritten in place. After a successful decoupler call (which fills a scoped log of $n_s$ slots of
$w$ entries) it replays the log on the right coupling (rows), the top coupling (columns) and
$\widehat{\mathbf{U}}$ (columns), and writes the **exact zero** `lit 0` at the cut entry. After a
leaf (on the tail twelve words, `leafOnTailWords`) it multiplies the couplings and
$\widehat{\mathbf{U}}$ by the leaf's accumulator $\mathbf{U}_b$ (`matMulOn`, under $d \le k$). The
invariant: the tracked relation from $(\mathbf{U}_0, \mathbf{H}_0)$, $\mathbf{A}$ block upper
triangular with exact zero words below, active blocks Hessenberg, done blocks upper triangular;
hence the final $\widehat{\mathbf{T}}$ is exactly upper triangular. The probabilistic theorem is
`solveRoundedWith_pwrites`; termination with the accumulator bound `solveRoundedWith_terminates`
(standard model), completion `solveRoundedWith_completes` (no rounding model).

The design's generic hooked worklist (`solveDeflationWith`, `DeflationHook`, `skipHook`,
`trackingHook`) was dropped with §14.6.

**The core.** `roundedShQRWith L := solveRoundedWith (roundedDecoupleWith (schurDiag L)) (leafOnTailWords L)`
and `roundedShQRSchurWith L` (the core stage `[N, np, k, F, T] (A, P, U) → (A, U, Fl)`, the
threshold the first word, $n_s = F(k + 1 + n_p - 1)$, $w = kN$; `Algorithm: shifted-qr-rounded`), with `roundedShQRSmallEig sG`,
`roundedShQRSchur sG` the instances at the `SmallEig` leaf. `schurDiag L` reads the diagonal of a
Schur leaf's output: it is the eigenvalue routine of the decoupler (Regularize's Ritz values need
no Schur form).

**The leaf.** `smallEigProg sG : [d, nq, T] (Bk, Qw) → (Bk, Ub)`: `identityLeaf` (stores
$\mathbf{U}_b = \mathbf{I}$; for $d \le 1$ that is the output), then for $d \ge 2$ copy, perturb,
reduce with a log, replay on $\mathbf{U}_b$, and the core in Schur mode at the bottom width $1$.
The output is the triangular block in `Bk` and its accumulator in `Ub`; the eigenvalues are the
diagonal (the "forward fix" of §16).

### 3.3 The in-place rewrite of the decoupler chain

Only committed rotations are recorded. Find's trial steps (`comptauHalf`) write into a scoped
scratch log that is never replayed. The slot layout per decoupler call: round $j$'s sites at
$j(k + 1 + n_p)$, so $n_s = F(k + 1 + n_p)$ slots of $w = k(n+1)$ entries (design: $k + n_q + 2$
sites); the reduction: $N$ slots of $N - 1$ entries.

| merged program | change |
|---|---|
| `stepWithDiag`, `stepWithDiagInPlace`, `multiStepStable` | write their entries; `IsStableQRStepBy`, `IsStableQRChainBy` name the unitary |
| `stepComptau`, `comptauHalf` | record into a scoped scratch log |
| `trialStep`, `trialAccept`, `regularizeTrial(s)`, `regularizeDecide`, `regularizeWith(ScratchWith)` | the trial writes its slot, acceptance validates; outcome with the witness |
| `shTestStep`, `shPotentialAccept`, `shTrial(s)`, `shExc`, `shStep` | thread the log; outcome with the witness |
| `shIterationWith`, `roundedDecoupleLoopWith`, `roundedDecoupleWith` | the decoupler opens and fills its log; `RandomDecouplingRoutineContract` carries the log and the witness |
| `hessenbergReduceLast`, `rhess`, `decoupleLast`, `smallEigDecoupler` | write their slots (`hessenbergReduceLastSlots`, `rhessSlots`) |
| `solveRoundedWith`, `smallEigProg`, `roundedShQRWith` | Schur mode (§3.2) |

## 4. Numerical analysis

### 4.1 Why the witness must ride on the probabilistic proof

The merged step lemma is deterministic, but its error is $300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\| +
|s|)$, and `clearBelowSubdiagonal` removes entries of size $O(\boldsymbol{u}(\|\mathbf{H}\| + |s|))$:
the rotations come from the rounded $\mathbf{H} - s$. Shifts are bounded only on the good events of
Regularize, Find and Exc inside the merged probabilistic chain, and are never exported. A
deterministic "ghost" invariant could therefore not bound the named backward error on every tape;
that route (Q-accumulation as non-interfering code plus an instrumentation metatheorem) was
rejected. The chain's backward relation `IsPerturbedUnitarySimilar H H' ε` became the witnessed
`IsPerturbedUnitarySimilarBy (givensLog (n+1) (slotEntries w L)) H H' ε`. The proofs changed in
bookkeeping only (the witnessed `trans`, `givensLog_append`); the probabilistic arguments are
untouched. The orthogonality bound, by contrast, needs no shift bound: every replayed rotation is a
near-unitary update whatever the angles, so HD4 holds on every tape.

### 4.2 The relations

* **MW1** `IsPerturbedUnitarySimilarBy V A B ε := HasOrthonormalCols V ∧ ∃ E, specNorm E ≤ ε ∧
  B = Vᴴ * (A + E) * V`, with `isPerturbedUnitarySimilar_iff_exists_by`, `refl`, `trans`, `mono`,
  and the bridge `isPerturbedUnitaryPair_zero_iff` to the merged pair relation.
* **MW2, MW3** the witnessed block lifts with a computed coupling block, and the range form on
  `Fin N` (`IsPerturbedUnitarySimilarBy.of_range_block`).
* **MW5** the leaf lift with a dense $\mathbf{U}_b$ (`IsTrackedUnitarySimilar.lift_leaf_block`).
* **MW6** `IsTrackedUnitarySimilar` (§2), with `trans` composing $(1 + \varepsilon_U)(1 +
  \varepsilon_U') - 1$.
* **MW4** `IsTrackedUnitarySimilar.specNorm_sub_mul_mul_conjTranspose_le`: from $(\mathbf{I},
  \mathbf{A}_1)$, $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\| \le 2\varepsilon_U +
  \varepsilon_U^2$ and $\|\mathbf{A}_1 - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\| \le
  \varepsilon_T + (2\varepsilon_U + \varepsilon_U^2)(\|\mathbf{A}_1\| + \varepsilon_T)$, and the
  exact-unitary form; they take $0 \le \varepsilon_U$ (else, at an empty index type, the conclusion
  is false).
* **MC1** `IsConditionedDiagonalizable B Γ` ($\kappa_V \le B$, gap $\ge \Gamma$), with
  `IsConditionedDiagonalizable.of_isPerturbedUnitarySimilarBy` (transfer through a witnessed
  similarity of error $\le \Gamma/(16(n+1)B)$, to $(2B, \Gamma/2)$).

### 4.3 The full-mode step on a block-triangular matrix

Let $\mathbf{T}$ be block upper triangular for $(\{<lo\}, R, \{\ge lo+d\})$ and let the decoupler
return $\mathbf{W}' = \mathbf{V}^{\mathsf H}(\mathbf{T}_{RR} + \mathbf{E}_b)\mathbf{V}$,
$\mathbf{V}$ = `givensLog d L`. With $\widetilde{\mathbf{V}} = \operatorname{diag}(\mathbf{I},
\mathbf{V}, \mathbf{I})$ only the blocks $RR$, $(<lo)R$, $R(\ge lo+d)$ change; the replayed
couplings are within $\rho = 26\boldsymbol{u}|L|\,\|\mathbf{T}\|$ each, so

$$\mathbf{T}' = \widetilde{\mathbf{V}}^{\mathsf H}(\mathbf{T} + \widetilde{\mathbf{E}})\widetilde{\mathbf{V}},\quad
  \|\widetilde{\mathbf{E}}\|_2 \le \|\mathbf{E}_b\|_2 + 2\rho.$$

The cut writes $0$ over an entry of modulus at most $c$: an error $c$. For a leaf, the coupling uses
the computed $\mathbf{U}_b$ within $\varepsilon_L$ of a unitary; the extra error is the product
rounding and $2\varepsilon_LN_0$ (the leaf-accumulator term, found while proving, §16). Per round
the error is $\varepsilon(N_0) + c + 78\boldsymbol{u}\,n_sw\,N_0$ (decoupler) or $\beta +
8(n+1)(k+2)\boldsymbol{u}N_0 + 2\varepsilon_LN_0$ (leaf), at most $2(n+1)$ rounds, $N_0 = 2\Sigma$.
`uShQRSchurReplay n k np F RL B Γ S δ` $= b/\bigl(16(n+1)(78n_sw + 8(n+1)(k+2) + 54R_L)\Sigma\bigr)$,
$b$ = `shqrBudget n B Γ δ` $= \min(\delta, \Gamma/(16(n+1)B))$, keeps the replay terms within a
quarter of the budget (`shqrSchurError_le`). The leaf term costs at most $\log_2(1 + 54R_L)$ more
bits (`uShQRSchurReplay_zero_div_le`).

### 4.4 Error budget

In scaled units ($\|\mathbf{A}'\|_2 \le 4$ after normalization), with $c_1 = 1/2$, $c_2 = 2$:

$$2\cdot2\sqrt{n+1}\Bigl(\tfrac{\delta'}{2} + \tfrac{3\cdot50(n+1)^2\boldsymbol{u}}{1/2} + \delta' +
  \tfrac{8\varepsilon}{1/2}\Bigr) + 8(n+1)\boldsymbol{u} \le \delta$$

(`denseSchur_errors_le`): the regularizer's $\delta'/2$, the reducer's $\varepsilon_T$, the core's
$\delta'$, the accumulator's $\varepsilon$, and the scaling.

## 5. Probability

* The regularizer fails with probability $3(\varphi/2)/4$ (gap, condition, noise norm, each
  $\varphi/8$, inside `ginibrePerturb_pwrites`).
* The core at $(2B, \Gamma/2)$ fails with probability $\varphi/2$: the merged split
  $2(n+1)(\varphi_D + \varphi_L)$ with the decoupler and the leaf failure ($\varphi_L$ =
  `shqrSmallEigFailure`).
* Total $3\varphi/8 + \varphi/2 \le \varphi$.

The reducer is deterministic and the class transfer needs only its error
($\varepsilon_{H,T}(4 + \delta'/2) \le \Gamma/(16(n+1)B)$, threshold term 3).

## 6. Cost

All counts are instrumented static counts (`stmtCost` of `Stmt.instrument`: every primitive, test
and structural instruction at unit cost), bounded by monomials evaluated by `kernel_rfl`, so they
hold on every tape.

| statement | bound |
|---|---|
| `size_stmtCost_frobNormStage_le` | $120(n+1)^2$ |
| `size_stmtCost_ginibrePerturb_le` | $201(n+1)^2$ |
| `size_stmtCost_hessenbergReduceQ_le` | $2998(n+1)^3$ |
| `size_stmtCost_roundedShQRSchur_le` | $380748(n+1)^3(k+1)^4(p+n_q+1)(F+1)(T+1)^2$ |
| `size_stmtCost_schurPipelineWith_le` (glue) | $120(N+1)^2$ |
| `denseSchur_work_le` (HD6) | $384547(n+1)^3(k+1)^4(n_r+n_q+1)(F+1)(T+1)^2$ |
| `denseSchurWork` (CT2) | $120(n+1)^2 + 201(n+1)^2 + 2998(n+1)^3 + 380748(n+1)^3(k+1)^4(n_r+n_q+1)(F+1)(T+1)^2 + 128(n+2)^2$ |

The power of $k + 1$ is $4$, that of the eigenvalue solver: the replays on the couplings and on the
accumulator cost no more than a step (the design expected $5$). No amortization over the deflation
tree is used; a run-time count (the paper's constant) would need the `Accepts` route and is not
planned. The polylog form (HD7) has $p = 15$.

## 7. Edge cases and junk values

* **$\mathbf{A} = 0$.** $\mathrm{fl}(\|\mathbf{A}\|_{\mathsf F}) = 0$ iff $\mathbf{A} = 0$ under
  the standard model. The pipeline branches with `isPos`; on the zero branch it writes
  $\widehat{\mathbf{U}} = \mathbf{I}$ and the flag $0$, and $\widehat{\mathbf{T}} = \mathbf{A} = 0$;
  both bounds are $0 \le 0$. No division by $0$.
* **Order 1** ($n = 0$): the worklist sends the $1\times1$ block to the leaf; the leaf takes the
  $d \le 1$ branch ($\mathbf{U}_b = \mathbf{I}$, `identityLeaf`, which needs the literal $1$ only at
  positive orders). In leaves, $d = 0$ gives empty matrices.
* **Nat subtraction.** Replay ranges `N - lo - d` appear only in program dims; in statements ranges
  are written $lo + d \le N$. `givensAt` uses `r + 1 < n`. A replay of a block of order $d \le 1$
  at the bottom needs `slotEntries w L = [] ∨ lo + 1 < N` (§16).
* **Zeros.** `M.lit 0 = 0` and $\mathrm{fl}(s\cdot0) = 0$ follow from `StdModel`.
* **Log words.** No count word. Plane words are exact naturals $\le n$ (`hNat` at $n + 1$
  suffices); an invalid slot (valid word $\le 0$, from the zero fill) is skipped; the padding
  $(0, 0, 0)$ is the identity.
* **Positivity**: `uDenseSchur_pos`, `uShQRSchur_pos`.
* **Scale invariance**: $\Sigma$ is fixed ($4$, then $8$) after normalization, so HD5 has no
  $\|\mathbf{A}\|$ term.

## 8. Placement

| folder | content |
|---|---|
| `Matrix/FinitePrecision` | the stored-matrix layer and the rotation programs (O7 moves); the Givens log layer (log, slots, close, replay); stored blocks and strided products |
| `Matrix/Perturbation/UnitarySimilarity` | MW1–MW6 |
| `Matrix/Perturbation/EigenvalueBackward` | MC1 |
| `Matrix/Factorizations/Givens` | MG1 |
| `Ops` | `StdModel` zeros (MS1) and the `nrm2` bounds (`RoundedScalarBlas.nrm2_writes_stdModel`) |
| `Eigensolvers/HessenbergReduction` | the reduction with its log, `hessenbergReduceQ` and its contract |
| `Eigensolvers/ShiftedQR` | the chain in Schur mode; the Schur-mode worklist (steps, updates, rounds); the core and its contract; the certificate |
| `Eigensolvers/SmallEig` | Part III in Schur mode; `identityLeaf`; the leaf contract; the certificate |
| `Eigensolvers/Schur` (new) | contracts, norm estimate, regularizer, pipeline, residual algebra, completion, the dense solver, its bits and its certificate |

**Placement.** The general lemmas proved for this stage live in the files of their topics:
`Ops.PWrites.of_forall_eq`, `Ops.PWrites.congr_eval` (`Ops/Logic/ProbabilisticFamily`),
`Ops.Writes.congr_eval`, `Ops.eval_seq_seq_seq_assoc` (`Ops/Logic/Writes`),
`Ops.StdModel.exists_holdsMatrix_mul` (`Matrix/FinitePrecision/StoredProducts`),
`Ops.stdModel_one_zero` (`Ops/Catalog/Scalar`), `Ops.RoundedScalarBlas.writes_nrm2` (its profile),
`Ops.size_sup_add_size_inf` (`Ops/MonomialWork`), `ShiftedQR.LoBd.of_hiBd`,
`ShiftedQR.HiBd.of_hiBd` (`ShiftedQR/RoundedTheoremsBits`), `IsTrackedUnitarySimilar.round`,
`IsTrackedUnitarySimilar.specNorm_le_add` (`Matrix/Perturbation/UnitarySimilarity`), the
`IsRangePartition` lemmas (`Matrix/QRIteration/DeflationRanges`) and the log lemmas
(`Matrix/FinitePrecision/GivensLog`, `GivensReplay`, `GivensReplayBlocks`).

**Vocabulary.** `IsPerturbedUnitarySimilarBy`, `IsTrackedUnitarySimilar`,
`IsConditionedDiagonalizable`, `IsRangeBlockTriangular`, `givensAt`, `givensLog`, `GivensEntry`,
`slotEntries`, `HoldsSlottedLog`, the five contracts and `TerminatingSchurCore`, `SchurOutput`,
`SchurOrth`, `SchurPipelineInput`, `HoldsSchurPair`. No Mathlib deviation: the witnessed
predicate is a new NLAlib notion next to an NLAlib notion.

**Shared machinery.** The witnessed `trans` and `givensLog_append` (every backward step); the
range-block lift (decoupler rounds, leaves, reducer); MG4 (couplings, $\widehat{\mathbf{U}}$, the
reducer); the tracked relation and PP2 (every stage swap); `BackwardStep.in_frame` and
`BackwardStep.allocs` (frames and allocation, already on `main`); `stmtWorkMono` + `kernel_rfl`
(every static count).

## 9. Targets

All 70 design targets (as revised by §14.3 and §14.6) are proved, plus the corollary targets
COR1–COR4. The ids used in this note: MV (moves), MW/MG/MC/MS/MR (matrix layer), GL/PR (log layer
and programs), RF (in-place rewrite), SW (Schur-mode worklist), SL/SQ (Part III and Part II in
Schur form), SC (contracts), NM/RG (stages), PP (pipeline), HD (dense solver), CT (certificates).

## 10. Risks, as they turned out

* The in-place rewrite of the chain was the bulk, as expected; every `Writes` lemma gained the
  log's hypotheses (§16 lists the ones that changed meaning).
* Measurability of the outcome sets with the log read: solved by a measurable read of the closed
  slots (`slottedLogRead`, the closed-slot event).
* `kernel_rfl` on the larger trees: works, with `maxRecDepth 100000`.
* The constants moved at proof time (O6); §1 and §15 have the final values.

## 11. Decisions (resolved by the maintainer after the review)

1. **O1** (a) `IsPerturbedUnitarySimilarBy`, with the two-error tracked relation in the contracts
   and the worklist invariant. Ghost route rejected.
2. **O2** (a) dense $\mathbf{U}_b$ at the leaf.
3. **O3** the slotted static log, self-describing entries.
4. **O4** superseded by §14.6 ("Schur is the program").
5. **O5** deferred (the spectrum-only core; no consumer).
6. **O6** constants allowed to move at proof time.
7. **O7** move `HoldsMatrix` and the rotation programs first (done).
8. **B5** approved: the merged certificate numerals change (§15).

## 12. Material

The Part I intro (`src1/intro.tex:18, 176`), Part II and III LaTeX, the two predecessor notes,
the errata of Part II (N7, the bottom-$k$ cut, kept; G16/D3.4/Q4, the shift-dependence of the
step, which drives §4.1), the sizing study of Part II (static $n^3$, guard narrowing),
`Computation-CertifiedRoutines.md` (routine-certificate precedent), Higham 2002 Ch. 19 (Givens
error, accumulation), Watkins 2008 (Schur vectors by accumulation).

## 13. Statements elaborated before proving

The statements of §1 and §2 and the log-layer programs were elaborated against the built tree
before the skeleton; the one fix from elaboration was an explicit import of
`Matrix.Perturbation.UnitaryPair`.

## 14. Changes after review

The design review ("revise, then approve for skeleton") and three maintainer messages (decisions
O1–O7, B5 approved, "the best final structure, not the least invasive diff"). Every change is
applied in the sections above.

### 14.1 Blockers

* **B1, `hclass`.** It was `δR + 3εH ≤ Γ/(16(n+1)B)`, unsatisfiable at the instance. Now the class
  is a predicate pair `C`, `C'` with a transfer hypothesis through the **reducer's** witnessed
  similarity only; at the instance it is MC1, guaranteed by threshold term 3.
* **B2, two errors.** The contracts and the worklist invariant use `IsTrackedUnitarySimilar εU εT`;
  the orthogonality holds on every tape (HD4).
* **B3, bits.** HD5 reads $\log_2(1/\boldsymbol{u}_0) \le c_1L^4(\log_2 L + 1)^2 + c_2$.
* **B4, exact naturals.** No count word: `IsExactNatLit id Mch (n + 1)` suffices for HD1 and HD4.
* **B5, merged certificate numerals.** Approved; final values in §15.

### 14.2 Structure

* **Witness (O1 a).** Every backward conclusion of the chain names its unitary
  (`IsPerturbedUnitarySimilarBy (givensLog L)`); the `∃ U` statements are corollaries.
* **Log (O3).** A reusable Givens log layer with self-describing entries (plane, $p$, $q$), so the
  replay is producer-agnostic: the reducer, the sweep, `rhess` and any later Givens algorithm share
  one replay and one error lemma.
* **Modularity (S2).** Class predicates, the threshold among the core's words, the pipeline's `nr`
  a dim, the norm estimate two-sided.
* **Library first (S3, O7).** The norm stage is the merged `nrm2` with its `StdModel` bound
  (`RoundedScalarBlas.nrm2_writes_stdModel`); the regularizer stage is the merged
  `ginibrePerturb_pwrites`.
* **S4.** PP2's glue condition is $8(n+1)\boldsymbol{u} \le 1/4$; the core states $0 < \Gamma$.

### 14.3 Targets

70 targets after the review. Removed before proving: SW1–SW6 (as first planned), SL2, HD2, OL1,
OPT1, OPT2. Added: MV1, MV2, MW6, MC1, GL1, GL2, GW1–GW7, SH1, SH2, SL6, SQ5, RF7b; §14.6 then
dropped or folded the GW/SH targets and added COR1–COR4.

### 14.4 Merged statements and numerals (B5)

Moved to §15 with their final values.

### 14.5 Re-check

* **εU relative.** `‖U' − U V‖ ≤ εU ‖U‖`; `trans` composes as $(1 + \varepsilon_U)(1 +
  \varepsilon_U') - 1$, which telescopes from $\mathbf{U}_0 = \mathbf{I}$ to $(1 +
  24\boldsymbol{u})^R - 1$. `‖U‖ ≤ 2` dropped from the contracts.
* **Threshold term 3** is $t_1t_2/(28800(n+1)^3)$.
* **Skeleton details.** The log entry is written from views of words the producer holds, the plane
  a dimension; `slottedLogOpen` zero-fills; the pending entries are state; `hNat` is a hypothesis
  of `slottedLogWrite_writes`, not of the producers.

### 14.6 Schur is the program (maintainer, after the re-check)

Supersedes O4(b), the hook and the sink. The Schur-mode programs **replace** the merged
eigenvalue-only programs in place: the shifted QR chain (step, Find, Regularize, Sh, Exc,
iteration, decoupler, worklist, `roundedShQR…`) and Part III (`rhess`, `decoupleLast`,
`smallEigDecoupler`, `smallEigProg`, the leaf) record their committed rotations, replay them on the
coupling blocks and on $\widehat{\mathbf{U}}$, and output $(\widehat{\mathbf{U}}, \widehat{\mathbf{T}})$.
The eigenvalue-only programs are deleted; there is no generic hooked worklist, no skip instance, no
sink parameter. Every merged eigenvalue theorem is a corollary of the Schur theorem of its program
(`diag T̂` lists the spectrum of $\mathbf{A} + \mathbf{E}$), keeping its name where the program
survives. Costs grow by a constant factor and precision conditions get slightly stronger
(`uShQRSchur` in place of `uShQRSmallEig`); this is accepted. Every changed statement or numeral
is in the rename map's `statementChanged`, every deleted declaration in `removed` with its
replacement.

**Deleted** (rename map `docs/renames/2026-11-schur.json`): the oracle-leaf Part II program
`roundedShQR` with its theorems (`_measureReal_not_spectrum_le`, `_terminates`, `_relative`,
`_hermitian`, `_work_le`) and its certificate (`shqrProgram`, `stmtWorkMono_shqrProgram`,
`shqrAlgorithm`, `roundedShQR_algorithm_measureReal_not_accepts_le`, the manifest variants);
the kernel-instance decoupler `roundedDecouple`, `roundedDecoupleLoop`; the eigenvalue leaf
contracts and lifts (`RandomLeafContract`, `RandomLeafRoutineContract`, `BackwardLeafContract`,
`BackwardLeafRoutineContract`, `liftLeaf`, `liftDecoupler`, `seLeaf`); `solveRounded` and its
wrapper theorems; `TerminatingDecoupler`, `TerminatingLeaf`; `copyLeaf` (now `identityLeaf`); the
`_at` variants of `roundedShQRWith_measureReal_not_spectrum_le` and `roundedShQRWith_terminates`.

**Meaning changes of the eigenvalue corollaries.** The eigenvalue theorems kept under their names
(`smallEig_*`, `roundedShQRSmallEig_*` and their `_relative`, `_hermitian`, `_unconditional`
forms) now run the Schur-mode programs, which changes what a caller must supply and what it gets:
the input matrix is destroyed (its buffer is overwritten by $\widehat{\mathbf{T}}$); the computed
eigenvalues are the diagonal of $\widehat{\mathbf{T}}$ in that buffer, not a separate output
column; and the shifted QR corollaries (`roundedShQRSmallEig_*`) require the accumulator buffer
($2(n+1)^2$ words, the former output) to be initialized, holding some stored matrix, which the run
multiplies by its rotations (`SmallEig` writes its own identity there and needs only the room).

**Check files.** Two edits of check data were approved by the maintainer on 2026-11-19 (recorded
in the harness decisions file for SCHUR): `scripts/ops_certificates.txt` regenerated by
`OPS_CERTIFICATES_WRITE=1` (the line of the deleted `shqrAlgorithm` removed; lines for
`denseSchurAlgorithm` and `schurPipelineAlgorithm` added; no other line changed), and the kernel
replay limit of `scripts/stage_check.sh` raised from `-M 8000` to `-M 12000` (the full replay of the
library with this stage peaks at about 8.6 GB; CI runs the replay without a limit).

## 15. Constants and certificate numerals (B5)

| declaration | `main` | final |
|---|---|---|
| `SmallEig.stmtWorkMono_smallEigProgram`, `smallEigWork` | $373483\,(n+1)^4(T+1)^2$ | $517058\,(n+1)^4(T+1)^2$ |
| `ShiftedQR.stmtWorkMono_shqrSmallEigProgram`, `shqrSmallEigWork` | $675307\,(n+1)^3(k+1)^4(n_p+1)(F+1)(T+1)^2$ | $967736\,(n+1)^3(k+1)^4(n_p+1)(F+1)(T+1)^2$ |
| `SmallEig.smallEig_work_le` | $\exists c$ (witness $3473$), uninstrumented, $(n+1)^4(T+1)^2$ | $80390\,(n+1)^4(T+1)^2$, instrumented, explicit |
| `ShiftedQR.roundedShQRSmallEig_work_le` | $\exists c$ (witness $15895$), uninstrumented, $(n+1)^4(k+1)^5(n_p+1)(F+1)(T+1)^2$ | $369224\,(n+1)^3(k+1)^4(n_p+1)(F+1)(T+1)^2$, instrumented, explicit, at the log dims $n_s = F(k+1+n_p)$, $w = k(n+1)$ |
| `ShiftedQR.stmtWorkMono_shqrProgram` | $196218\,(n+1)^3(k+1)^3(n_p+1)(F+1) + 8b^4\overline w$ | removed with the oracle program |

The intermediate values recorded in the rename map's note ($514650$, $960712$, $960776$) are those
of the skeleton; the final ones changed again when `comptauHalf` opened its scratch log and the
leaf ran on the tail words. The exponents of the certificates are unchanged.

New numerals of this stage: §6 (all `kernel_rfl`), the precision constants of §1 ($16$, $3200$,
$28800$, $1/100$, $4096$, $64$, $58$, $24$, $27$, $50$, $54$, $78$), and HD7's $p = 15$.

## 16. Statement fixes found during proving

Each changed a statement of the skeleton; none weakened a headline. Grouped by topic.

**The log and the chain.**

* `trialAccept_terminates` needs `hNat` at $1$ (the valid word is the literal $1$);
  `regularizeTrial_terminates` needs $0 < k$; `regularizeDecide_terminates` and
  `regularizeWithScratchWith_terminates` need the log apart from the views.
* The nine Sh termination lemmas: an exact slot count, the pending entries as state, the log apart
  from the views, index literals.
* `comptauHalf` (Find) opens a scoped scratch log, so it needs `IsIndexLit` and `hNat` for its
  planes; the certificate numerals moved with it.
* `rhess_writes_word`, `rhess_pwrites`, `rhess_terminates`: $2 \le N \le n_{\max} + 1$, the planes
  satisfy $x_1 + 1 < N$, and `rhess_pwrites` takes `hNat`.
* `multiStepStable_writes_replicate_succ`: index literals and exact naturals up to $n + 1$.
* `distSpec_accuracy`, `distSpec_terminates` take `hNat` (the OneEig callers pass it).
* `givensReplayRows_specNorm_sub_le`, `givensReplayColumns_specNorm_sub_le`:
  `slotEntries w L = [] ∨ lo + 1 < N` (a padding entry of a block of order $\le 1$ at the bottom
  would rotate rows $N - 1, N$).
* `reduceLastStep_writes_word`: the log need only be apart from the matrix (`Fp.Disj`), not in
  another buffer (a strengthening); log programs return the tape position.
* The `SmallEig` decoupler contract: the log in a buffer of its own.

**The worklist and the leaf.**

* `solveRoundedWith_pwrites`: $\boldsymbol{u} \le 1/100$, $0 \le N_0$, and the round error gains
  $2\varepsilon_LN_0$ (the leaf accumulator's error in the couplings); hence the leaf term
  $54R_L$ in `uShQRSchurReplay`, threaded through `uDenseSchurWith` and
  `denseSchurRotationsWith` as $R_L$.
* Termination split in two: `solveRoundedWith_completes` (any scalar machine, no rounding model)
  and `solveRoundedWith_terminates` (the accumulator bound, standard model); the leaf update uses
  the machine conjugate transpose (`machineConjTranspose`), equal to the adjoint under the standard
  model.
* `identityLeaf_writes` needs the literal $1$ only at positive orders.
* The forward fix of `smallEigProg`: the eigenvalues are the diagonal of $\mathbf{T}_b$ in `Bk`,
  and the footprint is `Bk ⊔ Ub` (both $2(n+1)^2$ words), not a $2(n+1)$-word output; the replay
  precision is absorbed by `uSmallEig`.
* The leaf runs on the last twelve words (`leafOnTailWords`), as the decoupler does.

**The contracts and the pipeline.**

* Contracts with order bounds (`nmax` in the norm estimate, the reducer and the terminating core)
  and room for the flag.
* PP2: $0 \le \varepsilon_{H,T}$, $0 \le \varphi_R$, $0 \le \varphi_C$ added; the norm estimate
  writes to another buffer.
* The stored-product constant is $8(p+1)\boldsymbol{u}$ (`specNorm_matMulWord_sub_le`), under
  $\boldsymbol{u} \le 1/8$.
* The shifted QR headlines hold an accumulator and have room for it (`ShQRSmallEigInput`,
  `ShQRSchurInput`); the certificate inputs count the accumulator buffer of $2(n+1)^2$ words
  (`smallEigInputWords`, `shqrSmallEigInputWords`).
* The `SmallEig`-leaf headlines take $\boldsymbol{u} \le$ `uShQRSchur` (the replay term added).
* PP4 and HD6 count at the offsets the pipeline passes to each stage (the "honest" count), not at
  zero offsets.
* The certificates' `wp` needs no rounding model (`SchurSizes`, `SmallEigSizes` without
  `StdModel`; `…_completes` lemmas).

**Constants against the design.** $\delta' = \delta/(16\sqrt{n+1})$ (design $32$); norm bounds $4$
and $8$ (design $2$ and $4$); threshold term 2 is $\delta'/(3200(n+1)^2)$, term 5 (accumulator)
$\delta/(4096(n+1)R)$ (design $\delta/(192R)$), term 6 (scaling) $\delta/(64(n+1))$ (design
$1/(32(n+1))$), and $1/100$ is a term of its own; $R$ has the leaf term $(n+1)R_L$; the static count
has $(k+1)^4$ and $(n_r + n_q + 1)$ (design $(k+1)^5(n_q+1)$); $p = 15$ (design about $12$).

## 17. Post-review changes

Unused hypotheses removed after the stage review (each a strengthening; no statement weakened):

* `identityLeaf_writes` loses `hl` (liveness) and `hwu` (disjointness of block and accumulator).
* `distSpec_writes_word` loses `hL : IsIndexLit`.
* `roundedDecoupleIteration_pwrites` loses `hlgL`; `roundedDecoupleLoop_pwrites` loses `_hw`.
* `IsPerturbedUnitarySimilarBy.of_range_block` loses both `IsRangeBlockTriangular` hypotheses.
* `IsTrackedUnitarySimilar.trans` loses $0 \le \varepsilon_U$ (only $0 \le \varepsilon_U'$ stays).
* `IsTrackedUnitarySimilar.specNorm_sub_mul_mul_conjTranspose_le` loses $\varepsilon_U \le 1/8$.
* `schurPipelineWith_measureReal_not_schur_le` loses `IsToNat` and $c_1 \le c_2$.
* `HoldsSlottedLog.slotEntries_read` loses its vacuous hypothesis.
* `slottedLogOpen_writes`, `slottedLogWrite_writes`, `slottedLogValidate_writes` lose their `Live`
  hypotheses.
