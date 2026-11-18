# A dense Schur solver on the operation core (SCHUR)

Stage SCHUR builds an end-to-end dense eigensolver whose output is a Schur form: for any complex
$\mathbf{A}$ of order $n + 1$ it computes words $\widehat{\mathbf{U}}$, $\widehat{\mathbf{T}}$
with $\widehat{\mathbf{T}}$ exactly upper triangular. It is built from the finite-precision shifted
QR of [BanksGarzaVargasSrivastava2022] (Part II, on `main`,
[Eigensolvers-ShiftedQR-FiniteOps](Eigensolvers-ShiftedQR-FiniteOps.md), the template of this
note) and the `SmallEig` program of [BanksGarzaVargasSrivastava2025] (Part III, open PR,
[Eigensolvers-SmallEig-PartIII](Eigensolvers-SmallEig-PartIII.md)). The papers compute
eigenvalues only. Part I's introduction (`src1/intro.tex:176`) says, without proof, that the
full Schur form "can be obtained directly from our results and will have the same asymptotic
running time". This stage proves it.

This note is the design only. No library Lean is written, and nothing changes in the checks,
CI, the lakefile, the allowlists, `*Targets.lean` or `docs/targets.*`. Base: `cleanup/smalleig`
(the Part III PR plus one docstring commit), branch `design/schur`. Decisions approved before
this note (harness `state/decisions/SCHUR.json`): S1 full Schur form; S2 accuracy in computed
form, with the exact-unitary form as a corollary; S3 the algorithm computes $\|\mathbf{A}\|_{\mathsf F}$;
S4 full-mode generalizations of the merged programs, with the eigenvalue-only programs kept as
wrappers. After the plan was approved the maintainer added a modularity requirement (§2): every
stage is a routine parameter with its own contract, and one generic composition theorem covers
any components that meet them. Targets: `~/nlalib-harness/pilot/schur-targets.json`. The
statements of §1, §2 and the new program interfaces were elaborated in a scratch file (§12).

## 0. Summary

* **Headline (§1).** For every $\mathbf{A} \in \mathbb{C}^{(n+1)\times(n+1)}$, $0 < \delta \le 1$
  and $0 < \varphi \le 1$, at a precision $\boldsymbol{u} \le \boldsymbol{u}_0(n,\delta,\varphi)$
  with $\log_2(1/\boldsymbol{u}_0) = O(\log^4((n+1)/(\delta\varphi)))$, the program `denseSchur`
  stores, except with probability at most $\varphi$, a failure word $0$ and words
  $\widehat{\mathbf{U}}$, $\widehat{\mathbf{T}}$ such that $\widehat{\mathbf{T}}$ is upper
  triangular,
  $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2
  \le \delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
  \mathbf{I}\|_2 \le \varepsilon_U$. Here $\varepsilon_U = 64R\boldsymbol{u} \le \delta$, with
  $R(n,\delta,\varphi)$ an explicit bound on the number of rotations accumulated on
  $\widehat{\mathbf{U}}$. There is no hypothesis on $\mathbf{A}$. The run terminates on every
  tape, and its static count is $c(n+1)^3(k+1)^5(n_p+1)(F+1)(T+1)^2$, which is
  $O(n^3\,\mathrm{polylog}(n/(\delta\varphi)))$. Corollaries: $\operatorname{diag}\widehat{\mathbf{T}}$
  lists the spectrum of a matrix $\mathbf{A} + \mathbf{E}$; and an exact unitary $\mathbf{V}$
  within $\varepsilon_U$ of $\widehat{\mathbf{U}}$ gives $\mathbf{A} + \mathbf{E} =
  \mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H}$.
* **Modular (§2).** Five stages are routine parameters, each with a named contract: the norm
  estimate, the regularizer, the Hessenberg reducer, the Schur core and, inside the core, the
  small-block Schur solver. The generic pipeline `schurPipelineWith Nm Reg Red Core` has one
  composition theorem: for any components that meet the contracts, the errors add, the failure
  probabilities add, and the static count is the sum of the components' counts plus $O(n^2)$.
  The headline is the instance at the current components.
* **Main finding (§4.1).** The cheap route fails. That route keeps the merged probabilistic
  proofs untouched and adds Q-accumulation as non-interfering "ghost" code. A Schur form needs
  the backward error with the unitary named, not only "some unitary exists". The named error of
  the rounded step contains the cleared below-subdiagonal garbage, which is
  $O(\boldsymbol{u}(\|\mathbf{H}\| + |s|))$. The shift modulus $|s|$ is bounded only on the good
  event of the merged probabilistic analysis, so the witness must travel through that analysis.
  This is decision S4 as approved: the decoupler chain is generalized to programs that write a
  rotation log, and the merged programs become wrappers.
* **Size (§9).** 61 planned targets (S 20, M 28, L 13), plus 2 optional: L1 matrix library 10
  (S 6, M 4); L2 Ops and programs 9 (S 1, M 7, L 1); L3 the refactor of the decoupler chain 12
  (S 2, M 4, L 6); L4 the Schur worklist and the stages 17 (S 6, M 7, L 4); L5 composition,
  instance and certificate 13 (S 5, M 6, L 2). Twelve waves, 0 to 11.
* **Open decisions (§11):** O1 the witness predicate, O2 the leaf interface (dense $\mathbf{U}_b$
  or a log), O3 the log capacity, O4 the worklist as a sibling program rather than a wrapper,
  O5 the spectrum-only core variant, O6 the error constants, O7 the placement of the rotation
  programs.

## 1. The headlines, in Lean

Notation as in Part II/III: order $n + 1$, `S` for $\Sigma$. The machine, sampler and tape
hypotheses are those of the merged `roundedShQRSmallEig_measureReal_not_spectrum_le`. The two
Ginibre tails are proved (`ginibreGapTail`, `ginibreConditionTail`), so no tail hypothesis
appears. All statements below elaborated (§12).

```lean
/-- The output: flag `0`, `T̂` upper triangular, the computed-form bounds. -/
def SchurOutput {n : ℕ} (a uo f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eA eU : ℝ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix uo U μ'.store ∧ T.IsUpperTriangular ∧
    specNorm (A - U * T * Uᴴ) ≤ eA * specNorm A ∧ specNorm (Uᴴ * U - 1) ≤ eU

/-- HD1: the dense Schur theorem. -/
theorem denseSchur_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uDenseSchur n δ φ)
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (denseSchurParams n δ φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (denseSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n δ φ) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A δ δ) μ} ≤ φ
```

Companions (same hypotheses):

* **HD2** `denseSchur_measureReal_not_orth_le`: the same event with
  `SchurOutput a uo f A δ (64 * denseSchurRotations n δ φ * u)`, so
  $\varepsilon_U(n,\delta,\varphi,\boldsymbol{u}) = 64R\boldsymbol{u}$.
* **HD3** the corollaries, stated once for any `SchurOutput` (PP3) and instantiated:
  `SchurOutput.exists_isEigenvalueListing`, giving $\|\mathbf{E}\|_2 \le (e_A + 4e_U)\|\mathbf{A}\|_2$
  with `IsEigenvalueListing (A + E) fun i => T i i` (from
  `HasOrthonormalCols.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul`, merged);
  and `SchurOutput.exists_hasOrthonormalCols`, giving a unitary $\mathbf{V}$ with
  $\|\widehat{\mathbf{U}} - \mathbf{V}\|_2 \le e_U$ and $\mathbf{A} + \mathbf{E} =
  \mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H}$. The second is cheap: the pair relation
  (§4.2) carries the exact $\mathbf{V}$ (`IsPerturbedUnitaryPair.exists_witness`, merged).
* **HD4** `denseSchur_terminates`: `Writes .total … (fun _ => True)` on every tape and every
  input, with no precision hypothesis.
* **HD5** `logb_inv_uDenseSchur_le`: $\log_2(1/\boldsymbol{u}_0) \le c_1\log_2^4 Y + c_2$ with
  $Y = 4(n+1)/(\delta\varphi)$. This is HL4's $O(k^2\log^2 Y)$ at the class of §5, which is
  polynomial in $Y$, plus $\log_2(64R/\delta)$.
* **HD6** `denseSchur_work_le`: the static count is at most
  $c(n+1)^3(k+1)^5(n_p+1)(F+1)(T+1)^2$ (`kernel_rfl`). **HD7** `denseSchur_work_le_polylog`
  states it at `denseSchurDims n δ φ` as $\le C(n+1)^3\log_2^{p}Y$. The exponent is fixed at
  proof time; it is about $12$, from $k = O(L\log L)$, $F = O(L)$ and $T = O(L^2\log L)$ with
  $L = \log Y$.
* **CT2** the certificate `denseSchurAlgorithm` and
  `denseSchur_algorithm_measureReal_not_accepts_le`, in the shape of the merged
  `roundedShQRSmallEig_algorithm_measureReal_not_accepts_le`: one counted run, failure at most
  $\varphi$ on Accepts plus `SchurOutput`. The work is `schurPipelineWork` (§2.3), the sum of
  the components' work polynomials.

**The precision threshold**, `uDenseSchur n δ φ`, is the minimum of five terms. Write
$\delta' = \delta/(32\sqrt{n+1})$ and $(B, \Gamma) = (2/t_2, t_1/2)$, with $t_1, t_2$ =
`smallEigGap/Cond (n+1) 2 δ' (φ/2)` at the proved tails (§5).

1. `uSmallEigReduce (n+1) 2 δ' (φ/2) ginibreGapTail ginibreConditionTail`, for the regularizer;
2. $1/(100(n+1)^2)$ and $\delta'/(64\cdot 50(n+1)^2)$, for the reducer;
3. `uShQRSchur n k (2B) (Γ/2) 4 δ' (φ/2)`, the core's threshold: the merged
   `uShQRSmallEig` at that class, together with the replay term of §4.3;
4. $\delta/(64R)$, for the orthogonality;
5. $1/(8(n+1))$, for the norm estimate and the scaling.

**$\varepsilon_U$.** It equals $64R\boldsymbol{u}$, where $R$ = `denseSchurRotations n δ φ`
$= (n+1)^2 + 2(n+1)\bigl(G_{\mathrm{dec}}(n+1) + 4k^2\bigr)$ and
$G_{\mathrm{dec}}(d) = F(k + n_p + 2)k\,d$ is the log capacity of a decoupler call (§4.4). The
term $4k^2$ is the dense leaf update, counted as rotation-equivalents. Under item 4 the bound is
at most $\delta$, so HD1 states both bounds with $\delta$ and HD2 gives the sharp form.

## 2. Modularity: stages, contracts, the generic pipeline

The maintainer's requirement is "make stuff modular so we can swap in other stuff as we need".
Each pipeline stage is a routine parameter `… : Impl O Q`, as SMALLEIG's `SE` (decision D2), and
has a contract named in the stage-neutral library style. All contracts state the stored
accumulator through **one relation**, the merged `IsPerturbedUnitaryPair a b ε` on the pair
$(\widehat{\mathbf{U}}^{\mathsf H}, \mathbf{T})$. Its first component is the conjugate transpose
of the computed accumulator, at scale $a = 1$; its second is the matrix, at scale $b$. Stages then
compose by `IsPerturbedUnitaryPair.trans` (merged, B2), and the computed-form conclusion is one
lemma at the end (MW4).

### 2.1 The contracts (Lean, elaborated)

The files are under `Eigensolvers/Schur/` (new folder). The contracts mention no shifted QR.

```lean
/-- SC1 (stage e): a norm estimate, deterministic. `[N] (A) → (S)`. -/
def FrobNormEstimateContract (ρ : ℝ) (Nm : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a s : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A : Matrix (Fin N) (Fin N) ℂ),
    HoldsMatrix a A μ.store → μ.Live [a, s] → s.2 + 1 ≤ μ.store.len s.1 →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock s.1 s.2 1) →
    Writes .total I tape Nm.body (Env.frame [N] [a, s]) (Store.inBlock s.1 s.2 1)
      (fun μ' => ∃ x : ℝ, μ'.store.get s.1 s.2 = some x ∧ |x - frobNorm A| ≤ ρ * frobNorm A) μ

/-- SC2 (stage a): a randomized regularizer into the class `(B, Γ)`. `[N, np] (A, P) → (A)`. -/
def RandomRegularizerContract (law : ℕ → Measure ℝ) (δ φ B Γ : ℝ) (nmax : ℕ) (S : ℝ)
    (ps : List ℝ) (Reg : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), n + 1 ≤ nmax →
    specNorm A ≤ S →
    PWrites law I Reg.body (Env.frame [n + 1, ps.length] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix a A μ.store ∧ μ.store.readBlock q.1 q.2 ps.length = some ps ∧
        μ.Live [a, q] ∧
        Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
          (Store.inBlock q.1 q.2 ps.length))
      (fun μ' => ∃ (E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
        HoldsMatrix a (A + E) μ'.store ∧ specNorm E ≤ δ ∧ IsUnit V ∧
        (A + E) * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B ∧
        ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) φ

/-- SC3 (stage b): a Hessenberg reducer with an accumulated unitary, deterministic.
`[N] (A, U) → (A, U)`. -/
def HessenbergReducerContract (ε : ℝ) (Red : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a uo : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A U : Matrix (Fin N) (Fin N) ℂ),
    HoldsSchurPair a uo U A μ.store → μ.Live [a, uo] →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N))) →
    Writes .total I tape Red.body (Env.frame [N] [a, uo, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => ∃ U' H : Matrix (Fin N) (Fin N) ℂ, HoldsSchurPair a uo U' H μ'.store ∧
        IsUpperHessenberg H ∧ IsPerturbedUnitaryPair 1 (specNorm A) ε (Uᴴ, A) (U'ᴴ, H)) μ

/-- SC4 (stage c): a randomized Schur core on Hessenberg input in the class `(B, Γ)`.
`[N, k, np, F, T] (A, P, U) → (A, U, Fl)`. -/
def RandomSchurCoreContract (law : ℕ → Measure ℝ) (ε φ B Γ : ℝ) (k F T nmax : ℕ) (S : ℝ)
    (ps : List ℝ) (Core : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} (H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ), n + 1 ≤ nmax → IsUpperHessenberg H → specNorm H ≤ S →
    specNorm U ≤ 2 → IsUnit V → H * V = V * Matrix.diagonal d → pseudoConditionNumber V ≤ B →
    (∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) →
    PWrites law I Core.body (Env.frame [n + 1, k, ps.length, F, T] [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => HoldsSchurPair a uo U H μ.store ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.Live [a, p, uo, f] ∧
        Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1])
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store ∧ Tm.IsUpperTriangular ∧
        IsPerturbedUnitaryPair 1 1 ε (Uᴴ, H) (U'ᴴ, Tm)) φ

/-- SC5 (stage d): a randomized small-block Schur solver, any block of order `≤ kmax`.
`[d, np, T] (Bk, P) → (Bk, Ub)`. -/
def RandomSchurLeafContract (law : ℕ → Measure ℝ) (β φ : ℝ) (kmax : ℕ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) (L : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p ub : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax → specNorm B ≤ Nmax →
    PWrites law I L.body (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [w, p, ub] ∧ ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 ∧
        Fp.Apart [w, p, ub] [2 * (d * d), ps.length, 2 * (d * d)])
      (fun μ' => ∃ Ub Tb : Matrix (Fin d) (Fin d) ℂ, HoldsSchurPair w ub Ub Tb μ'.store ∧
        Tb.IsUpperTriangular ∧ IsPerturbedUnitaryPair 1 1 β (1, B) (Ubᴴ, Tb)) φ
```

`HoldsSchurPair a uo U T s := HoldsMatrix a T s ∧ HoldsMatrix uo U s`. Termination companions,
each a `Writes .total … (fun _ => True)` on every tape, are `TerminatingRegularizer`,
`TerminatingSchurCore` and `TerminatingSchurLeaf` (SC6). The core's termination statement also
keeps $\widehat{\mathbf{U}}$ stored. The quantifier lessons of Part II apply. Outer bounds
`nmax`, `S` and `Nmax`, the words, the caps, $\varepsilon$ and $\varphi$ are fixed outside every
`∀` (C1, P11p). A leaf contract covers orders at most `kmax`, never every order (RF1).

The regularizer is a stage, not part of the core, because its contract is the only place where
the class $(B, \Gamma)$ is produced. The core consumes the class; a core for structured input
(Hermitian: $\kappa_V = 1$) can then be paired with the trivial regularizer.

### 2.2 The generic composition theorem (PP2, elaborated)

`schurPipelineWith Nm Reg Red Core : [N, k, np, F, T] (A, P) → (A, U, Fl)` runs eight steps:

1. $s$ := `Nm`.
2. If $s$ is zero (then $\mathbf{A} = 0$, §7): $\widehat{\mathbf{U}} := \mathbf{I}$, flag $0$.
3. Otherwise $\mathbf{A} := \mathrm{fl}(\mathbf{A}/s)$.
4. `Reg` on `P[0]`.
5. $\widehat{\mathbf{U}} := \mathbf{I}$.
6. `Red`.
7. `Core` on `P[nr + 1]`, with the threshold word `P[nr]`.
8. $\mathbf{A} := \mathrm{fl}(s\mathbf{A})$.

```lean
theorem schurPipelineWith_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {Nm Reg Red Core : Impl O Q} {ρ δR φR B Γ εH εC φC : ℝ}
    {k F T : ℕ} {qR qC : List ℝ} (thr : ℝ)
    (hNm : FrobNormEstimateContract ρ Nm I)
    (hReg : RandomRegularizerContract law δR φR B Γ (n + 1) 2 qR Reg I)
    (hRed : HessenbergReducerContract εH Red I)
    (hCore : RandomSchurCoreContract law εC φC (2 * B) (Γ / 2) k F T (n + 1) 4 qC Core I)
    (hρ : ρ ≤ 1 / 4) (hu : 8 * ((n : ℝ) + 1) * u ≤ ρ)
    (hclass : δR + 3 * εH ≤ Γ / (16 * (n + 1) * B)) (hδR : δR ≤ 1 / 2) (hεH : εH ≤ 1 / 8)
    (hεC : εC ≤ 1 / 8)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ thr :: qC) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (schurPipelineWith Nm Reg Red Core).body
      (Env.frame [n + 1, k, (qR ++ thr :: qC).length, F, T] [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A (4 * √((n : ℝ) + 1) * (δR + 2 * εH + 2 * εC) + 8 * (n + 1) * u)
        (3 * (εH + εC) + 8 * (n + 1) * u)) μ} ≤ φR + φC
```

The proof is composition only. `PWrites.seq` adds the failures. The pair relations of `Red` and
`Core` compose by `trans`, and the regularizer's perturbation enters the pair as a second-component
error (the first is $\mathbf{I}$). The class step from `Reg` to `Core` is the merged
`exists_pseudoConditionNumber_le_and_le_norm_sub`, applied to the exact unitary of `Red`'s pair:
a unitary similarity keeps $\kappa_V$ and the gap, and `hclass` absorbs the perturbation. The
scaling to and from $s \approx \|\mathbf{A}\|_{\mathsf F} \le \sqrt{n+1}\|\mathbf{A}\|_2$ gives
the factor $4\sqrt{n+1}$. The constants are as elaborated and are fixed when proved (O6).
`specNorm U ≤ 2` in SC4 holds because $\widehat{\mathbf{U}} = \mathbf{I}$ after step 5 and `Red`
moves it by $\varepsilon_H \le 1/8$.

### 2.3 Work and the certificate (PP4, CT1)

```lean
theorem size_stmtCost_schurPipelineWith_le (Nm Reg Red Core : Impl O Q) (ds : List ℕ)
    {N : ℕ} (hN : ds.head? = some N) :
    Count.size (stmtCost (schurPipelineWith Nm Reg Red Core).body ds) ≤
      Count.size (stmtCost Nm.body [N]) + Count.size (stmtCost Reg.body (ds.take 1 ++ [ds.length])) +
        Count.size (stmtCost Red.body [N]) + Count.size (stmtCost Core.body ds) +
        64 * (N + 1) ^ 2
```

The static count of a `seq` is the sum of its parts, and the glue (scaling, identity, branch) is
$O(N^2)$. CT1 is `schurPipelineAlgorithm`. It is built with `Algorithm.ofWp` from four component
data: the four programs, their termination lemmas, and their static work bounds
$W_\bullet(\mathrm{ds})$. Its work is
`schurPipelineWork W_Nm W_Reg W_Red W_Core ds = W_Nm + W_Reg + W_Red + W_Core + 64(N+1)^2`, so a
swapped component swaps its cost term. Its Accepts postcondition is `SchurOutput`, with the
failure of PP2. CT2 is the instance. No new Ops certificate machinery is needed: the merged
`Algorithm.ofWp` takes a static bound, and PP4 supplies one in summed form. The
`Computation-CertifiedRoutines` note is the precedent for routine certificates; these contracts
follow the merged `…RoutineContract` style instead, because they are probabilistic (`PWrites`).

### 2.4 Which programs meet which contract (a list, not targets)

| contract | now (this stage) | existing, almost | later candidates |
|---|---|---|---|
| SC1 norm | `frobNormRounded` (scalar, NM1) | `Ops.nrm2Sum` (needs `Blas1Op`, not in `SmallEigOp`) | any $\rho$-accurate estimate, e.g. $\max_{ij}\lvert a_{ij}\rvert$ with $\rho = \sqrt{n}$ |
| SC2 regularizer | `ginibreRegularizer` = merged `ginibrePerturb` (RG1) | `ginibrePerturb_pwrites` is this contract at the `smallEigParams` words | real Ginibre, sparse perturbations, the trivial one on Hermitian input |
| SC3 reducer | `hessenbergReduceQ` (rounded Givens + log replay, PR4) | merged `hessenbergReduceLast` (no $\mathbf{Q}$; its backward lemma has $\mathbf{Q}$ existential) | Householder reduction (`Factorizations/Householder`, exact only today), blocked Householder |
| SC4 Schur core | `roundedShQRSchur` (full-mode Part II, SQ2) | merged `roundedShQRSmallEig` meets the spectrum-only variant (O5) | other shifting strategies, spectral bisection (`Eigensolvers/SpectralBisection`) with Schur vectors, Hermitian Jacobi |
| SC5 leaf | `smallSchurProg` (Part III with $\mathbf{U}$, SL4) | merged `smallEigProg` meets the eigenvalue leaf contract only | the full-mode core itself at $k = 1$, a dense $O(k^3)$ QR, any exact small solver as a kernel |

## 3. The pipeline as programs

Buffers are word pairs in column-major order (`HoldsMatrix`). $N = n + 1$.

| step | program | buffers (words) | notes |
|---|---|---|---|
| norm | `frobNormRounded [N] (A) → (S)` | $S$: 1; scratch 3 | `normSq` per entry, rounded sum, `sqrt` |
| scale | `scaleBy [2N^2] (A, R) → (A)` | in place | $R = \mathrm{fl}(1/s)$; `ScalarOp.mul`; exact zeros stay zero |
| regularize | `ginibrePerturb sG [N, 12] (A, P[0]) → (A)` | scratch $2N^2 + 3$ | merged, word 0 = $\gamma$ |
| reduce | `hessenbergReduceQ [N] (A, U) → (A, U)` | log $1 + 5N^2$ (scoped) | `hessenbergReduceLastLog`, then replay on $\mathbf{U}$'s columns |
| core | `roundedShQRSchur sG [N, k, np, F, T] (A, Thr, P, U) → (A, U, Fl)` | §3.2 | full-mode Part II |
| unscale | `scaleBy [2N^2] (A, S)` | in place | |

All of these programs, and the matrix-level rotation programs of PR1–PR2, elaborated with real
`opsImpl%` bodies where noted in §12.

### 3.1 Rotations on views, logs and replay (PR1–PR4)

* **PR1** `rotateRowsOn [ld, r, j0, nc] (A, C, S, T) → (A)` rotates rows $r, r+1$ of a matrix of
  leading dimension `ld` over the columns $j_0, \dots, j_0 + n_c - 1$. `rotateColumnsOn` is the
  column analogue over rows $i_0, \dots$. The merged `rotateRowsWithScratch` and
  `rotateColumnsWithScratch` become wrappers at `[n, k, 0, n]`, with their `_writes_word`
  lemmas as corollaries (S4 pattern). Both new programs elaborated.
* **The log.** A rotation is stored as five words $(r, p_{\mathrm{re}}, p_{\mathrm{im}},
  q_{\mathrm{re}}, q_{\mathrm{im}})$: the two **input entries** of `coefficients`, not the
  coefficient words. The exact unitary of an entry is then `givens r (r+1) (givensCoeffs p q)`.
  This is exactly the exact rotation of the merged
  `specNorm_machineRowRotation_machineColRotation_sub_le`, $49\boldsymbol{u}$, and of G3–G5, so
  those lemmas apply verbatim. A replay recomputes the coefficients with `coefficients`, which on
  a deterministic machine gives the same words, `roundedGivensCoeffs M p q`. A log is the count
  word, then the entries (`logWords`, `HoldsGivensLog lg L s`).
* **PR2** `givensReplayRows [ld, lo, j0, nc, cnt] (Lg, A) → (A)` and `givensReplayColumns`
  replay the first `cnt` entries, shifted by `lo`. Both elaborated.
* **PR3** `hessenbergReduceLastLog [N] (A) → (A, Lg)`: the merged reduction, writing $(c, p, q)$
  before each step. The merged `hessenbergReduceLast` becomes the wrapper with a scratch log.
* **PR4** `hessenbergReduceQ [N] (A, U) → (A, U)`: PR3 with a scoped log, then
  `givensReplayColumns [N, 0, 0, N, c]` on $\mathbf{U}$. This is stage (b). Elaborated.

### 3.2 The full-mode core

`roundedShQRSchur SE SL := solveSchurWith (roundedDecoupleWithLog SE) (seSchurLeaf SL)`. The
Regularize routine stays the eigenvalue program `SE = smallEigProg` (its Ritz values need no
Schur form). The leaf is `SL = smallSchurProg`.

**`solveSchurWith D L : [N, k, np, F, T] (A, Thr, P, U) → (A, U, Fl)`** (SW1). It reuses the
merged stack and helpers: `stackInit`, `rangePop`, `copyToWork`, `bottomScan`, `splitPush`,
`copyToGlobal` and `roundedAbort`. A round pops $(lo, d)$ and copies the block to $\mathbf{W}$.

* **Large block** ($d > k$):
  1. `D` on $\mathbf{W}$, writing the log `Lg` (capacity $G_{\mathrm{dec}}(d)$, O3).
  2. On failure, abort as merged.
  3. Otherwise `bottomScan`, then `copyToGlobal` of $\mathbf{W}$.
  4. Bind $c$ := the count, with bound $G_{\mathrm{dec}}(N)$.
  5. `givensReplayRows [N, lo, lo+d, N-lo-d, c]` on $\mathbf{A}$ (right coupling).
  6. `givensReplayColumns [N, lo, 0, lo, c]` on $\mathbf{A}$ (top coupling).
  7. `givensReplayColumns [N, lo, 0, N, c]` on $\mathbf{U}$.
  8. Write the **exact zero** `lit 0` at the cut entry $(lo+i+1, lo+i)$.
  9. `splitPush`.
* **Leaf** ($d \le k$, inside the guard `ifPos k + 1 - d`, which narrows $d \le k$ for the
  static count):
  1. `L` on $\mathbf{W}$ in place, with $\mathbf{U}_b$ ($2k^2$ words, scratch).
  2. `copyToGlobal`.
  3. Three strided complex products, `matMulOn` (MR1): $\mathbf{A}_{0:lo,R} \leftarrow
     \mathbf{A}_{0:lo,R}\mathbf{U}_b$, $\mathbf{A}_{R,lo+d:} \leftarrow
     \mathbf{U}_b^{\mathsf H}\mathbf{A}_{R,lo+d:}$, $\mathbf{U}_{:,R} \leftarrow
     \mathbf{U}_{:,R}\mathbf{U}_b$, each through a scratch copy of the operand.

The regions rows $R$ × columns $<lo$ and rows $\ge lo+d$ × columns $R$ are never written. They
hold exact zeros from the reduction and from earlier cuts.

**Exactly triangular $\widehat{\mathbf{T}}$.** The invariant (SW2) says that $\mathbf{A}$ is
block upper triangular for the partition `done ++ active`, with exact zero words below the blocks.
Active blocks are upper Hessenberg with exact zeros: from the reduction's zero fill and the
step's `clearBelowSubdiagonal`. Done blocks are upper triangular: by SC5. At the cap, all ranges
are done (or the flag is $1$), so the stored $\mathbf{A}$ is upper triangular (SW6). Unscaling
keeps zeros, because $\mathrm{fl}(s\cdot 0) = 0$ in `StdModel` (MS1:
`StdModel.lit_zero`, `StdModel.mul_zero`).

**The leaf `smallSchurProg sG : [d, nq, T] (Bk, Qw) → (Bk, Ub)`** (SL1) runs as follows. For
$d \le 1$, write $\mathbf{U}_b = \mathbf{I}$ and leave the block. Otherwise:

1. Copy to scratch.
2. `ginibrePerturb`.
3. `hessenbergReduceQ` with $\mathbf{U}_b := \mathbf{I}$.
4. `solveSchurWith (smallEigDecouplerLog sG) trivialSchurLeaf` at $k = 1$, with $\mathbf{U}_b$
   as its $\mathbf{U}$.
5. Copy back.

It is the merged `smallEigProg` with the eigenvalue worklist replaced by the Schur worklist. The
same `solveSchurWith` is used twice. `trivialSchurLeaf` handles $d \le 1$ with
$\mathbf{U}_b = \mathbf{I}$, $\beta = \varphi = 0$ (SL2).

### 3.3 Which merged programs are generalized (S4)

Only the **committed** steps need a log. Trial steps on copies that are discarded do not:
`comptauHalf` and `findRounded` keep the eigenvalue programs. Each row below is a new `…Log`
program writing the extra operand(s) `Lg` (count and entries) and, for trials, a trial log `LgT`
of one degree-$k$ step ($k(N-1)$ entries). The merged name becomes the wrapper that allocates a
scratch log and runs the `…Log` program. Its merged theorem becomes a corollary by one frame
lemma (`PWrites.in_frame`/`Writes.in_frame` through the allocation, RF-pattern of SMALLEIG).

| merged program (file) | generalization |
|---|---|
| `stepWithDiag`, `stepWithDiagInPlace`, `multiStepStable` (StableStep) | each round also copies $(k, p, q)$ to `Lg` |
| `stepComptau` (RoundedFind) | through `multiStepStableLog` |
| `trialStep`, `trialAccept`, `regularizeTrial(s)`, `regularizeDecide` (RoundedRegularizeTrial) | trial log `LgT`; `trialAcceptLog` appends `LgT` at the count (bound read by `bindIdx`) |
| `regularizeWithScratchWith`, `regularizeWith` (RoundedRegularize) | thread `Lg`, `LgT` |
| `shTestStep`, `shPrefix`, `shPotentialAccept`, `shTrial(s)`, `shExc`, `shDecide`, `shStepWithScratch`, `shStep` (RoundedSh, RoundedShTrial, RoundedShExc) | thread |
| `shIterationWithScratchWith`, `shIterationWith` (RoundedIteration) | thread |
| `roundedDecoupleLoopWith`, `roundedDecoupleWith` (RoundedDecouple) | interface `[N, k, np, F, T] (W, P) → (W, Fl, Lg)` |
| `hessenbergReduceLast` (HessenbergReduction) | PR3 |
| `rhess`, `decoupleLast`, `smallEigDecoupler` (SmallEig) | log |
| `rotateRowsWithScratch`, `rotateColumnsWithScratch` (RotationLoops) | PR1 |

**Not generalized; siblings** (O4):

* `solveRoundedWith` and `solveSchurWith`. The eigenvalue worklist's leaves are eigenvalue
  routines (the kernel among them), which cannot produce a Schur block. Its invariant
  (`DeflationInv`, roots) differs from the Schur invariant.
* `smallEigProg` and `smallSchurProg`, for the same reason.

The merged worklist and SmallEig theorems are unchanged. The eigenvalue corollary of the Schur
pipeline (HD3) reproves "spectrum of a nearby matrix" for dense input anyway.

## 4. Numerical analysis

### 4.1 Why the witness must ride on the probabilistic proof (the finding)

The merged step lemma (`stepWithDiag_isStableQRStep`, P1) is deterministic, but its error is
$300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\| + |s|)$. The similarity part of a round is independent
of $s$ ($49\boldsymbol{u}\|\mathbf{Z}\|$). `clearBelowSubdiagonal`, however, removes entries of
size $O(\boldsymbol{u}(\|\mathbf{H}\| + |s|))$: the rotations come from the rounded $\mathbf{H} -
s$ (D3.4, Q4's lesson). Shifts are bounded ($|s| \le C\|\mathbf{H}\|$) only on the good events
of Regularize, Find and Exc inside the merged probabilistic chain. They are never exported. Hence
a deterministic "ghost" invariant could not bound the named backward error on every tape. That
route would add Q-accumulation as non-interfering code and transfer the merged theorems by a new
Ops rule, an XL instrumentation metatheorem. It is rejected (§11 O1 records it). The decoupler
chain is therefore generalized (S4) so that the merged statements' backward relation
`IsPerturbedUnitarySimilar H H' ε` becomes the **witnessed** relation by the log,
`IsPerturbedUnitarySimilarBy (givensLog (n+1) L) H H' ε`. The proofs change in bookkeeping only:
every place that composes by `IsPerturbedUnitarySimilar.trans` composes by the witnessed `trans`
(MW1) and `givensLog_append` (MG1). The probabilistic arguments are untouched.

### 4.2 The relations

* **MW1** `IsPerturbedUnitarySimilarBy V A B ε := HasOrthonormalCols V ∧ ∃ E, specNorm E ≤ ε ∧
  B = Vᴴ * (A + E) * V`, with `isPerturbedUnitarySimilar`, `isPerturbedUnitarySimilar_iff_exists_by`,
  `refl`, `trans` (at $\mathbf{V}\mathbf{W}$), `mono`, and the bridge
  `isPerturbedUnitaryPair_zero_iff`: the pair at first scale $0$ is the witnessed similarity, so
  `BackwardStep` composes it by the merged B6 `isBackwardErrorRel_isPerturbedUnitaryPair`.
  Elaborated.
* **MG1** `givensAt n (r, p, q)` (the identity if $r + 1 \ge n$) and `givensLog n L =
  (L.map fun e => (givensAt n e)ᴴ).prod`, so that conjugating by the entries in order is
  $\mathbf{Z} \mapsto \mathbf{V}^{\mathsf H}\mathbf{Z}\mathbf{V}$. Also
  `hasOrthonormalCols_givensLog` and `givensLog_append`. Elaborated.
* **The global state** is the pair $(\widehat{\mathbf{U}}^{\mathsf H}, \mathbf{T})$ under
  `IsPerturbedUnitaryPair 1 b ε`. From $(\mathbf{I}, \mathbf{A}_1)$: $\widehat{\mathbf{U}}^{\mathsf H} =
  \mathbf{V}^{\mathsf H}(\mathbf{I} + \mathbf{E})$ and $\widehat{\mathbf{T}} =
  \mathbf{V}^{\mathsf H}(\mathbf{A}_1 + \mathbf{F})\mathbf{V}$, so $\|\widehat{\mathbf{U}} -
  \mathbf{V}\| \le \varepsilon$, $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
  \mathbf{I}\| \le 2\varepsilon + \varepsilon^2$, and $\|\mathbf{A}_1 -
  \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\| \le \|\mathbf{F}\| +
  (2\varepsilon + \varepsilon^2)\|\mathbf{A}_1 + \mathbf{F}\|$ (**MW4**, elaborated with
  constants $4\varepsilon$, $3\varepsilon$ at $\varepsilon \le 1/4$).

### 4.3 The full-mode step on a block-triangular matrix (the lift)

Let $\mathbf{T}$ be block upper triangular for $(\{<lo\}, R, \{\ge lo+d\})$, and let the decoupler
return $\mathbf{W}' = \mathbf{V}^{\mathsf H}(\mathbf{T}_{RR} + \mathbf{E}_b)\mathbf{V}$,
$\mathbf{V}$ = `givensLog d L`. With $\widetilde{\mathbf{V}} = \operatorname{diag}(\mathbf{I},
\mathbf{V}, \mathbf{I})$, the exact $\widetilde{\mathbf{V}}^{\mathsf H}\mathbf{T}\widetilde{\mathbf{V}}$
changes only the three blocks $RR$, $(<lo)R$ and $R(\ge lo+d)$. The zero blocks map to zero.
Write $\mathbf{T}'$ for the stored result.

* Block $RR$ is $\mathbf{W}'$.
* Block $(<lo)R$ is the replayed $\mathbf{T}_{(<lo)R}\mathbf{V}$, within
  $\rho_1 = 26\boldsymbol{u}|L|\,\|\mathbf{T}\|$.
* Block $R(\ge lo+d)$ is the replayed $\mathbf{V}^{\mathsf H}\mathbf{T}_{R(\ge lo+d)}$, within
  $\rho_2$ (the same bound).

The replay errors follow from MG2 (one-sided chain: errors along right multiplications by
unitaries add up) and MG3 (G3/G4 generalized to rectangular blocks). Hence

$$\mathbf{T}' = \widetilde{\mathbf{V}}^{\mathsf H}(\mathbf{T} + \widetilde{\mathbf{E}})\widetilde{\mathbf{V}},\quad
  \|\widetilde{\mathbf{E}}\|_2 \le \|\mathbf{E}_b\|_2 + \rho_1 + \rho_2.$$

In Lean this is **MW2**: `IsPerturbedUnitarySimilarBy.fromBlocks₁₁`/`fromBlocks₂₂`, the
witnessed analogues of the merged `exists_fromBlocks₁₁/₂₂` with a computed coupling block
(elaborated), applied twice. **MW3** is the range form on `Fin N` with $[lo, lo+d)$, via
`finSumFinEquiv` and the merged `submatrix_equiv`. The $\widehat{\mathbf{U}}$ replay is the first
component of the pair: $\widehat{\mathbf{U}}' = (\widehat{\mathbf{U}} +
\mathbf{E}_U^{\mathsf H})\widetilde{\mathbf{V}}$ with $\|\mathbf{E}_U\| \le
26\boldsymbol{u}|L|\,\|\widehat{\mathbf{U}}\|$. For a leaf (dense $\mathbf{U}_b$, MW5), the
coupling uses the computed $\mathbf{U}_b = (\mathbf{I} + \mathbf{E}^{\mathsf H})\mathbf{V}_b$
from SC5's pair. Its extra error is $\|\mathbf{T}\|\,\|\mathbf{E}\| + $ the product rounding
(MR1, $(2k + 4)\boldsymbol{u}\|\cdot\|_{\mathsf F}$ terms).

The cut writes $0$ over an entry of modulus at most $c$: an error $c$ by the merged `sub_single`.
Per round, the error is $\varepsilon(N_0) + c + \rho_{\mathrm{rep}}$ (decoupler) or
$\beta + \rho_{\mathrm{leaf}}$ (leaf), with
$\rho_{\mathrm{rep}} = 78\boldsymbol{u}\,G_{\mathrm{dec}}(N)\,N_0$. There are at most $2(n+1)$
rounds, so $\varepsilon_C = 2(n+1)(c + \varepsilon(N_0) + \beta + \rho_{\mathrm{rep}} +
\rho_{\mathrm{leaf}})$. This is the merged worklist's $2(n+1)(c + \varepsilon(N_0) + \beta)$ plus
replay terms that the precision absorbs (item 3 of §1). The global sum over all rounds is
additive (`trans`), not a maximum over disjoint blocks: at most $2(n+1)$ rounds cost the same
factor as the per-level maximum of T6.3.

### 4.4 Forward error of the accumulated product

The library has the vector chain (`norm_toLp_sub_mulVec_le_sum`) and the similarity chain
(`specNorm_sub_mul_mul_conjTranspose_le_sum`), both in `GivensChain`. It lacks the one-sided
matrix chain **MG2** `specNorm_sub_mul_le_sum` (elaborated). **MG4**, in `Eigensolvers/GivensLog`,
is the replay statement: a replay of $L$ on $\mathbf{X}$ is within $26\boldsymbol{u}|L|(1 +
26\boldsymbol{u})^{|L|}\|\mathbf{X}\|$ of $\mathbf{X}\mathbf{V}$ (columns) or
$\mathbf{V}^{\mathsf H}\mathbf{X}$ (rows). Under $26\boldsymbol{u}|L| \le 1/2$ the bound is
$\le 52\boldsymbol{u}|L|\,\|\mathbf{X}\|$, from G4/G5 ($24\boldsymbol{u}$ per rotation, plus
$\le 2\boldsymbol{u}$ for the recomputed coefficients). On $\mathbf{X} = \mathbf{I}$:
$\|\widehat{\mathbf{U}} - \mathbf{V}\| \le 52\boldsymbol{u}|L|$. The total rotation count on
$\widehat{\mathbf{U}}$ is at most $R$ (§1), whence $\varepsilon_U = 64R\boldsymbol{u}$ after the
leaf products.

Log capacity per decoupler call (O3): at most one acceptance per trial site and at most $k + n_0
+ 2$ trial sites per iteration (Regularize's $k$ trials, Sh's test step, the Exc trials). With
$F$ iterations, $G_{\mathrm{dec}}(d) = F(k + n_p + 2)k\,d$. This bound needs no flag reasoning:
`BackwardStep.ite` takes the larger branch.

### 4.5 Error budget

The absolute accuracy in scaled units is $\delta' = \delta/(32\sqrt{n+1})$; the components are:

* $\delta_{\mathrm{scale}} \le 8(n+1)\boldsymbol{u}$, for the norm, the division and the
  multiplication back;
* $\delta_{\mathrm{reg}} = \delta'/2$, by the merged `ginibrePerturb_pwrites` at its $\delta =
  \delta'$;
* $\delta_{\mathrm{hess}} = 50(n+1)^2\boldsymbol{u}\cdot 2 + 52(n+1)^2\boldsymbol{u}$, the
  reduction plus the $\widehat{\mathbf{U}}$ replay;
* $\delta_{\mathrm{qr}} = \delta'$, Part II's absolute error at $\Sigma = 4$, the worklist sum of
  §4.3;
* $\delta_{\mathrm{leaf}} \le \beta_{\mathrm{se}}$ per leaf, inside $\delta_{\mathrm{qr}}$ (the
  forward words give backward error $\le \beta_{\mathrm{se}}$);
* $\delta_{\mathrm{rep}}$, the replay terms, inside the precision.

PP2 converts the sum to $\le \delta\|\mathbf{A}\|_2$ through $s \le (1 + 2(n+1)\boldsymbol{u})
\|\mathbf{A}\|_{\mathsf F} \le 2\sqrt{n+1}\|\mathbf{A}\|_2$.

## 5. Probability and parameters

The parameters depend on $(n, \delta, \varphi)$ only, never on $\mathbf{A}$ (S3: the
normalization makes $\|\mathbf{A}'\|_2 \le 1 + 3\boldsymbol{u} \le 2$):

* `ginibrePerturb` at the words `smallEigParams (n+1) 2 δ' (φ/2) ginibreGapTail
  ginibreConditionTail` (only word 0, $\gamma$ = `smallEigScale δ' (φ/2)`, is read). Its failure is
  $3(\varphi/2)/4$. It splits into the gap $\varphi/8$, the condition $\varphi/8$ and the noise
  norm $\varphi/8$ (RM4–RM6 inside the merged lemma).
* The class: $(B, \Gamma) = (2/t_2, t_1/2)$, $t_1$ = `smallEigGap (n+1) 2 δ' (φ/2)
  ginibreGapTail`, $t_2$ = `smallEigCond …` (the merged `ginibreClass_spec`). After the reducer,
  $(2B, \Gamma/2)$: PP2's `hclass` holds because $\delta_{\mathrm{reg}} + 3\varepsilon_H \le
  \Gamma/(16(n+1)B)$ for these choices. This is the same inequality as Part III's
  `smallEigCoreClass_hessenbergReduceLastWord`, with $\delta' \le t_1/4$ from
  `smallEigScale_mul_noiseLevel`.
* The core at $(2B, \Gamma/2)$, $\Sigma = 4$, $\delta_{\mathrm{qr}} = \delta'$,
  $\varphi_{\mathrm{qr}} = \varphi/2$, with $k$ = `shqrDegree (4 * (2 * B))`, words
  `shqrSmallEigParams n k (2B) (Γ/2) 4 δ' (φ/2) ginibreGapTail ginibreConditionTail`, $F$ =
  `shqrCap`, $T$ = `shqrSmallEigCap`. Inside it, the merged split: $2(n+1)(\varphi_D + \varphi_L)$
  with the decoupler failure and the leaf failure, exactly as T1c/HL2. The leaf contract is SC5 at
  the forward words (SL4), so $\varphi_L$ is the merged `shqrSmallEigFailure`.
* Total: $3\varphi/8 + \varphi/2 \le \varphi$.

Reuse of T1c and HL2: the core theorem SQ2 is HL2's proof. `roundedDecouple_pwrites` and
`roundedLeaf_pwrites` become their log versions (RF6, and SW3 with SC5), and `solveRoundedWith_pwrites`
becomes `solveSchurWith_pwrites` (SW4). The parameter side conditions are the merged
`shqrParams_spec`/`hiBd_smallEigForwardArg`, plus the replay term.

## 6. Cost

The static count multiplies loop bounds with every block order bounded by $N$. As the sizing
study found (`Sizing-SQR-FP-n3.md` §1), that is already $2N$ rounds × $N^2$ per step, with no
amortization. Full mode changes the per-step cost from $d^2$ to $N\cdot d$. The static count
bounds $d \le N$ either way, so the exponent of $N$ is unchanged. The new terms per round:

* the decoupler log replay, $3\,G_{\mathrm{dec}}(N)\cdot N = 3F(k+n_p+2)kN^2$;
* the leaf's three products, $O(N k^2)$ under the guard (`loopSlots` narrows $d \le k$);
* the leaf itself, the merged $(k+1)^4(T+1)^2$-type term.

Over $2N$ rounds this is $O(N^3Fk^2n_p)$. Outside the core: the reducer and its replay $O(N^3)$;
norm, scaling and perturbation $O(N^2)$.

HD6 expects the monomial $\langle c, [3, 5, 1, 1, 2]\rangle$, one power of $k$ above HL5's
$[3, 4, 1, 1, 2]$ from the replay's $k^2$ against the step's $k$. `kernel_rfl` decides it. No
amortization over the deflation tree is needed. A sharper, run-time count (Σ over the tree of
$N d \cdot$ steps, the paper's constant) would need the Accepts route of sizing item G; it is
not planned.

## 7. Edge cases and junk values

* **$\mathbf{A} = 0$.** $\mathrm{fl}(\|\mathbf{A}\|_{\mathsf F}) = 0$ exactly iff $\mathbf{A} =
  0$ (`StdModel`: the rounded sum of squares is $0$ iff every term is; the square root of $0$ is
  $0$). The pipeline branches with `isPos`. On the zero branch it writes $\widehat{\mathbf{U}} =
  \mathbf{I}$ and the flag $0$, and $\widehat{\mathbf{T}} = \mathbf{A} = 0$. Both bounds are
  $0 \le 0$. No division by $0$ (`StdModel.div` says nothing at $0$). The rotation of a zero pair
  (`givensCoeffs 0 0`) is the identity (merged `linearComplex_zero_zero`).
* **Order 1** ($n = 0$): the worklist sends the $1\times1$ block to the leaf (`ifPos k + 1 - d`).
  The leaf takes the $d \le 1$ branch ($\mathbf{U}_b = \mathbf{I}$). The reducer loops over
  `N - 2` columns, zero rounds. `Fin (n + 1)` throughout, so no order-0 junk. In leaves, $d = 0$
  gives empty matrices, triangular and unitary by `Subsingleton`.
* **Nat subtraction.** Replay ranges `N - lo - d` appear only in program dims. In statements,
  ranges are written $lo + d \le N$ (V2). `givensAt` uses `r + 1 < n`, never `n - 1`.
* **Zeros.** `M.lit 0 = 0` and $\mathrm{fl}(s\cdot 0) = 0$ follow from `StdModel` (MS1). The
  merged `hessenbergReduceLast_isPerturbedUnitarySimilar` takes `hzero` as a hypothesis, but it is
  derivable, as its own proof shows (`simpa using hM.lit 0`).
* **Log junk.** The count word is read by `bindIdx` with bound $G$. A junk count fails the run,
  so termination (HD4, SW5) is claimed for the program's own logs. The invariant keeps the count
  $\le G$. Entries with $r + 1 \ge n$ give the identity in `givensAt` and are skipped by the replay
  (no out-of-range write: the row index is bounded by `ld`).
* **Shift-dependence** (§4.1): every chain lemma keeps `IsUpperHessenberg` (Q4's lesson).
* **Positivity**: `uDenseSchur_pos` (elaborated) is needed, else the headline is vacuous
  [PAR1p].
* **Quantifiers**: contract constants are outside the `∀` [C1]. `nmax = n + 1` for the stages of
  the instance.
* **Scale invariance**: $\Sigma$ is fixed ($2$, then $4$) after normalization, so HD5 has no
  $\|\mathbf{A}\|$ term. This is the T2 lesson solved by the algorithm, not by a hypothesis.

## 8. Placement and shared machinery (rule 10)

### 8.1 Files

| file | content |
|---|---|
| `Matrix/Perturbation/UnitarySimilarity.lean` | MW1, MW2, MW3 (beside `exists_fromBlocks₁₁/₂₂`) |
| `Matrix/Perturbation/UnitaryPair.lean` | MW4, MW5 |
| `Matrix/Factorizations/Givens.lean` | MG1 (`givensAt`, `givensLog`) |
| `Matrix/FinitePrecision/GivensChain.lean` | MG2 |
| `Matrix/FinitePrecision/GivensRounded.lean` | MG3 (rectangular generalization of `IsRoundedRowRotation`/`ColRotation`, merged statements unchanged) |
| `Ops/Catalog/Scalar.lean` | MS1 (`StdModel.lit_zero`, `StdModel.mul_zero`) |
| `Eigensolvers/ShiftedQR/RotationLoops.lean` | PR1 |
| `Eigensolvers/GivensLog.lean` (new) | OL1, PR2, MG4 |
| `Eigensolvers/HessenbergReduction.lean` | PR3, PR4 |
| `Eigensolvers/ShiftedQR/{StableStep, RoundedFind, RoundedRegularize*, RoundedSh*, RoundedIteration, RoundedDecouple*}.lean`, `Eigensolvers/SmallEig/{RandomHessenberg, Decouple, Decoupler, DecouplerPrecision}.lean` | RF1–RF10 |
| `Eigensolvers/ShiftedQR/SchurWorklist.lean` (new) | DC1, SW1–SW6 |
| `Eigensolvers/ShiftedQR/RoundedSchur.lean` (new) | SQ1–SQ4 |
| `Eigensolvers/SmallEig/Schur.lean` (new) | SL1–SL5 |
| `Eigensolvers/Schur/Contracts.lean` (new folder) | SC1–SC6 |
| `Eigensolvers/Schur/Pipeline.lean` | PP1–PP4 |
| `Eigensolvers/Schur/Certificate.lean` | CT1, CT2 |
| `Eigensolvers/Schur/Norm.lean` | NM1 |
| `Eigensolvers/Schur/BlockUpdate.lean` | MR1 |
| `Eigensolvers/Schur/Regularizer.lean` | RG1 |
| `Eigensolvers/Schur/Dense.lean` | HD0–HD7 |

**Placement flags.** `HoldsMatrix` (in `ShiftedQR/Storage`) and the rotation programs (in
`ShiftedQR/RotationLoops`) are general stored-matrix and Givens tools that live in the shifted QR
folder. Every new program that needs them (PR1–PR2, NM1, MR1) must therefore sit in
`Eigensolvers`. The intended homes are `Ops/Blas` (NM1, MR1) and `Matrix/FinitePrecision`
(PR1–PR2, MG4), after a move of `HoldsMatrix` and the rotation loops that is not this stage's
(O7).

### 8.2 Vocabulary rows

| object | meaning | Mathlib bridge |
|---|---|---|
| `IsPerturbedUnitarySimilarBy V A B ε` | perturbed similarity by the named unitary | `isPerturbedUnitarySimilar_iff_exists_by`; `isPerturbedUnitaryPair_zero_iff` (no Mathlib notion; searched) |
| `givensAt`, `givensLog` | exact unitary of a rotation log | Mathlib `List.prod`; `givens` |
| `logWords`, `HoldsGivensLog` | stored log | as `HoldsMatrix` |
| `FrobNormEstimateContract`, `RandomRegularizerContract`, `HessenbergReducerContract`, `RandomSchurCoreContract`, `RandomSchurLeafContract`, `RandomLogDecouplingRoutineContract` | stage contracts | `Writes`/`PWrites` |
| `SchurOutput`, `SchurPipelineInput`, `HoldsSchurPair` | input/output memories | as `ShQRSpectrum` |

No Mathlib deviation: the witnessed predicate is a new NLAlib notion next to a NLAlib notion.

### 8.3 Shared machinery

| repeated argument | handled by | status |
|---|---|---|
| merged name kept, program generalized | wrapper + one frame lemma per program (`in_frame`) | SMALLEIG pattern |
| witnessed composition through `BackwardStep` | `isPerturbedUnitaryPair_zero_iff` + merged B6 | new (MW1) |
| a block step lifted with computed coupling | MW2/MW3, used by both worklist uses (top, leaf) and the reducer | new |
| replay error | MG2 + MG3 + MG4, used for coupling, $\widehat{\mathbf{U}}$, the reducer | new |
| one worklist, two uses | `solveSchurWith D L` with log/leaf contracts | new (SW) |
| stages composed | the pair relation + PP2; one theorem for every swap | new |
| class through a unitary stage | merged `exists_pseudoConditionNumber_le_and_le_norm_sub` | merged |
| static count of a composition | PP4 (seq adds) + `stmtWorkMono` + `kernel_rfl` | merged + new |
| `BackwardStep` through frames and allocation | the rule candidates of Part II §7.4 (`BackwardStep.in_frame`, an allocation rule) | **planned first** (OB1), since RF1–RF6 use them about 25 times |

## 9. Target table

The ids, statements and dependencies are in `~/nlalib-harness/pilot/schur-targets.json`. Sizes
are S/M/L/XL; "w" is the wave.

**L1: matrix library (10).**

* MW1 (S, w0): `IsPerturbedUnitarySimilarBy` and its API.
* MW2 (S, w1): the witnessed `fromBlocks₁₁/₂₂`.
* MW3 (M, w2): the range form.
* MW4 (S, w1): the computed form and the exact-unitary form from the pair.
* MW5 (M, w3): the leaf lift with a dense $\mathbf{U}_b$.
* MG1 (S, w0): `givensAt`, `givensLog`, unitarity, append.
* MG2 (S, w0): the one-sided chain.
* MG3 (M, w0): rectangular rounded rotations.
* MS1 (S, w0): the zero lemmas.
* MR1 (M, w0): the strided complex product and its error.

**L2: Ops and programs (9).**

* OL1 (S, w1): the log words.
* OB1 (M, w0): `BackwardStep.in_frame` and the allocation rule.
* PR1 (M, w1): rotations on views, the merged programs as wrappers.
* PR2 (M, w2): replay programs, `_writes_word` and termination.
* MG4 (M, w3): the replay forward error.
* PR3 (M, w2): the reduction with a log, witnessed.
* PR4 (M, w4): `hessenbergReduceQ` meets SC3.
* NM1 (M, w2): `frobNormRounded` meets SC1.
* RG1 (L, w2): `ginibreRegularizer` meets SC2. L because the merged lemma is stated at the fixed
  `smallEigParams` list; it is generalized to any words with word 0 equal to $\gamma$.

**L3: the refactor of the decoupler chain (12).**

* DC1 (S, w2): `RandomLogDecouplingRoutineContract` and the forgetful bridge to the merged
  contract.
* RF1 (L, w2): StableStep log programs and the witnessed chain.
* RF2 (M, w3): `stepComptau`.
* RF3 (L, w3): Regularize trials.
* RF4 (M, w4): Regularize.
* RF5 (L, w4): Sh, Sh trials and Exc.
* RF6 (L, w5): iteration.
* RF7 (L, w6): the decouple loop meets DC1.
* RF8 (M, w3): `rhess`.
* RF9 (M, w3): `decoupleLast`.
* RF10 (L, w4): the SmallEig decoupler meets DC1.
* RF11 (S, w7): the merged certificates' work numerals re-checked; merged statements unchanged.

**L4: the Schur worklist and the stages (17).**

* SC1–SC5 (S, w1, one target): contract definitions.
* SC6 (S, w2): termination contracts and the forgetful bridges.
* SW1 (M, w3): `solveSchurWith`.
* SW2 (M, w4): invariant and measurability.
* SW3 (L, w5): the round lemmas.
* SW4 (L, w6): `solveSchurWith_pwrites`.
* SW5 (M, w5): termination.
* SW6 (S, w5): exact triangularity.
* SL1 (M, w5): `smallSchurProg`.
* SL2 (S, w2): the trivial leaf.
* SL3 (L, w7): Part III's Theorem 1.1 in Schur form.
* SL4 (M, w8): SL meets SC5 at the forward words.
* SL5 (M, w6): termination.
* SQ1 (S, w6): `roundedShQRSchur`.
* SQ2 (L, w9): it meets SC4.
* SQ3 (M, w7): the core's parameters.
* SQ4 (S, w10): the Hessenberg-class Schur headline (analogue of HL2).

**L5: composition, instance and certificate (13).**

* PP1 (M, w2): `schurPipelineWith`.
* PP2 (L, w3): the generic composition.
* PP3 (S, w2): the corollaries.
* PP4 (S, w3): the static count sum.
* CT1 (M, w4): `schurPipelineAlgorithm`.
* HD0 (L, w9): the instance's parameters and side conditions.
* HD1 (S, w10): the dense Schur theorem.
* HD2 (S, w11): the explicit $\varepsilon_U$.
* HD4 (S, w10): termination.
* HD5 (M, w10): the bits.
* HD6 (M, w10): the static count.
* HD7 (M, w11): the polylog work, with `shqrCap_le_log` and `smallEigCap_le_log`.
* CT2 (M, w11): the instance certificate.

**Optional (2).** OPT1 (M): the spectrum-only core contract and the pipeline variant, with the
merged `roundedShQRSmallEig` as a degenerate core. OPT2 (XL, rejected, §4.1): the instrumentation
("ghost") rule.

Totals: 61 planned (S 20, M 28, L 13, XL 0) plus the 2 optional (M 1, XL 1). The generic part
(matrix library, log and replay, contracts, worklist, pipeline, DC1) is 29 of the 61. A stage swap later touches only its own contract proof and the
instance.

## 10. Risks

* The refactor (L3) is the bulk of the work: about 17k merged lines on the path, with the
  statements changed in their backward conjunct. OB1 first; without it the frame proofs repeat
  about 25 times.
* `measurableSet_iterationOutcome` and its siblings gain the log read. The log is a finite read
  of words, and `givensLog` is continuous in them, but this needs checking at RF6.
* The kernel cost of `kernel_rfl` on the larger tree for HD6. HL5's tree already passes; the
  replay adds three loops per round.
* The constants in PP2 and the replay constants are design estimates (O6). The statements are
  loose on purpose, as in Part II's D7.
* The merged `hessenbergReduceLast` proof builds $\mathbf{Q}$ in `hrBound_rows`. PR3 assumes that
  $\mathbf{Q}$ is the product of `givens (givensCoeffs p q)` of the logged pairs; this is to be
  checked first.

## 11. Open decisions (recommendation in bold)

1. **O1, the witness.** **(a) the new predicate `IsPerturbedUnitarySimilarBy`, bridged to the
   pair at scale 0**; or (b) state everything with `IsPerturbedUnitaryPair 0 1`. The ghost route
   is rejected: it needs a deterministic shift bound that does not hold on every tape (§4.1). It
   would become possible only with an all-tape bound on every committed shift, about ten
   shift-producing programs.
2. **O2, the leaf interface.** **(a) a dense $\mathbf{U}_b$** (solver-neutral, needed for
   modularity; cost $O(Nk^2)$ per leaf); or (b) a log (uniform with decouplers, but it ties
   leaves to Givens).
3. **O3, the log capacity.** **(a) $F(k + n_p + 2)k\,d$** (per trial site, no flag reasoning);
   or (b) $Fk\,d$ (at most one acceptance per iteration, which needs the search word in the
   invariant).
4. **O4, worklist and leaf as siblings.** **(a) siblings `solveSchurWith`, `smallSchurProg`
   beside the merged ones**; or (b) a hook-generalized worklist with the merged one as the
   `skip`-hook wrapper (re-proves the merged worklist theorems; no gain, because eigenvalue
   leaves cannot be Schur leaves).
5. **O5, spectrum-only core.** **Optional OPT1**: a contract `RandomSpectrumCoreContract` that
   the merged `roundedShQRSmallEig` meets, with a pipeline variant concluding HD3's eigenvalue
   statement. It is cheap, but no consumer needs it now.
6. **O6, constants.** **State PP2 with the elaborated constants and allow them to move at proof
   time (a one-line amendment)**, as Part II's D7.
7. **O7, placement.** **Keep the new rotation and log programs in `Eigensolvers` with flags**;
   moving `HoldsMatrix` and `RotationLoops` to `Ops/Blas` and `Matrix/FinitePrecision` is a
   separate cleanup PR.

## 12. Elaboration (scratch, not in the repo)

File `/home/ubuntu/.claude/jobs/59127b8e/tmp/schur-elab/SchurStatements.lean`, checked with
`lake env lean` against the built worktree (`design/schur`): **no errors**. Proofs are `sorry`.
Programs with real `opsImpl%` bodies:

* `rotateRowsOn` and `rotateColumnsOn`;
* `givensReplayRows` and `givensReplayColumns` (a `bindIdx` inside a counted loop, offsets
  `1 + 5 * e`);
* `hessenbergReduceQ`.

The other programs are stubs: `hessenbergReduceLastLog`, `schurPipelineWith`, the instance
components. Elaborated:

* MW1 (with `trans` and the pair bridge), MW2, MW4;
* MG1 (`givensAt`, `givensLog` with real bodies), MG2;
* `logWords`, `HoldsGivensLog`;
* SC1–SC5 and DC1, with real bodies;
* PP2 and PP3 (both corollaries), PP4;
* HD1, HD2, HD4, HD5, HD6 and `uDenseSchur_pos`.

Fixes from elaboration: the pair relation needed `Matrix.Perturbation.UnitaryPair` imported
explicitly. The scalar `nrm2Sum` needs `Blas1Op`, which `SmallEigOp` lacks, so NM1 is a
scalar-only program.

## 13. Material

The Part I intro (`src1/intro.tex:18, 176`), Part II and III LaTeX, the two predecessor notes,
`Corrections-BGS-Ordered.md` (N7, the bottom-$k$ cut, kept; G16/D3.4/Q4, the shift-dependence of
the step, which drives §4.1), `Sizing-SQR-FP-n3.md` (static $n^3$, guard narrowing), the merged
Lean listed in §3.3, `Computation-CertifiedRoutines.md` (routine-certificate precedent), Higham
2002 Ch. 19 (Givens error, accumulation), Watkins 2008 (Schur vectors by accumulation).
