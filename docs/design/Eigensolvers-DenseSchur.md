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

Revised after the design review (Fable, `Review-Fable-SCHUR-Design.md`, "revise, then approve
for skeleton") and the maintainer's decisions; §14 lists every change and the reasons.

* **Headline (§1).** For every $\mathbf{A} \in \mathbb{C}^{(n+1)\times(n+1)}$, $0 < \delta \le 1$
  and $0 < \varphi \le 1$, at a precision $\boldsymbol{u} \le \boldsymbol{u}_0(n,\delta,\varphi)$
  with $\log_2(1/\boldsymbol{u}_0) = O(L^4\log^2 L)$, $L = \log_2(4(n+1)/(\delta\varphi))$, the
  program `denseSchur` stores, except with probability at most $\varphi$, a failure word $0$ and
  words $\widehat{\mathbf{U}}$, $\widehat{\mathbf{T}}$ with $\widehat{\mathbf{T}}$ exactly upper
  triangular and $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2
  \le \delta\|\mathbf{A}\|_2$. **On every tape**, $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
  \mathbf{I}\|_2 \le 58R\boldsymbol{u} \le \delta$, with $R(n,\delta,\varphi)$ an explicit static
  bound on the rotations (and rotation-equivalents) accumulated on $\widehat{\mathbf{U}}$. There is
  no hypothesis on $\mathbf{A}$; exact naturals are needed only up to $n + 1$. Static count
  $c(n+1)^3(k+1)^5(n_q+1)(F+1)(T+1)^2 = O(n^3L^p)$, $p \approx 12$.
* **Modular (§2, §14).** Four pipeline stages (norm estimate, regularizer, Hessenberg reducer,
  Schur core), each a routine parameter with a contract, one generic composition theorem
  (errors, failures and static counts add). Inside the core, one **generic deflation worklist**
  with three routine parameters (decoupler, leaf, **hook**); the merged eigenvalue programs are
  its skip-hook instance and keep their statements, costs and precision; the Schur core is the
  tracking-hook instance. Rotations go through a reusable **Givens sink** layer (skip sink: no
  log, zero cost; slot sink: a self-describing slotted static log).
* **Why the merged chain changes (§4.1, §14.2).** A Schur form needs the backward error with the
  unitary *named*; the only probability bounds for it are inside the merged chain (the shift
  bounds are hypotheses of the deterministic lemmas, established only within event sets). So the
  committed chain is refactored **in place** to take a sink and to state its witness; the merged
  names are the skip instances.
* **Size (§9).** 70 targets (S 21, M 35, L 13, XL 1), waves 0–11: L1 matrix library 14, L2 log
  layer and stage programs 10, L3 the in-place refactor of the decoupler chain 13, L4 the generic
  worklist, hooks, leaves and the core 21, L5 composition, instance and certificates 12. The
  merged worklist, Part III and Part II headline theorems are re-derived as skip instances
  (GW6, SL6, SQ5).
* **Decisions (§11):** all resolved by the maintainer; B5 (merged certificate numerals change) is
  approved and listed in §14.4.

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
      (SchurOutput a uo f A δ (58 * denseSchurRotations n δ φ * u)) μ} ≤ φ
```

Companions (same hypotheses unless said):

* **HD4** `denseSchur_terminates`: on every tape and every input, with only
  `IsExactNatLit id Mch (n + 1)`, the run is total and `SchurOrth uo (58 * denseSchurRotations n δ φ * u)`:
  $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\| \le 58R\boldsymbol{u}$ whatever
  the tape (review B2: the orthogonality is shift-free).
* **PP3** corollaries for any `SchurOutput` (eigenvalue listing of $\mathbf{A} + \mathbf{E}$ by
  `HasOrthonormalCols.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul`; an exact
  unitary $\mathbf{V}$ within $e_U$ of $\widehat{\mathbf{U}}$ with $\mathbf{A} + \mathbf{E} =
  \mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H}$, from `IsTrackedUnitarySimilar.exists_eq_mul_mul_conjTranspose`).
* **HD5** `logb_inv_uDenseSchur_le`: $\log_2(1/\boldsymbol{u}_0) \le c_1L^4(\log_2L + 1)^2 + c_2$
  (review B3: $k = \Theta(L\log L)$ in the merged $e_1kL + e_2k^2L^2 + e_3$).
* **HD6** `denseSchur_work_le`: static count $\le c(n+1)^3(k+1)^5(n_q+1)(F+1)(T+1)^2$
  (`kernel_rfl`); **HD7** the polylog form at `denseSchurDims`, $C(n+1)^3L^p$ with $p$ about $12$
  (the paper's is $2$), said in the docstring.
* **CT2** `denseSchurAlgorithm`, `denseSchur_algorithm_measureReal_not_accepts_le`: one counted
  run, work `schurPipelineWork`, the sum of the components' work polynomials.

**The precision threshold**, `uDenseSchur n δ φ`, is the minimum of six terms. Write
$\delta' = \delta/(32\sqrt{n+1})$ and $(B, \Gamma) = (2/t_2, t_1/2)$, $t_1, t_2$ =
`smallEigGap/Cond (n+1) 2 δ' (φ/2)` at the proved tails (§5):

1. `uSmallEigReduce (n+1) 2 δ' (φ/2) ginibreGapTail ginibreConditionTail` (the regularizer);
2. $1/(100(n+1)^2)$ and $\delta'/(64\cdot 50(n+1)^2)$ (the reducer's $\varepsilon_T$);
3. **the class term (review B1)**: $3\cdot 50(n+1)^2\boldsymbol{u}\cdot 3 \le \Gamma/(16(n+1)B)$,
   i.e. $\boldsymbol{u} \le t_1t_2/(7200(n+1)^3)$, so that the reducer's error keeps the class;
4. `uShQRSchur n k (2B) (Γ/2) 4 δ' (φ/2)`: the merged `uShQRSmallEig` and the replay term;
5. $\delta/(192R)$ (the orthogonality; it also gives $24R\boldsymbol{u} \le 1/8$);
6. $1/(32(n+1))$ (the norm estimate, scaling, PP2's glue $8(n+1)\boldsymbol{u} \le 1/4$).

**$\varepsilon_U$.** Each replayed rotation moves $\widehat{\mathbf{U}}$ by at most
$24\boldsymbol{u}\|\widehat{\mathbf{U}}\|$ from its exact product (the merged one-sided bound inside
`specNorm_machineRowRotation_machineColRotation_sub_le`, recomputed coefficients included). Over
$R$ rotations, $\|\widehat{\mathbf{U}} - \mathbf{V}\| \le (1 + 24\boldsymbol{u})^R - 1 \le
24R\boldsymbol{u} + (24R\boldsymbol{u})^2 \le 27R\boldsymbol{u}$ (merged `one_add_pow_sub_one_le`,
$24R\boldsymbol{u} \le 1/8$), so $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|
\le 2\cdot27R\boldsymbol{u} + (27R\boldsymbol{u})^2 \le 58R\boldsymbol{u}$, and under term 5 this is
$\le 58\delta/192 < \delta$. $R$ = `denseSchurRotations n δ φ` $= (n+1)^2 + 2(n+1)\bigl(F(k+n_q+2)k(n+1)
+ R_{\mathrm{leaf}}(k, T) + 2k(k+2)\bigr)$; the last term counts the leaf's dense products as
rotation-equivalents (MR1), $R_{\mathrm{leaf}}$ the leaf's own replays.

## 2. Modularity: stages, contracts, the generic pipeline

The maintainer's requirement is "make stuff modular so we can swap in other stuff as we need".
Each pipeline stage is a routine parameter `… : Impl O Q`, as SMALLEIG's `SE` (decision D2), and
has a contract named in the stage-neutral library style. There are **four pipeline stages** (norm
estimate, regularizer, Hessenberg reducer, Schur core) and, inside the shifted QR core, **three
worklist routines** (decoupler, leaf, hook, §3.2). The contracts state the stored accumulator
through one relation, the tracked similarity `IsTrackedUnitarySimilar εU εT` (MW6, two errors,
review B2): stages compose by its `trans`, which adds both errors, and the computed-form
conclusion is one lemma at the end (MW4). The single-ε pair relation of the first draft is
dropped from the contracts: it forced $e_U \approx \delta$.

### 2.1 The contracts (Lean, elaborated)

The files are under `Eigensolvers/Schur/` (new folder). The contracts mention no shifted QR.

```lean
/-- SC1 (stage e, review S2: two-sided): a norm estimate `c₁‖A‖_F ≤ x ≤ c₂‖A‖_F`,
deterministic. `[N] (A) → (S)`. -/
def FrobNormEstimateContract (c₁ c₂ : ℝ) (Nm : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a s : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A : Matrix (Fin N) (Fin N) ℂ),
    HoldsMatrix a A μ.store → μ.Live [a, s] → s.2 + 1 ≤ μ.store.len s.1 →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock s.1 s.2 1) →
    Writes .total I tape Nm.body (Env.frame [N] [a, s]) (Store.inBlock s.1 s.2 1)
      (fun μ' => ∃ x : ℝ, μ'.store.get s.1 s.2 = some x ∧ c₁ * frobNorm A ≤ x ∧
        x ≤ c₂ * frobNorm A) μ

/-- SC2 (stage a): a randomized regularizer into the class `C` (review S2: any class
predicate). `[N, np] (A, P) → (A)`. -/
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

/-- The stored pair `(Û, T)` at `(a, uo)`. -/
def HoldsSchurPair {n : ℕ} (a uo : ℕ × ℕ) (U T : Matrix (Fin n) (Fin n) ℂ) (s : Store ℝ) :
    Prop :=
  HoldsMatrix a T s ∧ HoldsMatrix uo U s

/-- SC3 (stage b, review B2: two errors): a Hessenberg reducer with an accumulated unitary,
errors `εU` (absolute, for `‖U‖ ≤ 2`) and `εT ‖A‖`; deterministic. `[N] (A, U) → (A, U)`. -/
def HessenbergReducerContract (εU εT : ℝ) (Red : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a uo : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A U : Matrix (Fin N) (Fin N) ℂ),
    specNorm U ≤ 2 → HoldsSchurPair a uo U A μ.store → μ.Live [a, uo] →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N))) →
    Writes .total I tape Red.body (Env.frame [N] [a, uo, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => ∃ U' H : Matrix (Fin N) (Fin N) ℂ, HoldsSchurPair a uo U' H μ'.store ∧
        IsUpperHessenberg H ∧ IsTrackedUnitarySimilar εU (εT * specNorm A) U A U' H) μ

/-- SC4 (stage c, review S2: opaque dims `cd`, class `C'`): a randomized Schur core on upper
Hessenberg input: except with probability `φ`, the flag is `0`, the matrix is upper triangular
and tracked with `(εU, εT)`. `(n+1) :: np :: cd` dims, `(A, P, U) → (A, U, Fl)`; any
threshold is in the core's own words. -/
def RandomSchurCoreContract (law : ℕ → Measure ℝ) (εU εT φ : ℝ)
    (C' : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop) (cd : List ℕ) (nmax : ℕ)
    (S : ℝ) (ps : List ℝ) (Core : Impl O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    n + 1 ≤ nmax → IsUpperHessenberg H → specNorm H ≤ S → specNorm U ≤ 2 → C' H →
    PWrites law I Core.body (Env.frame ((n + 1) :: ps.length :: cd) [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => HoldsSchurPair a uo U H μ.store ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.Live [a, p, uo, f] ∧
        Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1])
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store ∧ Tm.IsUpperTriangular ∧
        IsTrackedUnitarySimilar εU εT U H U' Tm) φ

/-- SC6 (review B2): the all-tape companion of a core: total, and the accumulator stays within
`εU` of `U V` for an exact unitary `V`, whatever the tape. -/
def TerminatingSchurCore (εU : ℝ) (cd : List ℕ) (ps : List ℝ) (Core : Impl O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), specNorm U ≤ 2 →
    HoldsSchurPair a uo U H μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [a, p, uo, f] →
    Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1] →
    Writes .total I tape Core.body (Env.frame ((n + 1) :: ps.length :: cd) [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ U' Tm V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store ∧ HasOrthonormalCols V ∧
        specNorm (U' - U * V) ≤ εU) μ
```

The tracked relation (MW6, review B2) carries two errors: `IsTrackedUnitarySimilar εU εT U A U' A'`
is `∃ V, IsPerturbedUnitarySimilarBy V A A' εT ∧ specNorm (U' - U * V) ≤ εU`; it composes by
adding both. The class is a predicate `C`/`C'` (review S2); the instance is
`IsConditionedDiagonalizable B Γ` (MC1). The core's dims are opaque (`(n+1) :: np :: cd`); a
threshold word lives among its own words. The leaf (SC5) and the decoupler (DC1) are not
pipeline stages but worklist routines (§3.2). The quantifier lessons of Part II apply. Outer bounds
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
/-- PP2 (revised after review B1, B2, S2, S4): **the generic composition theorem**. For ANY
norm estimate, regularizer (into `C`), reducer and Schur core (from `C'`) meeting their
contracts, with the class transfer `hCC'` through the reducer's similarity, the pipeline outputs
a Schur pair with the summed errors, except with probability `φR + φC`. -/
theorem schurPipelineWith_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {c : ℕ} {Nm Reg Red Core : Impl O Q}
    {c₁ c₂ δR φR εHU εHT εCU εCT φC : ℝ} {cd : List ℕ} (hcd : cd.length = c)
    {qR qC : List ℝ}
    {C C' : ∀ {m : ℕ}, Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Prop}
    (hNm : FrobNormEstimateContract c₁ c₂ Nm I)
    (hReg : RandomRegularizerContract law δR φR C (n + 1) (2 / c₁) qR Reg I)
    (hRed : HessenbergReducerContract εHU εHT Red I)
    (hCore : RandomSchurCoreContract law εCU εCT φC C' cd (n + 1) (4 / c₁) qC Core I)
    (hCC' : ∀ (A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C A →
      IsPerturbedUnitarySimilarBy V A H (εHT * (2 / c₁ + δR)) → C' H)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂) (hu : 8 * ((n : ℝ) + 1) * u ≤ 1 / 4)
    (hδR : δR ≤ 1 / c₁) (hεHT : εHT ≤ 1 / 8) (hεU : εHU + εCU ≤ 1 / 16)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (qR ++ qC) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (schurPipelineWith c Nm Reg Red Core).body
      (Env.frame ((n + 1) :: qR.length :: qC.length :: cd) [a, p, a, uo, f]) (schurFp n a uo f)
      (SchurOutput a uo f A
        (2 * c₂ * √((n : ℝ) + 1) * (δR + 3 * εHT / c₁ + εCT + 8 * (εHU + εCU) / c₁)
          + 8 * (n + 1) * u)
        (2 * (εHU + εCU) + (εHU + εCU) ^ 2)) μ} ≤ φR + φC := sorry
```

The proof is composition only. `PWrites.seq` adds the failures. The tracked relations of `Red` and
`Core` compose by `trans`, and the regularizer's perturbation enters the pair as a second-component
error (the first is $\mathbf{I}$). The class step from `Reg` to `Core` is the hypothesis `hCC'` (a class transfer through the
reducer's witnessed similarity); at the instance it is MC1, and only the reducer's error enters
(review B1: the regularizer's perturbation is already inside `C (A + E)`). The
scaling to and from $s \approx \|\mathbf{A}\|_{\mathsf F} \le \sqrt{n+1}\|\mathbf{A}\|_2$ gives
the factor $4\sqrt{n+1}$. The constants are as elaborated and are fixed when proved (O6).
`specNorm U ≤ 2` in SC3/SC4 holds because $\widehat{\mathbf{U}} = \mathbf{I}$ after step 5 and `Red`
moves it by $\varepsilon_H \le 1/8$.

### 2.3 Work and the certificate (PP4, CT1)

```lean
/-- PP4 (review S2: dims fixed): the static count of the pipeline is the sum of the components'
counts plus `64 (N + 1)²`. -/
theorem size_stmtCost_schurPipelineWith_le (c : ℕ) (Nm Reg Red Core : Impl O Q)
    (N nr nq : ℕ) (cd : List ℕ) :
    Count.size (stmtCost (schurPipelineWith c Nm Reg Red Core).body (N :: nr :: nq :: cd)) ≤
      Count.size (stmtCost Nm.body [N]) + Count.size (stmtCost Reg.body [N, nr]) +
        Count.size (stmtCost Red.body [N]) + Count.size (stmtCost Core.body (N :: nq :: cd)) +
        64 * (N + 1) ^ 2 := sorry
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
| SC1 norm | merged `ShiftedQR.matrixNorm` (NM1: its `StdModel` bounds) | `Ops.nrm2Sum` (needs `Blas1Op`) | any two-sided estimate, e.g. $\max_{ij}\lvert a_{ij}\rvert$ ($c_1 = 1/(n+1)$, $c_2 = 1$) |
| SC2 regularizer | `ginibreRegularizer` = merged `ginibrePerturb` (RG1) | `ginibrePerturb_pwrites` is this contract at the `smallEigParams` words | real Ginibre, sparse perturbations, the trivial one on Hermitian input |
| SC3 reducer | `hessenbergReduceQ` (rounded Givens + log replay, PR4) | merged `hessenbergReduceLast` (no $\mathbf{Q}$; its backward lemma has $\mathbf{Q}$ existential) | Householder reduction (`Factorizations/Householder`, exact only today), blocked Householder |
| SC4 Schur core | `roundedShQRSchur` (full-mode Part II, SQ2) | merged `roundedShQRSmallEig` meets the spectrum-only variant (O5) | other shifting strategies, spectral bisection (`Eigensolvers/SpectralBisection`) with Schur vectors, Hermitian Jacobi |
| SC5 leaf (worklist routine) | `smallEigProgWith trackingHook` (SL4) | merged `smallEigProg` = the skip instance, eigenvalue output only | the full-mode core itself at $k = 1$, a dense $O(k^3)$ QR, any exact small solver as a kernel |

## 3. The pipeline as programs

Buffers are word pairs in column-major order (`HoldsMatrix`). $N = n + 1$.

| step | program | buffers (words) | notes |
|---|---|---|---|
| norm | merged `ShiftedQR.matrixNorm [N, N] (A) → (S)` | $S$: 1 | `RoundedScalarBlas.nrm2` (NM1: its `StdModel` bounds) |
| scale | `scaleBy [2N^2] (A, R) → (A)` | in place | $R = \mathrm{fl}(1/s)$; `ScalarOp.mul`; exact zeros stay zero |
| regularize | `ginibrePerturb sG [N, 12] (A, P[0]) → (A)` | scratch $2N^2 + 3$ | merged, word 0 = $\gamma$ |
| reduce | `hessenbergReduceQ [N] (A, U) → (A, U)` | log $1 + 5N^2$ (scoped) | `hessenbergReduceLastLog`, then replay on $\mathbf{U}$'s columns |
| core | `roundedShQRSchur sG [N, k, np, F, T] (A, Thr, P, U) → (A, U, Fl)` | §3.2 | full-mode Part II |
| unscale | `scaleBy [2N^2] (A, S)` | in place | |

All of these programs, and the matrix-level rotation programs of PR1–PR2, elaborated with real
`opsImpl%` bodies where noted in §12.

### 3.1 The Givens log layer (GL1, GL2, PR1–PR4)

A reusable layer, in `Matrix/FinitePrecision/GivensLog.lean` after the O7 move:

* **Entries** `GivensEntry = ℕ × ℂ × ℂ`: the plane $r$ (rows/columns $r, r+1$) and the two
  **inputs** $(p, q)$ of `coefficients`. The exact unitary of an entry is
  `givens r (r+1) (givensCoeffs p q)`, exactly the rotation of the merged
  `specNorm_machineRowRotation_machineColRotation_sub_le` and G3–G5; `givensLog n L` (MG1) is the
  product. A replay recomputes the coefficients (`coefficients`, the same words on a
  deterministic machine).
* **Storage** `HoldsSlottedLog lg w L`: slots of $1 + 5w$ words, a valid word, then $w$
  self-describing entries $(r, p_{\mathrm{re}}, p_{\mathrm{im}}, q_{\mathrm{re}}, q_{\mathrm{im}})$; the
  log is the valid slots in order (`slotEntries`). **No count word** (review B4): the layout is
  static, the plane word is an exact natural $\le n+1$ (`hNat`), and the validity test is `isPos`.
* **Sinks** (GL2): a producer of rotations calls a sink routine `Wr` for each committed rotation
  (`[ld, j, i] (E, Lg) → (Lg)`: entry $i$ of slot $j$) and `Vd` when a slot is accepted.
  `IsGivensSink Inv Fp Wr I` says the sink moves `Inv L` to `Inv (L ++ [x])` inside `Fp`. Two
  instances: **`skipSink`** (`Inv = True`, empty footprint, zero work) and **`slotSink`**
  (`Inv = HoldsSlottedLog`). Producers are generic in the sink, so an eigenvalue-only run pays
  nothing and a Schur run records.
* **Replay** (PR2) `givensReplayRows/Columns [ld, lo, j0, n, ns, w] (Lg, A) → (A)`: valid slots in
  order, plane by `bindIdx ≤ ld`, rotation by PR1 `rotateRowsOn`/`rotateColumnsOn` on a strided
  view (the merged `rotateRowsWithScratch` becomes the instance `[n, k, 0, n]`). MG4: each
  replayed rotation moves its operand by $\le 24\boldsymbol{u}\|\cdot\|$ from the exact product, on
  every tape.
* **PR3** `hessenbergReduceLastWith Wr`: the merged reduction, in place, with a sink;
  `hessenbergReduceLast` is the skip instance, and its merged theorem a corollary of the witnessed
  one (`Q = givensLog` of its entries, keeping $\mathbf{Q}\mathbf{e}_N = \mathbf{e}_N$; review §2 item 4:
  checked first against `hrBound_rows`). **PR4** `hessenbergReduceQ`: reduce with a slot sink, then
  replay on $\mathbf{U}$'s columns; meets SC3 with $(\varepsilon_U, \varepsilon_T) = (27N^2\boldsymbol{u}, 50N^2\boldsymbol{u})$.

All of these elaborated (§12).

### 3.2 One generic deflation worklist with a hook (maintainer O4(b))

`solveDeflationWith D L Hk : [N, k, np, F, T] (A, Thr, P, X) → (A, X, Out, Fl)` (GW1) is the merged
worklist with three routine parameters:

* **decoupler** `D : [d, k, np, F, T] (W, P) → (W, Fl, Lg)`, generic in its sink; contract DC1:
  the merged decoupler contract plus `∃ L, Inv L ∧ IsPerturbedUnitarySimilarBy (givensLog L) H H' ε`
  (with the skip sink, `Inv = True` and the merged `∃ U` form is the corollary);
* **leaf** `L : [d, np, T] (Bk, P) → (Bk, Ev, Ub)` with one generic contract
  `RandomLeafRoutineContractWith Post` (GW7): `Ev` lists the spectrum of $\mathbf{B} + \mathbf{F}$, and
  `Post` adds what the leaf promises; the merged eigenvalue leaf contract is the instance with
  `Post = True` (Bk, Ub untouched), the Schur leaf contract the instance with
  `Tb` upper triangular, `Ev = diag Tb`, `IsTrackedUnitarySimilar εU εT 1 B Ub Tb`;
* **hook** `Hk`, run after each successful decoupler call (`[N, lo, d, …] (Lg, A, X) → (A, X)`) and
  after each leaf (`[N, lo, d] (W, Ub, A, X) → (A, X)`). Its contract (GW2, `DeflationHook`) is an
  invariant `Inv H₀ e μ` and per-round extra errors `ρ` (decoupler, as a function of the log size
  and the norm), `ρL` (leaf), plus its static work. **`skipHook`**: `Inv = True`, `ρ = ρL = 0`, zero
  work.

**The generic theorem** GW4 `solveDeflationWith_pwrites` (elaborated) concludes the **merged**
conclusion (eigenvalues of $\mathbf{H} + \mathbf{E}$, $\|\mathbf{E}\| \le 2(n+1)(c + \varepsilon(N_0) + \beta)$)
**and** `hk.Inv H (2(n+1)(c + ε N₀ + β + ρ + ρL))`, with failure $2(n+1)(\varphi_D + \varphi_L)$
and the merged precision hypotheses only (the hook's precision needs live in its own `ρ`). At
the skip hook and skip sinks it is the merged `solveRoundedWith_pwrites`, with its current
statement, cost and precision (GW6); the merged program `solveRoundedWith D L` is the instance
`solveDeflationWith D L skipHook` (wrapper).

**The tracking hook** `trackingHook` (SH1, SH2), `X` = $\widehat{\mathbf{U}}$:

* after a decoupler: `givensReplayRows [N, lo, lo+d, N-lo-d, …]` (right coupling),
  `givensReplayColumns [N, lo, 0, lo, …]` (top coupling) and `[N, lo, 0, N, …]` ($\widehat{\mathbf{U}}$),
  then the **exact zero** `lit 0` at the cut entry;
* after a leaf: the three strided products with $\mathbf{U}_b$ (MR1) under the guard $d \le k$.

Its invariant: the tracked relation from $(\mathbf{U}_0, \mathbf{H}_0)$; $\mathbf{A}$ block upper
triangular for `done ++ active` with exact zero words below; active blocks Hessenberg; done blocks
upper triangular. Hence the final $\widehat{\mathbf{T}}$ is exactly upper triangular (zeros never
written; `StdModel.lit_zero`, `mul_zero`). $\rho = 78\boldsymbol{u}\,m\,N_0$ for a log of $m$ entries.

**The leaf, generic too** (SL1): Part III's program becomes `smallEigProgWith Hk` (copy,
`ginibrePerturb`, `hessenbergReduceLastWith`, `solveDeflationWith (smallEigDecouplerWith) copyLeaf Hk`
at $k = 1$); the merged `smallEigProg` is the skip instance (its theorems re-derived, SL6), and the
Schur leaf `smallSchurProg = smallEigProgWith trackingHook` with the slot sink, writing `Bk`,
`Ub` and `Ev`.

**The core** (SQ1): `roundedShQRWith SE L Hk := solveDeflationWith (roundedDecoupleWith SE) (seLeaf L) Hk`;
merged `roundedShQRWith SE` is the skip instance; `roundedShQRSchur` the tracking instance with the
Schur leaf. Regularize keeps the eigenvalue program `SE` (Ritz values need no Schur form).

### 3.3 The in-place refactor of the decoupler chain

Only committed rotations need recording, but the cleanest structure (maintainer: best final
proofs) gives every rotation-producing program a sink parameter and states every backward
conclusion with its witness; the merged name is the skip-sink instance, the merged theorem a
one-line corollary through `isPerturbedUnitarySimilar_iff_exists_by`. Find's trial steps use
the skip sink. Trials write directly into their own slot and acceptance validates it (no trial
log buffer, no copy). The slot layout per decoupler call: $F$ iterations × $(k + n_q + 2)$ trial
sites × $k\,n$ entries (O3); the reduction: $N$ slots of $N - 1$ entries.

| merged program (file) | change |
|---|---|
| `stepWithDiag`, `stepWithDiagInPlace`, `multiStepStable` (StableStep) | sink parameter; chain lemma names its $\mathbf{Q}$s |
| `stepComptau` (RoundedFind) | sink |
| `trialStep`, `trialAccept`, `regularizeTrial(s)`, `regularizeDecide` (RoundedRegularizeTrial) | trial writes its slot, accept validates |
| `regularizeWithScratchWith`, `regularizeWith` (+ termination) | thread the sink |
| `shTestStep`, `shPrefix`, `shPotentialAccept`, `shTrial(s)`, `shExc`, `shDecide`, `shStep` (+ termination) | thread |
| `shIterationWith`, `roundedDecoupleLoopWith`, `roundedDecoupleWith` (+ routine, termination) | thread; outcome with the witness |
| `hessenbergReduceLast`, `rhess`, `decoupleLast`, `smallEigDecoupler` | sink |
| `solveRoundedWith`, `smallEigProg`, `roundedShQRWith` | instances of the generic programs (skip hook) |
| `rotateRowsWithScratch`, `rotateColumnsWithScratch` | instances of PR1 |

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
* **The global state** is the tracked relation (MW6) `IsTrackedUnitarySimilar εU εT 1 A₁ Û T̂`:
  an exact unitary $\mathbf{V}$ with $\widehat{\mathbf{T}} = \mathbf{V}^{\mathsf H}(\mathbf{A}_1 + \mathbf{F})\mathbf{V}$,
  $\|\mathbf{F}\| \le \varepsilon_T$, and $\|\widehat{\mathbf{U}} - \mathbf{V}\| \le \varepsilon_U$. Then
  $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\| \le 2\varepsilon_U + \varepsilon_U^2$ and
  $\|\mathbf{A}_1 - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\| \le \varepsilon_T +
  (2\varepsilon_U + \varepsilon_U^2)(\|\mathbf{A}_1\| + \varepsilon_T)$ (**MW4**, elaborated). The two errors
  stay apart: $\varepsilon_U$ is a deterministic $O(R\boldsymbol{u})$, $\varepsilon_T$ the probabilistic
  backward error (review B2).

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
$\varepsilon_U$ part of the tracked relation: $\|\widehat{\mathbf{U}}' - \widehat{\mathbf{U}}\widetilde{\mathbf{V}}\| \le
24\boldsymbol{u}|L|(1+24\boldsymbol{u})^{|L|}\|\widehat{\mathbf{U}}\|$ (MG4). For a leaf (dense $\mathbf{U}_b$, MW5), the
coupling uses the computed $\mathbf{U}_b = (\mathbf{I} + \mathbf{E}^{\mathsf H})\mathbf{V}_b$
from SC5's tracked relation. Its extra error is $\|\mathbf{T}\|\,\|\mathbf{E}\| + $ the product rounding
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

The library has the vector and similarity chains in `GivensChain`; MG2 adds the one-sided matrix
chain. MG4: each replayed rotation is within $24\boldsymbol{u}\|\mathbf{X}\|$ of the exact one (the
merged one-sided bound, coefficients recomputed), so a replay of $R$ rotations on $\mathbf{I}$ is
within $(1+24\boldsymbol{u})^R - 1 \le 27R\boldsymbol{u}$ of the exact product (for $24R\boldsymbol{u} \le 1/8$)
and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\| \le 58R\boldsymbol{u}$, **on every tape**
(the bound does not depend on the angles, hence not on the shifts). Leaves contribute through their
$\varepsilon_U$ and the product rounding, counted in $R$ (§1). The log capacity per decoupler call
is $F(k + n_q + 2)k\,d$ (slots per trial site; `BackwardStep.ite` takes the larger branch, no flag
reasoning).

### 4.5 Error budget

The absolute accuracy in scaled units is $\delta' = \delta/(32\sqrt{n+1})$; the components are:

* $\delta_{\mathrm{scale}} \le 8(n+1)\boldsymbol{u}$, for the norm, the division and the
  multiplication back;
* $\delta_{\mathrm{reg}} = \delta'/2$, by the merged `ginibrePerturb_pwrites` at its $\delta =
  \delta'$;
* $\delta_{\mathrm{hess}} = 50(n+1)^2\boldsymbol{u}\cdot 2$ (the reduction; its $\widehat{\mathbf{U}}$ replay
  goes to $\varepsilon_U$, not to the residual budget);
* $\delta_{\mathrm{qr}} = \delta'$, Part II's absolute error at $\Sigma = 4$, the worklist sum of
  §4.3;
* $\delta_{\mathrm{leaf}} \le \beta_{\mathrm{se}}$ per leaf, inside $\delta_{\mathrm{qr}}$ (the
  forward words give backward error $\le \beta_{\mathrm{se}}$);
* $\delta_{\mathrm{rep}}$, the replay terms, inside the precision.

With B1 fixed the sum is about $0.33\delta$ (review S4). PP2 converts it to $\le \delta\|\mathbf{A}\|_2$ through $s \le (1 + 2(n+1)\boldsymbol{u})
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
  $(2B, \Gamma/2)$ by MC1, which needs only the reducer's error: $3\varepsilon_{H,T} \le
  \Gamma/(16(n+1)B)$, guaranteed by threshold term 3. The regularizer's perturbation is not in it
  (review B1: it is always larger than the gap it creates, $\Gamma \le \delta'/48$; it is
  already inside `C (A + E)`). This matches Part III's `smallEigCoreClass_hessenbergReduceLastWord`.
* The core at $(2B, \Gamma/2)$, $\Sigma = 4$, $\delta_{\mathrm{qr}} = \delta'$,
  $\varphi_{\mathrm{qr}} = \varphi/2$, with $k$ = `shqrDegree (4 * (2 * B))`, words
  `shqrSmallEigParams n k (2B) (Γ/2) 4 δ' (φ/2) ginibreGapTail ginibreConditionTail`, $F$ =
  `shqrCap`, $T$ = `shqrSmallEigCap`. Inside it, the merged split: $2(n+1)(\varphi_D + \varphi_L)$
  with the decoupler failure and the leaf failure, exactly as T1c/HL2. The leaf contract is SC5 at
  the forward words (SL4), so $\varphi_L$ is the merged `shqrSmallEigFailure`.
* Total: $3\varphi/8 + \varphi/2 \le \varphi$.

Reuse of T1c and HL2: SQ2 is HL2's proof at the generic worklist (GW4) with the tracking hook;
T1c and HL2 themselves are the skip instances (SQ5). The parameter side conditions are the merged
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
* **Log words.** No count word (B4). Plane words are exact naturals $\le n$ written by the
  producer (`IsIndexLit`, `hNat` at $n+1$ suffice); an invalid slot (valid word $\le 0$, from the
  zero fill) is skipped. Entries with $r + 1 \ge n$ give the identity in `givensAt` and are never
  produced.
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
| `Matrix/FinitePrecision/StoredDense.lean`, `Matrix/FinitePrecision/GivensPrograms.lean` | MV1, MV2 (O7 moves, first) |
| `Matrix/Perturbation/UnitarySimilarity.lean` | MW1, MW2, MW3, MW4, MW5, MW6 |
| `Matrix/Spectral/Diagonalizable.lean` | MC1 |
| `Matrix/Factorizations/Givens.lean` | MG1 |
| `Matrix/FinitePrecision/GivensChain.lean`, `GivensRounded.lean` | MG2, MG3 |
| `Matrix/FinitePrecision/GivensLog.lean` (new) | GL1, GL2, PR2, MG4 |
| `Matrix/FinitePrecision/GivensPrograms.lean` | PR1 |
| `Matrix/FinitePrecision/StoredProducts.lean` (new) | MR1 |
| `Ops/Catalog/Scalar.lean` | MS1 |
| `Ops/Logic/Backward.lean` | OB1 |
| `Ops/Profiles/RoundedScalarBlas.lean` | NM1 (`nrm2` StdModel bounds) |
| `Eigensolvers/HessenbergReduction.lean` | PR3, PR4 |
| `Eigensolvers/ShiftedQR/{StableStep, RoundedFind, RoundedRegularize*, RoundedSh*, RoundedIteration, RoundedDecouple*}.lean`, `Eigensolvers/SmallEig/{RandomHessenberg, Decouple, Decoupler, DecouplerPrecision}.lean` | RF1–RF10 (in place) |
| `Eigensolvers/ShiftedQR/{RoundedSolve, RoundedHeadline, RoundedWorklistTermination}.lean` | GW1–GW7, DC1 (in place) |
| `Eigensolvers/SmallEig/{Program, Theorems}.lean` | SL1–SL6 (in place) |
| `Eigensolvers/ShiftedQR/RoundedSmallEig.lean`, `RoundedCertificate.lean`, `RoundedSmallEigCertificate.lean`, `SmallEig/Certificate.lean` | SQ1–SQ5, RF11 |
| `Eigensolvers/Schur/{Contracts, TrackingHook, Pipeline, Regularizer, Dense, Certificate}.lean` (new folder) | SC, SC6, SH1, SH2, PP1–PP4, RG1, HD0–HD7, CT1, CT2 |

No placement flags remain after MV1/MV2 (review O7: move first).

### 8.2 Vocabulary rows

| object | meaning | Mathlib bridge |
|---|---|---|
| `IsPerturbedUnitarySimilarBy V A B ε` | perturbed similarity by the named unitary | `isPerturbedUnitarySimilar_iff_exists_by`; `isPerturbedUnitaryPair_zero_iff` (no Mathlib notion; searched) |
| `givensAt`, `givensLog` | exact unitary of a rotation log | Mathlib `List.prod`; `givens` |
| `IsTrackedUnitarySimilar εU εT U A U' A'` | the two-error stage relation | via `IsPerturbedUnitarySimilarBy` |
| `IsConditionedDiagonalizable B Γ A` | the class (κ_V ≤ B, gap ≥ Γ) | `IsDiagonalizable` (merged) |
| `GivensEntry`, `slotEntries`, `HoldsSlottedLog`, `IsGivensSink`, `skipSink`, `slotSink` | the log layer | as `HoldsMatrix` |
| `DeflationHook`, `skipHook`, `trackingHook`, `RandomLeafRoutineContractWith` | worklist routines | `PWrites` |
| `FrobNormEstimateContract`, `RandomRegularizerContract`, `HessenbergReducerContract`, `RandomSchurCoreContract`, `RandomLogDecouplingRoutineContract` | contracts | `Writes`/`PWrites` |
| `SchurOutput`, `SchurPipelineInput`, `HoldsSchurPair` | input/output memories | as `ShQRSpectrum` |

No Mathlib deviation: the witnessed predicate is a new NLAlib notion next to a NLAlib notion.

### 8.3 Shared machinery

| repeated argument | handled by | status |
|---|---|---|
| merged name kept, program generalized | instance (skip sink / skip hook) + one frame lemma (`in_frame`) | SMALLEIG pattern |
| one producer, record or not | the sink layer (GL2) | new |
| witnessed composition through `BackwardStep` | `isPerturbedUnitaryPair_zero_iff` + merged B6 | new (MW1) |
| a block step lifted with computed coupling | MW2/MW3, used by both worklist uses (top, leaf) and the reducer | new |
| replay error | MG2 + MG3 + MG4, used for coupling, $\widehat{\mathbf{U}}$, the reducer | new |
| one worklist, every mode | `solveDeflationWith D L Hk`, GW4 parameterized by the hook | new (GW) |
| stages composed | the tracked relation (MW6) + PP2; one theorem for every swap | new |
| class through a unitary stage | merged `exists_pseudoConditionNumber_le_and_le_norm_sub` | merged |
| static count of a composition | PP4 (seq adds) + `stmtWorkMono` + `kernel_rfl` | merged + new |
| `BackwardStep` through frames and allocation | the rule candidates of Part II §7.4 (`BackwardStep.in_frame`, an allocation rule) | **planned first** (OB1), since RF1–RF6 use them about 25 times |

## 9. Target table

The ids, statements, dependencies and waves are in `~/nlalib-harness/pilot/schur-targets.json` (waves by longest dependency path). Sizes S/M/L/XL; "w" the wave.

**L1: matrix library and the O7 moves (14: S 8, M 6).**

* MV1 (M, w0): `HoldsMatrix` …. O7: move the stored-matrix layer (ShiftedQR/Storage: HoldsMatrix, matrixWords, storedMatrix and lemmas) to its topic home; names kept via deprecated aliases; importers updated.
* MV2 (M, w1): `ShiftedQR.coefficients` …. O7: move Coefficients, Rotation, RotationLoops (programs + word lemmas) to Matrix/FinitePrecision; rename to the NLAlib namespace with deprecated aliases.
* MW1 (S, w0): `IsPerturbedUnitarySimilarBy` …. Named-unitary perturbed similarity and its API; bridge to the pair at scale 0 for BackwardStep (merged B6).
* MW2 (S, w1): `IsPerturbedUnitarySimilarBy.fromBlocks₁₁` …. Witnessed lifts with a computed coupling block (error ε+ρ).
* MW3 (M, w2): `IsPerturbedUnitarySimilarBy.of_range_block`. Range form on Fin N, block [lo, lo+d), lo+d ≤ N, computed top/right coupling, via finSumFinEquiv + submatrix_equiv.
* MW6 (S, w1): `IsTrackedUnitarySimilar` …. Review B2: two errors: ∃ V, By V A A' εT ∧ ‖U' − U V‖ ≤ εU; trans adds both errors.
* MW4 (S, w2): `IsTrackedUnitarySimilar.specNorm_sub_mul_mul_conjTranspose_le` …. From (1, A): ‖A − ÛT̂Ûᴴ‖ ≤ εT + (2εU+εU²)(‖A‖+εT), ‖ÛᴴÛ−1‖ ≤ 2εU+εU²; exact-unitary form.
* MW5 (M, w3): `IsTrackedUnitarySimilar.lift_leaf_block`. Leaf lift with a dense Ub from the leaf's tracked relation and the rounded products.
* MC1 (S, w1): `IsConditionedDiagonalizable` …. Review S2: the (κ_V ≤ B, gap ≥ Γ) class as a named predicate (repeated raw in the merged statements); transfer through a witnessed similarity of error ≤ Γ/(16(n+1)B) from the merged exists_pseudoConditionNumber_le_and_le_norm_sub.
* MG1 (S, w0): `givensAt` …. Exact unitary of a Givens log.
* MG2 (S, w0): `specNorm_sub_mul_le_sum` …. One-sided chains.
* MG3 (M, w0): `IsRoundedRowRotation` …. Generalize to rectangular blocks; merged square statements are instances.
* MS1 (S, w0): `Ops.StdModel.lit_zero` …. Zeros are exact.
* MR1 (M, w1): `matMulOn` …. Strided complex products (left factor optionally conjugate-transposed) with error (2d+4)u‖X‖_F‖Y‖_F.

**L2: the log layer and the stage programs (10: S 2, M 8).**

* GL1 (S, w1): `GivensEntry` …. Self-describing slotted static log: slots of 1+5w words, a valid word, entries (r, p, q); no count word (review B4).
* GL2 (M, w2): `IsGivensSink` …. The reusable logged-program layer: a producer calls a sink routine per committed rotation and per accepted slot; skip sink (Inv = True, empty footprint, zero work) and slot sink (HoldsSlottedLog).
* OB1 (M, w0): `Ops.BackwardStep.in_frame` …. Part II §7.4 rule candidates; used ~25 times.
* PR1 (M, w2): `rotateRowsOn` …. Rotations on strided views; rotateRows/ColumnsWithScratch become instances at [n,k,0,n].
* PR2 (M, w3): `givensReplayRows` …. Replay the valid slots (plane by bindIdx ≤ ld).
* MG4 (M, w4): `specNorm_givensReplayWord_sub_le` …. Each replayed rotation is within 24u‖X‖ (merged one-sided bound); a replay of R rotations is within (1+24u)^R − 1 ≤ 27Ru (24Ru ≤ 1/8) of the exact product; on every tape.
* PR3 (M, w3): `hessenbergReduceLastWith` …. In place: the reduction takes a sink; witnessed backward with Q = givensLog of the entries (check hrBound_rows first) keeping Q e_N = e_N; merged name = skip-sink instance, merged statement a corollary.
* PR4 (M, w5): `hessenbergReduceQ` …. Stage (b): (εU, εT) = (27N²u, 50N²u).
* NM1 (M, w3): `Ops.RoundedScalarBlas.nrm2_stdModel_bounds` …. Review S3: reuse merged ShiftedQR.matrixNorm; prove the StdModel bounds of nrm2 (two-sided, (1 ∓ (2N²+2)u)) and the contract instance.
* RG1 (S, w3): `Schur.ginibreRegularizer` …. Review S3: at qR = smallEigParams the merged ginibrePerturb_pwrites is the contract (class (2/t₂, t₁/2) through MC1).

**L3: the in-place refactor of the decoupler chain (13: S 1, M 5, L 6, XL 1).**

* DC1 (S, w3): `ShiftedQR.RandomLogDecouplingRoutineContract` …. The decoupler contract with the sink invariant and the witnessed similarity By (givensLog (slotEntries L)); the merged contract is the skip-sink corollary.
* RF1 (L, w3): `ShiftedQR.stepWithDiagWith` …. In place: the step takes the sink; the chain lemma names its Q's (givensLog of the step's entries); merged names = skip instances, merged statements corollaries.
* RF2 (M, w4): `ShiftedQR.stepComptauWith`. The committed comptau step; Find's trials use the skip sink.
* RF3 (L, w4): `ShiftedQR.trialStepWith` …. Trials write their slot directly; accept validates it (no LgT).
* RF4 (L, w5): `ShiftedQR.regularizeWith (sink)` …. RoundedRegularize + RoundedRegularizeTermination (1368 lines), review S1: L.
* RF5 (XL, w5): `ShiftedQR.shStepWith` …. RoundedSh, RoundedShTrial, RoundedShExc, RoundedShTermination (2739 lines), review S1: XL.
* RF6 (L, w6): `ShiftedQR.shIterationWith (sink)` …. Outcome with the named witness; measurability with the log read.
* RF7 (L, w7): `ShiftedQR.roundedDecoupleWith (sink)` …. RoundedDecouple + RoundedDecoupleRoutine; meets DC1 at sites = k + np + 2.
* RF7b (M, w7): `ShiftedQR.roundedDecoupleWith_terminates (sink)`. Review S1: termination half split out.
* RF8 (M, w4): `SmallEig.rhessWith`. Random Hessenberg form with a sink; deterministic witnessed backward.
* RF9 (M, w4): `SmallEig.decoupleLastWith`. Decouple steps through the sink.
* RF10 (L, w5): `SmallEig.smallEigDecouplerWith` …. D3b with the sink (Decoupler, DecouplerPrecision); merged D3b a corollary.
* RF11 (M, w10): `ShiftedQR.stmtWorkMono_shqrProgram` …. B5 (approved): the merged numerals change (list in note §14.4); recompute by kernel_rfl and restate; exponents expected unchanged.

**L4: generic worklist, hooks, leaves, the core (21: S 6, M 10, L 5).**

* SC (S, w2): `Schur.FrobNormEstimateContract` …. Pipeline-stage contracts: two-sided norm estimate, regularizer into a class predicate C, reducer and core with the tracked relation (εU, εT), core dims opaque.
* SC6 (S, w3): `Schur.TerminatingRegularizer` …. All-tape companions; the core's states ‖U' − UV‖ ≤ εU on every tape (review B2).
* GW7 (S, w2): `ShiftedQR.RandomLeafRoutineContractWith` …. One generic leaf interface [d, np, T] (Bk, P) → (Bk, Ev, Ub) with an output predicate; the merged eigenvalue leaf contract and the Schur leaf contract (Ev = diag Tb, tracked (1,B)→(Ub,Tb)) are instances.
* GW2 (S, w1): `ShiftedQR.DeflationHook` …. Hook contract: invariant + per-round extra error ρ, ρL and work; the skip hook: Inv = True, ρ = ρL = 0, zero work.
* GW1 (M, w4): `ShiftedQR.solveDeflationWith` …. One generic worklist with decoupler, leaf and hook routines; the merged solveRoundedWith becomes the skip-hook instance (wrapper).
* GW3 (L, w5): `ShiftedQR.DeflationWorklistState` …. The merged RoundedWorklistState/round lemmas generalized: merged invariant ∧ hook invariant; RoundedSolveBackward + RoundedHeadline round lemmas moved to the generic program.
* GW4 (L, w6): `ShiftedQR.solveDeflationWith_pwrites`. Generic theorem: the merged conclusion with the merged error, and the hook invariant at 2(n+1)(c+ε+β+ρ+ρL).
* GW5 (M, w5): `ShiftedQR.solveDeflationWith_terminates`. Generic termination (merged RoundedWorklistTermination generalized).
* GW6 (M, w7): `ShiftedQR.solveRoundedWith_pwrites` …. Merged worklist theorems re-derived as skip-hook instances, statements, costs and precision unchanged.
* SH1 (M, w4): `Schur.trackingHook`. The U-tracking hook: after a decoupler, replay on the right/top coupling and on U, exact zero at the cut; after a leaf, the three products with Ub.
* SH2 (L, w5): `Schur.trackingHook_deflationHook`. Invariant: tracked (U,A) from (U₀,H₀), block structure with exact zeros, done blocks triangular; ρ = 78u·m·N₀, ρL from MR1; triangular at the end.
* SL1 (M, w6): `SmallEig.smallEigProgWith` …. The Part III program generic in the hook (and the leaf output); merged smallEigProg = skip instance; the Schur leaf = tracking instance writing Bk, Ub, Ev.
* SL3 (L, w7): `SmallEig.smallEigProgWith_pwrites`. Generic Theorem 1.1 with the hook's invariant; merged composition proof generalized.
* SL4 (M, w8): `SmallEig.smallSchurProg_randomSchurLeafContract`. The tracking instance meets the Schur leaf contract at the forward words.
* SL5 (M, w7): `SmallEig.smallEigProgWith_terminates`. Generic termination; merged a corollary.
* SL6 (M, w8): `SmallEig.smallEig_measureReal_not_spectrum_le` …. Merged TH1–TH4 (and the _unconditional forms) as skip instances; statements unchanged.
* SQ1 (S, w7): `ShiftedQR.roundedShQRWith (hook)` …. roundedShQRWith SE L Hk; merged = skip; Schur = tracking hook with the Schur leaf; threshold among the core's words.
* SQ3 (M, w8): `ShiftedQR.shqrSchurParams` …. Merged words + threshold word; uShQRSchur = min(uShQRSmallEig, replay term).
* SQ2 (L, w9): `ShiftedQR.roundedShQRSchur_randomSchurCoreContract`. Stage (c) at the class IsConditionedDiagonalizable B Γ, 0 < Γ (review S4).
* SQ5 (M, w9): `ShiftedQR.roundedShQR_measureReal_not_spectrum_le` …. Merged T1c, HL2 (+ relative, Hermitian, unconditional) as skip instances; statements, costs, precision unchanged.
* SQ4 (S, w10): `ShiftedQR.roundedShQRSchur_measureReal_not_schur_le`. Hessenberg-class Schur headline.

**L5: composition, instance and certificates (12: S 4, M 6, L 2).**

* PP1 (M, w3): `Schur.schurPipelineWith` …. Pipeline at c core dims (numeral), interface [N, nr, nq, d₁…d_c] (A, P) → (A, U, Fl).
* PP2 (L, w4): `Schur.schurPipelineWith_measureReal_not_schur_le`. Generic composition, class predicates C, C' with a transfer hypothesis (review S2, B1: no δR), two errors (B2), hu : 8(n+1)u ≤ 1/4 (S4).
* PP3 (S, w3): `Schur.SchurOutput.exists_isEigenvalueListing` …. Corollaries.
* PP4 (S, w4): `Schur.size_stmtCost_schurPipelineWith_le` …. Static count sum (dims fixed, review S2).
* CT1 (M, w5): `Schur.schurPipelineAlgorithm` …. Certificate from component data; work = Σ component work + glue.
* HD0 (L, w9): `Schur.denseSchur` …. Parameters, the six-term threshold (class term for B1, δ/(192R)), side conditions of PP2.
* HD1 (S, w10): `Schur.denseSchur_measureReal_not_schur_le`. SchurOutput A δ (58Ru) w.p.
* HD4 (S, w10): `Schur.denseSchur_terminates`. Every tape: total and ‖ÛᴴÛ − 1‖ ≤ 58Ru; only IsExactNatLit (n+1).
* HD5 (M, w10): `Schur.logb_inv_uDenseSchur_le`. Review B3: ≤ c₁ L⁴ (log₂ L + 1)² + c₂, L = log₂(4(n+1)/(δφ)).
* HD6 (M, w10): `Schur.denseSchur_work_le`. c(n+1)³(k+1)⁵(nq+1)(F+1)(T+1)², kernel_rfl.
* HD7 (M, w11): `Schur.denseSchur_work_le_polylog` …. ≤ C(n+1)³ L^p, p fixed when proved (about 12; the paper's is 2); said in the docstring.
* CT2 (M, w11): `Schur.denseSchurAlgorithm` …. Instance certificate.

Totals: 70 targets (S 21, M 35, L 13, XL 1), waves 0–11. Besides L3, fifteen targets refactor or re-derive merged material in place: MV1, MV2, PR1, PR3, GW1, GW3, GW4, GW5, GW6, SL1, SL3, SL5, SL6, SQ5, RF11. OPT1 (spectrum-only core) is deferred (O5); the instrumentation rule is rejected (§4.1) and not a target.

## 10. Risks

* The in-place refactor (L3, GW, SL) is the bulk: about 17k merged lines on the decoupler path
  plus 2.5k of the worklist; every `Writes` lemma gains the sink's `Live`/`Disj` hypotheses. OB1
  and GL2 first; land PR3/PR4, the contracts, PP2 and the generic worklist against DC1 as a
  hypothesis before the chain (review §2 item 3).
* Measurability of the outcome sets with the log read (RF6).
* `kernel_rfl` on the larger trees (HD6, RF11).
* PR3's assumption about `hrBound_rows`' $\mathbf{Q}$ (checked first).
* Constants of PP2 and the replay are design values (O6); the known-wrong ones are fixed (§14).

## 11. Decisions (resolved by the maintainer after the review)

1. **O1** (a) `IsPerturbedUnitarySimilarBy`, with the two-error tracked relation (MW6) in the
   contracts and the worklist invariant. Ghost route rejected.
2. **O2** (a) dense $\mathbf{U}_b$ at the leaf.
3. **O3** the slotted static log, self-describing entries, behind the sink layer (§14.2 gives the
   reasons for keeping it).
4. **O4** superseded (§14.6, "Schur is the program"): the Schur-mode programs replace the merged
   eigenvalue-only programs in place; the merged eigenvalue theorems become corollaries, with
   costs about 2–3 times larger and slightly stronger precision conditions.
5. **O5** deferred (the spectrum-only core; no consumer).
6. **O6** constants allowed to move at proof time; the known-wrong ones fixed now (`hclass`,
   `64` → `58`, HD5).
7. **O7** move `HoldsMatrix` and the rotation programs first (MV1, MV2).
8. **B5** approved: the merged certificate numerals change; list in §14.4 and in the rename map.
9. **Re-check** (§14.5) applied: εU relative, threshold term 3 at 28800, log details.

## 12. Elaboration (scratch, not in the repo)

File `/home/ubuntu/.claude/jobs/59127b8e/tmp/schur-elab/SchurStatements.lean`, checked with
`lake env lean` against the built worktree (`design/schur`): **no errors**. Proofs are `sorry`.
Programs with real `opsImpl%` bodies:

* `rotateRowsOn` and `rotateColumnsOn`;
* `givensReplayRows` and `givensReplayColumns` (valid-slot test, a `bindIdx` for the plane word
  inside counted loops, offsets `s * (1 + 5 * w) + 1 + 5 * i`);
* `hessenbergReduceQ`.

The other programs are stubs: `hessenbergReduceLastLog` (named `hessenbergReduceLastWith` in the
skeleton), `schurPipelineWith`, `solveDeflationWith`, `skipHook`, the instance components.
Elaborated after the review (second pass, no errors):

* MW1 (with `trans` and the pair bridge), MW2, MW6 (with `trans`), MW4 (revised, and the
  exact-unitary form), MC1 (with the transfer);
* MG1, MG2; GL1 (`GivensEntry`, `slotEntries`, `HoldsSlottedLog`), GL2 (`IsGivensSink`);
* SC1–SC4 (two-sided norm, class predicates, tracked relation, opaque core dims), SC6 (core),
  SC5 (leaf, tracked), DC1 (slotted log, `IsConditionedDiagonalizable`);
* GW2 (`DeflationHook` shape) and GW4 `solveDeflationWith_pwrites` (generic, merged conclusion
  plus the hook invariant);
* PP2 (revised), PP3, PP4 (revised dims);
* HD1 (58), HD4 (all-tape orthogonality), HD5 (revised), HD6, `uDenseSchur_pos`,
  `mul_denseSchurRotations_le`.

The first pass's file is kept as `SchurStatements.v1.lean`. Fixes from elaboration: the pair
relation needed `Matrix.Perturbation.UnitaryPair` imported explicitly.

## 13. Material

The Part I intro (`src1/intro.tex:18, 176`), Part II and III LaTeX, the two predecessor notes,
`Corrections-BGS-Ordered.md` (N7, the bottom-$k$ cut, kept; G16/D3.4/Q4, the shift-dependence of
the step, which drives §4.1), `Sizing-SQR-FP-n3.md` (static $n^3$, guard narrowing), the merged
Lean listed in §3.3, `Computation-CertifiedRoutines.md` (routine-certificate precedent), Higham
2002 Ch. 19 (Givens error, accumulation), Watkins 2008 (Schur vectors by accumulation).

## 14. Changes after review

Fable's design review (`Review-Fable-SCHUR-Design.md`, "revise, then approve for skeleton") and
three maintainer messages (decisions O1–O7, B5 approved, "the best final structure, not the least
invasive diff", O4(b)). Every change below is applied in the sections above.

### 14.1 Blockers

* **B1, `hclass`.** It was `δR + 3εH ≤ Γ/(16(n+1)B)`, unsatisfiable at the instance
  ($\Gamma \le \delta'/48 < \delta'/2 = \delta_R$). Now the class is a predicate pair `C`, `C'` with
  a transfer hypothesis through the **reducer's** witnessed similarity only; at the instance it is
  MC1 with $3\varepsilon_{H,T} \le \Gamma/(16(n+1)B)$, guaranteed by the new threshold term 3
  ($\boldsymbol{u} \le t_1t_2/(7200(n+1)^3)$). The wrong justification in §5 is corrected.
* **B2, two errors.** The contracts and the worklist invariant use `IsTrackedUnitarySimilar εU εT`
  (MW6), not the single-ε pair. PP2 gives $e_U = 2\varepsilon_U + \varepsilon_U^2$ with
  $\varepsilon_U = \varepsilon_{H,U} + \varepsilon_{C,U}$ (no $\delta$), and HD1 is its instance. The
  constant is derived (§1): $24\boldsymbol{u}$ per replayed rotation (merged one-sided bound),
  $(1 + 24\boldsymbol{u})^R - 1 \le 27R\boldsymbol{u}$ under $24R\boldsymbol{u} \le 1/8$, so
  $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\| \le 58R\boldsymbol{u}$; threshold term 5 is
  $\delta/(192R)$. The orthogonality holds **on every tape** (HD4, SC6). HD2 is merged into HD1.
* **B3, bits.** HD5 now reads $\log_2(1/\boldsymbol{u}_0) \le c_1L^4(\log_2 L + 1)^2 + c_2$
  ($k = \Theta(L\log L)$). §0 and §1 corrected.
* **B4, exact naturals.** The count word is gone (slotted static log, self-describing entries):
  the largest natural written is a plane index $\le n$, so `IsExactNatLit id Mch (n + 1)` suffices
  for HD1 and HD4.
* **B5, merged certificate numerals.** Approved by the maintainer; listed in §14.4.

### 14.2 Structure: the best final design, with reasons

* **Witness (O1 a).** The merged chain is refactored **in place**: every rotation-producing
  program takes a sink and every backward conclusion names its unitary
  (`IsPerturbedUnitarySimilarBy (givensLog L)`); the merged `∃ U` statements are one-line
  corollaries. Reason: the witness is the strongest true statement of each lemma, a consumer
  that needs the unitary (Schur vectors, eigenvectors later) gets it without a second proof, and
  there is one program per algorithm (rule 4) instead of `…Log` twins.
* **Log (O3).** A reusable **Givens log layer** (GL1, GL2) rather than a shifted-QR-specific log:
  self-describing entries (plane, $p$, $q$), slotted static storage with validity words, and sink
  routines (`skipSink`, `slotSink`). The slotted static layout is kept because it is also the
  cleanest: no count (no exact naturals beyond $n + 1$, B4), static cost that the `stmtWorkMono`
  analysis sees directly, trials write their own slot and acceptance only validates it (no trial
  buffer, no copy). The entries carry their plane (one word more than Fable's slotted layout) so
  that the replay is producer-agnostic: the reducer, the sweep, `rhess` and any later Givens
  algorithm share one replay and one error lemma. The sink makes the eigenvalue-only run pay
  nothing (`skipSink`: empty footprint, zero work) instead of writing a scratch log.
* **Worklist (O4 b).** One generic `solveDeflationWith D L Hk`; its theorem (GW4) is parameterized
  by the hook's contract, so error, work and precision terms come from the hook; the skip hook
  contributes zero. The merged `solveRoundedWith`, `roundedShQRWith`, `smallEigProg` are the
  skip-hook instances and their theorems (worklist, T1c, HL2, TH1–TH4, the `_unconditional`,
  relative and Hermitian forms) are re-derived with their current statements, costs and
  precision (GW6, SQ5, SL6). The leaf has one generic contract (GW7) with the eigenvalue and the
  Schur leaves as instances.
* **Modularity (S2).** Core dims opaque (`(n+1) :: np :: cd`), class predicates, the threshold
  among the core's words, the pipeline's `nr` a dim; SC1 two-sided. Four pipeline stages and
  three worklist routines.
* **Library first (S3, O7).** NM1 is the `StdModel` bound of the merged `matrixNorm`
  (`RoundedScalarBlas.nrm2`), not a new program. RG1 is S: at `qR = smallEigParams …` the merged
  `ginibrePerturb_pwrites` is the contract. `HoldsMatrix` and the rotation programs move first
  (MV1, MV2), so the log layer, the strided rotations and the products land in
  `Matrix/FinitePrecision`.
* **Sizes (S1).** RF5 XL; RF4 L; RF7 split (RF7b termination M); RF11 M.
* **S4.** PP2's glue condition is `8(n+1)u ≤ 1/4`; SQ2 states `0 < Γ`.
* **Nits.** "four stages"; $e_A$ relative, $e_U$ absolute (docstring of `SchurOutput`). The base
  is still `cleanup/smalleig`; rebase on `main` before the skeleton.

### 14.3 Targets

70 targets (S 21, M 35, L 13, XL 1), waves 0–11 (§9). Removed: SW1–SW6, SL2, HD2, OL1, OPT1,
OPT2. Added: MV1, MV2, MW6, MC1, GL1, GL2, GW1–GW7, SH1, SH2, SL6, SQ5, RF7b.

### 14.4 Merged statements and numerals that change (B5, approved; rename map)

The skip-sink and skip-hook instances add frame instructions to the merged trees, so the
following `kernel_rfl` equalities and public work definitions change. The new numerals are fixed
by `kernel_rfl` at RF11; the exponents are expected to stay.

| merged declaration | file | old | new |
|---|---|---|---|
| `ShiftedQR.stmtWorkMono_shqrProgram` (statement) | RoundedCertificate | `⟨196218, [3, 3, 1, 1]⟩` | `⟨c₁, [3, 3, 1, 1]⟩`, c₁ by `kernel_rfl` |
| `ShiftedQR.shqrWork` (definition) | RoundedCertificate | `196218 * …` | `c₁ * …` |
| `ShiftedQR.stmtWorkMono_shqrSmallEigProgram` (statement) | RoundedSmallEigCertificate | `⟨675307, [3, 4, 1, 1, 2]⟩` | `⟨c₂, [3, 4, 1, 1, 2]⟩` |
| `ShiftedQR.shqrSmallEigWork` (definition) | RoundedSmallEigCertificate | `675307 * …` | `c₂ * …` |
| `SmallEig.stmtWorkMono_smallEigProgram` (statement) | SmallEig/Certificate | `⟨373483, [4, 0, 2]⟩` | `⟨c₃, [4, 0, 2]⟩` |
| `SmallEig.smallEigWork` (definition) | SmallEig/Certificate | `373483 * …` | `c₃ * …` |
| `ShiftedQR.roundedShQR_work_le` (proof witness only; statement `∃ c` unchanged) | RoundedTheorems | `2011` | by `kernel_rfl` |
| `ShiftedQR.roundedShQRSmallEig_work_le` (witness only) | RoundedSmallEig | `15895` | by `kernel_rfl` |
| `SmallEig.smallEig_work_le` (witness only) | SmallEig/Theorems | `3473` | by `kernel_rfl` |
| `ShiftedQR.exactWorkCoefficient`, `exactWorkDegree` (computed definitions; PR1 makes `rotateRowsWithScratch` an instance) | ShiftedQR/Cost | computed | computed (value changes, no numeral in a statement) |

Renames (no statement weakened): `solveRoundedWith`, `roundedShQRWith`, `smallEigProg`,
`multiStepStable`, `stepWithDiag`, `hessenbergReduceLast`, `rhess`, `decoupleLast`,
`smallEigDecoupler`, `regularizeWith`, `shStep`, `shIterationWith`, `roundedDecoupleWith` keep
their names as the skip instances; the generic programs are `solveDeflationWith`,
`smallEigProgWith`, and `…With` forms taking a sink (`multiStepStableWith`,
`hessenbergReduceLastWith`, …). MV1/MV2 move `HoldsMatrix` and the rotation programs with
deprecated aliases. The merged eigenvalue statements are strengthened only where a witness is
added, never weakened.

### 14.5 Re-check (`Review-SCHUR-Design-2.md`)

Applied in the skeleton:

* **εU relative.** `IsTrackedUnitarySimilar εU εT U A U' A'` bounds `‖U' − U V‖ ≤ εU ‖U‖`;
  `trans` composes as `(1 + εU)(1 + εU') − 1` (with `0 ≤ εU, εU'`), which telescopes from
  `U₀ = I` to `(1 + 24u)^R − 1 ≤ 27Ru`. SC3, SC4, SC6 drop `‖U‖ ≤ 2`; PP2's `e_U` is
  `2ε + ε²` with `ε = (1 + ε_{H,U})(1 + ε_{C,U}) − 1`. MW4 and the exact-unitary form take
  `0 ≤ εU` (else, at an empty index type, the conclusion `≤ 2εU + εU²` is false).
* **Threshold term 3** is `u ≤ t₁t₂/(28800(n+1)³)` (`Γ/B = t₁t₂/4`).
* **The witness** is the Schur programs' own (`givensLog` of their log): with §14.6 there is no
  hook and no arbitrary decoupler to quantify over.
* **Skeleton details.** The log entry is written from views of words the producer holds, the plane
  is a dimension (`slottedLogWrite [w, j, i, r] (Pw, Qw) → (Lg)`); `slottedLogOpen` zero-fills the
  log (the padding `(0, 0, 0)` is the identity, `givensAt_zero`, and the capacity is counted);
  the pending entries are state (`HoldsSlottedLog lg ns w L P`, with `reject`); `hNat` is a
  hypothesis of `slottedLogWrite_writes`, not of the producers.

### 14.6 Schur is the program (maintainer, after the re-check)

Supersedes O4(b), the hook and the `Option` sink. The Schur-mode programs **replace** the merged
eigenvalue-only programs in place: the shifted QR chain (step, Find, Regularize, Sh, Exc,
iteration, decoupler, worklist, `roundedShQR…`) and Part III (`rhess`, `decoupleLast`,
`smallEigDecoupler`, `smallEigProg`, the leaf) record their committed rotations in a slotted log,
replay them on the coupling blocks and on `Û`, and output `(Û, T̂)`. The eigenvalue-only programs
are deleted; there is no generic hooked worklist, no skip instance, no sink parameter. Every
merged eigenvalue theorem (T1c, T1d, T2–T5, `roundedShQRAlgorithm` and its probability bound,
HL2/HL7, `roundedShQRSmallEig…`, TH1–TH4, `smallEigAlgorithm`, …) becomes a corollary of the
Schur theorem of its program through PP3 (`diag T̂` lists the spectrum of `A + E`), keeping its
name where possible. Their costs grow by a constant factor (about 2–3) and their precision
conditions get slightly stronger; this is accepted. Every changed statement or numeral is
recorded in the rename map's `statementChanged`, every deleted program or lemma as `removed` with
its replacement. The Givens log layer (`Matrix/FinitePrecision/GivensLog`) and the witnessed
relation (MW1–MW6) stay, general.

Targets: the generic worklist and hook targets (GW1, GW2, GW3 as a generic state, GW5, GW6, GW7's
generic contract, SH1, SH2, SL1's generic program, SQ1's hook instance, GL2's sink abstraction)
are dropped or folded into the in-place rewrite targets; OB1 is already on `main`
(`BackwardStep.in_frame`, `BackwardStep.allocs` in `Ops/Logic/BackwardFrame`); corollary targets
COR1–COR4 are added (§9 of the targets file). O7's move of `HoldsMatrix` goes to
`Matrix/FinitePrecision/StoredMatrix` (Ops may import only Ops, and the storage layer uses
`decodeMatrix` of `Matrix/FinitePrecision/Machine`), the rotation programs to
`Matrix/FinitePrecision/GivensCoefficients`, `GivensRotation`, `GivensPrograms`.
