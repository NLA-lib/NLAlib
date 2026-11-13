/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosReorthProgramRounded

/-!
# Full-program guarantees of Lanczos with full reorthogonalization

What a rounded run of Lanczos with full reorthogonalization guarantees about its own decoded
outputs, in two layers.

**Generic layer.** For the loop `NLAlib.lanczosReorthLoop` with any product routine certified
by `NLAlib.Computation.IsMatvecRoutine` and any orthogonalization routine family certified by
`NLAlib.Computation.IsOrthRoutine` at parameters $(\eta_0, \varepsilon_1, \varepsilon_2,
\varepsilon_3)$, the parameter condition `NLAlib.LanczosReorthRegime` (a condition on
$q$, $\varepsilon$, $\tau$ and the four certificate parameters only) gives
`NLAlib.LanczosReorthGuarantees`: on every admissible prefix of $m$ steps the computed basis is
nearly orthonormal, the computed tridiagonal $\mathbf{T}_m$ is the exact Lanczos tridiagonal of
$(\mathbf{A} + \mathbf{E}, \mathbf{b})$ for a small symmetric $\mathbf{E}$, and the computed Ritz
values interlace the eigenvalues of $\mathbf{A}$ up to a small radius; all bounds are explicit
functions of the parameters, $m$ and $\|\mathbf{A}\|_2$. Paige analyzes reorthogonalization
corrections in [Paige1971, §6.1].

**CGS2 layer.** For the registered trees `NLAlib.lanczosReorthProg.compiled` (stored matrix) and
`NLAlib.lanczosReorthOracleProg.compiled` (matrix-free), whose orthogonalization is
`NLAlib.cgs2`, the parameter condition is discharged from the unit roundoff $u$, the
dimensions $N$, $q$ and the threshold $\tau$ alone, through the budget
`NLAlib.lanczosReorthRoundoffBound` $N\,q\,u$, that
is <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u;$$
the operation and workspace bounds apply to successful executions with unit charges.

## Adding an orthogonalization scheme

A scheme (MGS2, Householder, a QR kernel, …) gets every result of the generic layer by three
steps: (a) write its builder `orth work coef j` (reduce `work` against the columns
$0, \dots, j$ of the basis, coefficients in `coef`); (b) prove that it meets
`NLAlib.Computation.IsOrthRoutine` at parameters $(\eta_0, \varepsilon_1, \varepsilon_2,
\varepsilon_3)$ at every step $t < q$ (the CGS2 proof is
`NLAlib.Computation.IsRelErrSem.isOrthRoutine_cgs2`); (c) check
`NLAlib.LanczosReorthRegime` for those parameters (the CGS2 check is
`NLAlib.lanczosReorthRegime_cgsPassBound`). Then
`NLAlib.LanczosReorthImplementation.exec_rounded_loop_guarantees` applies to
`NLAlib.lanczosReorthLoop` with that builder; a stored-matrix or matrix-free program around the
loop is handled as `NLAlib.LanczosReorthImplementation.exec_rounded_compiled` handles the CGS2
trees.

## Main definitions

* `NLAlib.lanczosCoeffTridiagonal`: the symmetric tridiagonal of given coefficients.
* `NLAlib.LanczosReorthRegime`: the parameter condition of the generic layer.
* `NLAlib.LanczosReorthGuarantees`: the guarantees on the decoded outputs.
* `NLAlib.lanczosReorthRoundoffBound`: the CGS2 budget of the CGS2 layer.

## Main results

* `NLAlib.lanczosReorthGuarantees_of_lanczosReorthOutputs`: certified outputs in the regime
  satisfy the guarantees.
* `NLAlib.LanczosReorthImplementation.exec_rounded_loop_guarantees`: the generic loop.
* `NLAlib.lanczosReorthRegime_cgsPassBound`: the CGS2 parameters are in the regime.
* `NLAlib.LanczosReorthImplementation.exec_rounded_compiled_guarantees`: the stored-matrix
  CGS2 program.
* `NLAlib.LanczosReorthImplementation.exec_rounded_oracle_compiled_guarantees`: the matrix-free
  CGS2 program.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-! ### The generic layer -/

/-- The **symmetric tridiagonal matrix of coefficients** $\alpha$, $\beta$ has entries
$$\mathsf{lanczosCoeffTridiagonal}(\alpha,\beta,k)_{ij}:=
\begin{cases}
\alpha_{i+1} & i=j,\\
\beta_i & i=j+1,\\
\beta_j & j=i+1,\\
0 & \text{otherwise}
\end{cases}
\qquad(0\le i,j<k).$$
This is the coefficient indexing of `NLAlib.LanczosData.tridiagonal`. -/
def lanczosCoeffTridiagonal (α β : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then α ((i : ℕ) + 1)
    else if (i : ℕ) = j + 1 then β i
    else if (j : ℕ) = i + 1 then β j
    else 0

/-- **The parameter regime of Lanczos with full reorthogonalization** for $q$ steps, local
accuracy $\varepsilon$, threshold $\tau$ and an orthogonalization scheme certified at
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$: with the per-column orthogonality level
$\mu = 2(\varepsilon_1 + \varepsilon_3/\tau + \varepsilon)$, it asks $\eta_0 \le 1/100$,
$\tau \le 1$, the fixed-point condition $\sqrt{3(q+1)}\,\mu \le \eta_0$ and
$\mu + \varepsilon + \varepsilon_2 \le 1/100$. It involves the parameters only. -/
def LanczosReorthRegime (q : ℕ) (ε τ η₀ ε₁ ε₂ ε₃ : ℝ) : Prop :=
  η₀ ≤ 1 / 100 ∧ τ ≤ 1 ∧ Real.sqrt (3 * ((q : ℝ) + 1)) * (2 * (ε₁ + ε₃ / τ + ε)) ≤ η₀ ∧
    2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂ ≤ 1 / 100

/-- **The guarantees of Lanczos with full reorthogonalization** on a store: the decoded basis
$\mathbf{v}_1, \dots, \mathbf{v}_{q+1}$ (buffer $1$), coefficients $\alpha_j$ (buffer $2$),
$\beta_0,\dots,\beta_q$ (buffer $3$) and norms $\nu_1,\dots,\nu_q$ (buffer $6$) are such that, with
$\mu = 2(\varepsilon_1 + \varepsilon_3/\tau + \varepsilon)$ and
$e = 100(m+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{A}\|_2$, every prefix of $m$ steps,
$0 < m \le q$, that passes the test $\tau\nu_j < \beta_j$ on the computed $\nu_j$, $\beta_j$ for
$1 \le j \le m$ (the threshold is chosen when reading the stored norms) has $m < N$;
$\|\mathbf{V}_m^{\mathsf{H}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$;
a symmetric $\mathbf{E}$ with
$\|\mathbf{E}\|_{\mathsf F} \le e + 3(3\varepsilon + 2\sqrt{3(m+1)}\,\mu)\|\mathbf{A}\|_2$
for which the tridiagonal $\mathbf{T}_m$ of the computed $\alpha$, $\beta$ is the exact
Lanczos tridiagonal of $(\mathbf{A} + \mathbf{E}, \mathbf{b})$; and the eigenvalues $\theta_i$
of $\mathbf{T}_m$ satisfy
$\lambda_{i+N-m}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) + e$ for $i < m$. -/
def LanczosReorthGuarantees {P K : Type} [DecidableEq P] (s : Store P K) (dec : P → K → ℝ)
    (tag : P) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (ε τ ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ∃ (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
    HoldsDecoded s dec tag 1 0 (fun i (j : Fin (q + 1)) => v ((j : ℕ) + 1) i) ∧
    HoldsDecoded s dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
    HoldsDecoded s dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
    HoldsDecoded s dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
    ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
      m + 1 ≤ N ∧
      frobNorm ((LanczosReorthRun.basisOf v m)ᴴ * LanczosReorthRun.basisOf v m - 1) ≤
        Real.sqrt (3 * (m : ℝ)) * (2 * (ε₁ + ε₃ / τ + ε)) ∧
      (∃ E : Matrix (Fin N) (Fin N) ℝ, E.IsHermitian ∧
        frobNorm E ≤ (100 * ((m : ℝ) + 1) * (2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂) +
          3 * (3 * ε + 2 * Real.sqrt (3 * ((m : ℝ) + 1)) * (2 * (ε₁ + ε₃ / τ + ε)))) *
            specNorm A ∧
        lanczosTridiagonal (A + E) b m = lanczosCoeffTridiagonal α β m) ∧
      ∀ i < m,
        eigenvalue A (i + (N - m)) -
            100 * ((m : ℝ) + 1) * (2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂) * specNorm A ≤
          eigenvalue (lanczosCoeffTridiagonal α β m) i ∧
        eigenvalue (lanczosCoeffTridiagonal α β m) i ≤
          eigenvalue A i + 100 * ((m : ℝ) + 1) * (2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂) * specNorm A

/-- **Certified outputs in the regime satisfy the guarantees**: if the decoded outputs of a store
satisfy `NLAlib.LanczosReorthOutputs` at $(\varepsilon, \tau, \eta_0, \varepsilon_1,
\varepsilon_2, \varepsilon_3)$ (every admissible prefix is a run with these parameters), the
parameters satisfy `NLAlib.LanczosReorthRegime` for $q$ steps, and $\mathbf{b} \ne \mathbf{0}$,
then the store satisfies `NLAlib.LanczosReorthGuarantees`. For $0<m\le q$ passing
$\tau\nu_j < \beta_j$ for every $1\le j\le m$, with
$\mu = 2(\varepsilon_1 + \varepsilon_3/\tau + \varepsilon)$,
$\|\mathbf{V}_m^{\mathsf{H}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$, the
computed $\mathbf{T}_m$ is the Lanczos tridiagonal of $(\mathbf{A} + \mathbf{E}, \mathbf{b})$
with $\mathbf{E}^{\mathsf{H}} = \mathbf{E}$ and $\|\mathbf{E}\|_{\mathsf F} \le
(100(m+1)(\mu + \varepsilon + \varepsilon_2) + 3(3\varepsilon + 2\sqrt{3(m+1)}\,\mu))
\|\mathbf{A}\|_2$, and its eigenvalues interlace those of $\mathbf{A}$ up to
$100(m+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{A}\|_2$.
[Paige1971, §6.1] analyzes reorthogonalization corrections. No printed source for these bounds.
-/
theorem lanczosReorthGuarantees_of_lanczosReorthOutputs {P K : Type} [DecidableEq P]
    {s : Store P K} {dec : P → K → ℝ} {tag : P} {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {ε τ η₀ ε₁ ε₂ ε₃ : ℝ}
    (hout : LanczosReorthOutputs s dec tag N q A b ε τ η₀ ε₁ ε₂ ε₃)
    (hreg : LanczosReorthRegime q ε τ η₀ ε₁ ε₂ ε₃) (hbnz : b ≠ 0) :
    LanczosReorthGuarantees s dec tag N q A b ε τ ε₁ ε₂ ε₃ := by
  obtain ⟨hη, hτ1, hfix, hrec⟩ := hreg
  obtain ⟨v, α, β, ν, -, h1, h2, h3, h6, hδ, hm⟩ := hout
  refine ⟨v, α, β, ν, h1, h2, h3, h6, fun m hm0 hmq hadm => ?_⟩
  obtain ⟨L, hH, hv, hcoef, hLε, hLτ, hLη, hLε₁, hLε₂, hLε₃⟩ := hm m hm0 hmq hadm
  have hμ : L.orthLevel = 2 * (ε₁ + ε₃ / τ + ε) := by
    rw [LanczosReorthRun.orthLevel, hLε₁, hLε₃, hLτ, hLε]
  have hrecEq : L.recLevel = 2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂ := by
    rw [LanczosReorthRun.recLevel, hμ, hLε, hLε₂]
  have hrE : L.backwardRadius =
      100 * ((m : ℝ) + 1) * (2 * (ε₁ + ε₃ / τ + ε) + ε + ε₂) * specNorm A := by
    rw [LanczosReorthRun.backwardRadius, hrecEq, hH]
  have hηL : L.η₀ ≤ 1 / 100 := hLη ▸ hη
  have hτL : L.τ ≤ 1 := hLτ ▸ hτ1
  have hrecL : L.recLevel ≤ 1 / 100 := hrecEq ▸ hrec
  have hμ0 : 0 ≤ 2 * (ε₁ + ε₃ / τ + ε) := hμ ▸ L.orthLevel_nonneg
  have hsm : Real.sqrt (3 * ((m : ℝ) + 1)) * L.orthLevel ≤ L.η₀ := by
    rw [hLη, hμ]
    refine le_trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) hμ0) hfix
    have : (m : ℝ) ≤ q := by exact_mod_cast hmq
    linarith
  have hbasis : LanczosReorthRun.basisOf L.v m = LanczosReorthRun.basisOf v m := by
    ext i c
    simp only [LanczosReorthRun.basisOf, Matrix.of_apply]
    rw [hv ((c : ℕ) + 1) (by omega) (by omega)]
  have htri : L.toLanczosData.tridiagonal = lanczosCoeffTridiagonal α β m := by
    ext i j
    simp only [LanczosData.tridiagonal, lanczosCoeffTridiagonal, Matrix.of_apply,
      LanczosReorthRun.toLanczosData]
    split_ifs
    · exact (hcoef _ (by omega)).1
    · exact (hcoef _ (by omega)).2.1
    · exact (hcoef _ (by omega)).2.1
    · rfl
  have hAt : Aᵀ = A := hH ▸ L.transpose_H
  refine ⟨L.succ_le_card hηL hsm, ?_, ?_, fun i hi => ?_⟩
  · have h := L.frobNorm_transpose_mul_self_sub_one_le hηL hsm m (by omega)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    rwa [hbasis, hμ] at h
  · have hδL : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ 3 * ε := by
      rw [hv 1 le_rfl (by omega)]
      exact hδ
    obtain ⟨H', hH't, hH'f, hH'T⟩ := L.exists_pure_backward hηL hsm hrecL hτL hbnz hδL
    refine ⟨H' - A, ?_, ?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_sub, hH't, hAt]
    · rw [hrE, hμ, hH] at hH'f
      exact hH'f.trans_eq (by ring)
    · rw [add_sub_cancel, hH'T, htri]
  · have hlo := L.eigenvalue_sub_le_eigenvalue_tridiagonal hηL hsm hrecL hτL hi
    have hhi := L.eigenvalue_tridiagonal_le_add hηL hsm hrecL hτL hi
    rw [hH, hrE, htri] at hlo hhi
    exact ⟨hlo, hhi⟩

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- **Lanczos with full reorthogonalization for any certified orthogonalization scheme.**
The first seven buffers at the program tag have lengths $N,N(q+1),q,q+1,1,N,q$. Buffer $0$
decodes to $\mathbf{b}$. The eighth buffer holds the product routine's storage. Its precondition
holds initially and is preserved whenever the eight shapes and the eighth buffer's reads agree.
Assume the all-range relative-error model with unit roundoff $u$ and exact zero addition,
symmetric $\mathbf{A}$ and $\mathbf{b}\ne\mathbf{0}$. The product routine at each index
satisfies `NLAlib.Computation.IsMatvecRoutine` with coefficient $\varepsilon\|\mathbf{A}\|_2$,
where $\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound` $N\,u$, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u \le 1/100$.
At each step $t<q$ the orthogonalization meets `NLAlib.Computation.IsOrthRoutine` at parameters
$(\eta_0,\varepsilon_1,\varepsilon_2,\varepsilon_3)$ with $\varepsilon_i\ge 0$.
Take $\tau>0$ and $\mu=2(\varepsilon_1+\varepsilon_3/\tau+\varepsilon)$ satisfying
`NLAlib.LanczosReorthRegime`, namely $\eta_0\le 1/100$, $\tau\le 1$,
$\sqrt{3(q+1)}\,\mu\le\eta_0$ and $\mu+\varepsilon+\varepsilon_2\le 1/100$.
Then `NLAlib.lanczosReorthLoop` succeeds, keeps the shape, and its decoded outputs satisfy
`NLAlib.LanczosReorthGuarantees`. On every prefix $0<m\le q$ passing
$\tau\nu_j < \beta_j$ on the computed $\nu_j$, $\beta_j$ for $1\le j\le m$,
$\|\mathbf{V}_m^{\mathsf{H}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$; the
computed $\mathbf{T}_m$ is the Lanczos tridiagonal of $(\mathbf{A} + \mathbf{E}, \mathbf{b})$ for
a symmetric $\mathbf{E}$ with
$\|\mathbf{E}\|_{\mathsf F} \le (100(m+1)(\mu + \varepsilon + \varepsilon_2) +
3(3\varepsilon + 2\sqrt{3(m+1)}\,\mu))\|\mathbf{A}\|_2$; and its eigenvalues interlace those of
$\mathbf{A}$ up to $100(m+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{A}\|_2$.
[Paige1971, §6.1] analyzes reorthogonalization corrections. No printed source for these
execution bounds.
Result: lanczos-reorth-certified-scheme -/
theorem exec_rounded_loop_guarantees {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι))
    (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K (OpCount P ι)) (N q : ℕ) (slot : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q), (tag, slot)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (pre : Store P K → Prop) (hpre : pre st.store)
    (hpreFrame : ∀ s s' : Store P K, pre s → (∀ k < 8, s'.shape[k]? = s.shape[k]?) →
      (∀ i, s'.read tag 7 i = s.read tag 7 i) → pre s')
    (mv : ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit)
    (hmv : ∀ t : ℕ, IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A) pre 1 8
      (IExp.const N * IExp.var t) 0 (mv 8 (IExp.var t)))
    (orth : ℕ → ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit) {η₀ ε₁ ε₂ ε₃ : ℝ}
    (hε : 0 ≤ ε₁ ∧ 0 ≤ ε₂ ∧ 0 ≤ ε₃)
    (horth : ∀ t < q, IsOrthRoutine I dec tag N (t + 1) η₀ ε₁ ε₂ ε₃ (fun _ => True) 1 8 10 0 0
      (orth 8 10 (IExp.var t)))
    (hA : A.IsHermitian) (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hbnz : b ≠ 0) {τ : ℝ} (hτ : 0 < τ)
    (hreg : LanczosReorthRegime q (lanczosImplementationRoundoffBound N (u tag)) τ η₀ ε₁ ε₂ ε₃) :
    ∃ out : St P K (OpCount P ι),
      exec I (lanczosReorthLoop tag (IExp.const N) (IExp.const q) 0 1 2 3 4 5 6 mv orth).run
        st = some out ∧
      out.store.shape = st.store.shape ∧
      LanczosReorthGuarantees out.store dec tag N q A b
        (lanczosImplementationRoundoffBound N (u tag)) τ ε₁ ε₂ ε₃ := by
  obtain ⟨out, hrun, hshape', hout⟩ := exec_rounded_loop I tag hsem hz st N q slot A b hshape hb
    pre hpre hpreFrame mv hmv orth hε horth
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA)
    hsmall hτ
  exact ⟨out, hrun, hshape', lanczosReorthGuarantees_of_lanczosReorthOutputs (hout hbnz) hreg hbnz⟩

end LanczosReorthImplementation

/-! ### The CGS2 layer -/

/-- **The CGS2 budget of Lanczos with full reorthogonalization** for $q$ steps of length $N$
at unit roundoff $u$: twice the coefficient of one rounded CGS pass at $\eta_0 = 1/100$ plus the
local budget of the Lanczos implementation, shown
by <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$ -/
noncomputable irreducible_def lanczosReorthRoundoffBound (N q : ℕ) (u : ℝ) : ℝ :=
  101 / 25 * Real.sqrt ((q : ℝ) + 1) * ((N + q + 2 : ℕ) : ℝ) * u + 16 * ((N : ℝ) + 1) ^ 2 * u

/-- For dimension $N$, $q$ steps and nonnegative unit roundoff $u$, the CGS2 budget
is nonnegative. Its current value is <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
No printed source. -/
theorem lanczosReorthRoundoffBound_nonneg (N q : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ lanczosReorthRoundoffBound N q u := by
  rw [lanczosReorthRoundoffBound_def]
  positivity

/-- The CGS2 budget for dimension $N$, $q$ steps and roundoff parameter $u$ is at
most <!-- value lanczosReorthRoundoffBound N q u -->
$$(101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
No printed source. -/
theorem lanczosReorthRoundoffBound_le (N q : ℕ) (u : ℝ) :
    lanczosReorthRoundoffBound N q u ≤
      101 / 25 * Real.sqrt ((q : ℝ) + 1) * ((N + q + 2 : ℕ) : ℝ) * u + 16 * ((N : ℝ) + 1) ^ 2 * u :=
  (lanczosReorthRoundoffBound_def N q u).le

/-- The budget is the sum of its two parts. -/
private theorem lanczosReorthRoundoffBound_eq (N q : ℕ) (u : ℝ) :
    lanczosReorthRoundoffBound N q u =
      2 * cgsPassBound N q u (1 / 100) + lanczosImplementationRoundoffBound N u := by
  rw [lanczosReorthRoundoffBound_def, cgsPassBound_def, lanczosImplementationRoundoffBound_def]
  ring

/-- $\sqrt{3y} \le (5/4)\,y$ for $y \ge 2$, and $\sqrt{3y} \le 2y$ for $y \ge 1$. -/
private theorem sqrt_three_mul_le {y : ℝ} (hy : 1 ≤ y) :
    Real.sqrt (3 * y) ≤ 2 * y ∧ (2 ≤ y → Real.sqrt (3 * y) ≤ 5 / 4 * y) := by
  refine ⟨?_, fun hy2 => ?_⟩
  · calc Real.sqrt (3 * y) ≤ Real.sqrt ((2 * y) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * y := Real.sqrt_sq (by linarith)
  · calc Real.sqrt (3 * y) ≤ Real.sqrt ((5 / 4 * y) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 5 / 4 * y := Real.sqrt_sq (by linarith)

/-- The arithmetic of the CGS2 regime: with $\rho$ the CGS2 budget, $(q+1)\rho \le 1/1000$,
$132(q+1)\rho \le \tau$, $\tau > 0$, $\eta_0 = 4\sqrt{3(q+1)}\,\rho$ and $c_1$ the pass
coefficient at $\eta_0$: the hypotheses of the CGS2 run,
$\mu = 2(2c_1 + 2(\eta_0 + c_1)^2/\tau + \varepsilon) \le 4\rho$ and
$\varepsilon + 3c_1 \le (3/2)\rho$. -/
private theorem cgs2_regime_bounds {N q : ℕ} {u τ η₀ : ℝ} (hu : 0 ≤ u)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ 1 / 1000)
    (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ τ)
    (hη₀ : η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q u) :
    0 ≤ η₀ ∧ η₀ ≤ 1 / 100 ∧ ((N + q + 2 : ℕ) : ℝ) * u ≤ 1 / 100 ∧
      cgsPassBound N q u η₀ ≤ 1 / 100 ∧ lanczosImplementationRoundoffBound N u ≤ 1 / 100 ∧
      0 ≤ lanczosReorthRoundoffBound N q u ∧
      lanczosImplementationRoundoffBound N u ≤ lanczosReorthRoundoffBound N q u ∧
      2 * (2 * cgsPassBound N q u η₀ + 2 * (η₀ + cgsPassBound N q u η₀) ^ 2 / τ +
        lanczosImplementationRoundoffBound N u) ≤ 4 * lanczosReorthRoundoffBound N q u ∧
      lanczosImplementationRoundoffBound N u + 3 * cgsPassBound N q u η₀ ≤
        3 / 2 * lanczosReorthRoundoffBound N q u ∧
      Real.sqrt (3 * ((q : ℝ) + 1)) * (4 * lanczosReorthRoundoffBound N q u) = η₀ := by
  set x : ℝ := (q : ℝ) + 1 with hx
  set ρ := lanczosReorthRoundoffBound N q u with hρ
  set ε := lanczosImplementationRoundoffBound N u with hεd
  set c := cgsPassBound N q u (1 / 100) with hcd
  set c₁ := cgsPassBound N q u η₀ with hc₁d
  set s := Real.sqrt (3 * x) with hs
  have hx1 : 1 ≤ x := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ≤ 2 * x := (sqrt_three_mul_le hx1).1
  have hε0 : 0 ≤ ε := lanczosImplementationRoundoffBound_nonneg N hu
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  have hM0 : 0 ≤ ((N + q + 2 : ℕ) : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hcM : ((N + q + 2 : ℕ) : ℝ) * u ≤ c := by
    rw [hcd, cgsPassBound_def]
    nlinarith [mul_le_mul_of_nonneg_right hsq1 hM0]
  have hc0 : 0 ≤ c := hM0.trans hcM
  have hρeq : ρ = 2 * c + ε := lanczosReorthRoundoffBound_eq N q u
  have hρ0 : 0 ≤ ρ := lanczosReorthRoundoffBound_nonneg N q hu
  have hρle : ρ ≤ 1 / 1000 := by nlinarith
  have hη0 : 0 ≤ η₀ := by rw [hη₀]; positivity
  have hsρ : s * ρ ≤ 2 * x * ρ := mul_le_mul_of_nonneg_right hs2 hρ0
  have hηle : η₀ ≤ 8 / 1000 := by rw [hη₀]; nlinarith
  have hc₁c : c₁ ≤ c := by
    rw [hc₁d, hcd, cgsPassBound_def, cgsPassBound_def]
    gcongr
    linarith
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁d, cgsPassBound_def]; positivity
  -- $(\eta_0 + c_1)^2 \le (4s\rho + \rho/2)^2 \le 56.25\,x\rho^2$
  have hsum : η₀ + c₁ ≤ 4 * s * ρ + ρ / 2 := by rw [hη₀]; linarith
  have hsq : (η₀ + c₁) ^ 2 ≤ 57 * x * ρ ^ 2 := by
    have hss : s ^ 2 = 3 * x := Real.sq_sqrt (by linarith)
    have h1 := pow_le_pow_left₀ (by positivity) hsum 2
    have h2 : (4 * s * ρ + ρ / 2) ^ 2 = 48 * x * ρ ^ 2 + 4 * (s * ρ) * ρ + ρ ^ 2 / 4 := by
      rw [show (4 * s * ρ + ρ / 2) ^ 2 = 16 * s ^ 2 * ρ ^ 2 + 4 * (s * ρ) * ρ + ρ ^ 2 / 4 by
        ring, hss]
      ring
    have h3 : 4 * (s * ρ) * ρ ≤ 8 * x * ρ ^ 2 := by nlinarith
    have h4 : ρ ^ 2 / 4 ≤ x * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    nlinarith [sq_nonneg ρ]
  have hdiv : 2 * (η₀ + c₁) ^ 2 / τ ≤ ρ := by
    rw [div_le_iff₀ hτ]
    have := mul_le_mul_of_nonneg_left hτlo hρ0
    nlinarith [sq_nonneg ρ, mul_nonneg (by linarith : (0 : ℝ) ≤ x) (sq_nonneg ρ)]
  refine ⟨hη0, by linarith, by linarith, by linarith, by linarith, hρ0, by linarith,
    by linarith, by linarith, by rw [hη₀]; ring⟩

/-- CGS2 is in the regime: with $\rho$ = `NLAlib.lanczosReorthRoundoffBound` $N\,q\,u$, that
is <!-- value lanczosReorthRoundoffBound N q u -->
$$\rho = (101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u,$$
for $u \ge 0$, $(q+1)\rho \le 1/1000$ and $132(q+1)\rho \le \tau \le 1$,
$\tau > 0$, the CGS2 parameters $(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$ at
$\eta_0 = 4\sqrt{3(q+1)}\,\rho$, $c_1$ = `NLAlib.cgsPassBound` $N\,q\,u\,\eta_0$, that
is <!-- value cgsPassBound N q u \eta_0 -->$2(1+\eta_0)\sqrt{q+1}\,(N+q+2)\,u$, and
$\varepsilon$ = `NLAlib.lanczosImplementationRoundoffBound` $N\,u$, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$, satisfy
`NLAlib.LanczosReorthRegime` for $q$ steps: $\eta_0 \le 1/100$, $\tau \le 1$,
$\sqrt{3(q+1)}\,\mu \le \eta_0$ and $\mu + \varepsilon + 3c_1 \le 1/100$ for
$\mu = 2(2c_1 + 2(\eta_0 + c_1)^2/\tau + \varepsilon)$. No printed source. -/
theorem lanczosReorthRegime_cgsPassBound {N q : ℕ} {u τ η₀ : ℝ} (hu : 0 ≤ u)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ 1 / 1000)
    (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ τ)
    (hτ1 : τ ≤ 1)
    (hη₀ : η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q u) :
    LanczosReorthRegime q (lanczosImplementationRoundoffBound N u) τ η₀
      (2 * cgsPassBound N q u η₀) (3 * cgsPassBound N q u η₀)
      (2 * (η₀ + cgsPassBound N q u η₀) ^ 2) := by
  obtain ⟨-, hη, -, -, -, hρ0, -, hμ, hε₂, hfix⟩ := cgs2_regime_bounds hu hsmall hτ hτlo hη₀
  have hs0 : 0 ≤ Real.sqrt (3 * ((q : ℝ) + 1)) := Real.sqrt_nonneg _
  refine ⟨hη, hτ1, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hμ hs0).trans_eq hfix
  · have : lanczosReorthRoundoffBound N q u ≤ 1 / 1000 := by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      nlinarith
    linarith

/-- The CGS2 guarantees in terms of the budget: certified outputs at the CGS2 parameters with
$\eta_0 = 4\sqrt{3(q+1)}\,\rho$, $\rho$ the CGS2 budget, satisfy the explicit bounds of the
CGS2 headline theorems for $\mathbf{T}_m=\mathsf{lanczosCoeffTridiagonal}(\alpha,\beta,m)$. -/
private theorem cgs2_guarantees {P K : Type} [DecidableEq P] {s : Store P K}
    {dec : P → K → ℝ} {tag : P} {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {u τ η₀ : ℝ} (hu : 0 ≤ u)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ 1 / 1000)
    (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q u ≤ τ)
    (hτ1 : τ ≤ 1)
    (hη₀ : η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q u)
    (hbnz : b ≠ 0)
    (hout : LanczosReorthOutputs s dec tag N q A b (lanczosImplementationRoundoffBound N u) τ η₀
      (2 * cgsPassBound N q u η₀) (3 * cgsPassBound N q u η₀)
      (2 * (η₀ + cgsPassBound N q u η₀) ^ 2)) :
    ∃ (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
      HoldsDecoded s dec tag 1 0 (fun i (j : Fin (q + 1)) => v ((j : ℕ) + 1) i) ∧
      HoldsDecoded s dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
      HoldsDecoded s dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
      HoldsDecoded s dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
      ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
        m + 1 ≤ N ∧
        frobNorm ((LanczosReorthRun.basisOf v m)ᴴ * LanczosReorthRun.basisOf v m - 1) ≤
          4 * Real.sqrt (3 * (m : ℝ)) * lanczosReorthRoundoffBound N q u ∧
        (∃ E : Matrix (Fin N) (Fin N) ℝ, E.IsHermitian ∧
          frobNorm E ≤ 600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q u * specNorm A ∧
          lanczosTridiagonal (A + E) b m = lanczosCoeffTridiagonal α β m) ∧
        ∀ i < m,
          eigenvalue A (i + (N - m)) -
              600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q u * specNorm A ≤
            eigenvalue (lanczosCoeffTridiagonal α β m) i ∧
          eigenvalue (lanczosCoeffTridiagonal α β m) i ≤
            eigenvalue A i +
              600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q u * specNorm A := by
  obtain ⟨-, -, -, -, -, hρ0, hερ, hμ, hε₂, -⟩ := cgs2_regime_bounds hu hsmall hτ hτlo hη₀
  obtain ⟨v, α, β, ν, h1, h2, h3, h6, hm⟩ := lanczosReorthGuarantees_of_lanczosReorthOutputs
    hout (lanczosReorthRegime_cgsPassBound hu hsmall hτ hτlo hτ1 hη₀) hbnz
  refine ⟨v, α, β, ν, h1, h2, h3, h6, fun m hm0 hmq hadm => ?_⟩
  obtain ⟨hN, ha, ⟨E, hEt, hEf, hET⟩, hc⟩ := hm m hm0 hmq hadm
  set ρ := lanczosReorthRoundoffBound N q u
  set ε := lanczosImplementationRoundoffBound N u
  set μ := 2 * (2 * cgsPassBound N q u η₀ + 2 * (η₀ + cgsPassBound N q u η₀) ^ 2 / τ + ε)
  have hA0 : 0 ≤ specNorm A := specNorm_nonneg A
  have hy2 : (2 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    linarith
  -- the recurrence level is at most $5.5\rho$, the radius at most $550(m+1)\rho\|\mathbf{A}\|_2$
  have hrec : μ + ε + 3 * cgsPassBound N q u η₀ ≤ 11 / 2 * ρ := by linarith
  have hrad : 100 * ((m : ℝ) + 1) * (μ + ε + 3 * cgsPassBound N q u η₀) * specNorm A ≤
      600 * ((m : ℝ) + 1) * ρ * specNorm A := by
    have h := mul_le_mul_of_nonneg_left hrec (by positivity : (0 : ℝ) ≤ 100 * ((m : ℝ) + 1))
    have h' : 100 * ((m : ℝ) + 1) * (μ + ε + 3 * cgsPassBound N q u η₀) ≤
        600 * ((m : ℝ) + 1) * ρ := by nlinarith
    exact mul_le_mul_of_nonneg_right h' hA0
  refine ⟨hN, ha.trans ?_, ⟨E, hEt, hEf.trans ?_, hET⟩, fun i hi => ?_⟩
  · have := mul_le_mul_of_nonneg_left hμ (Real.sqrt_nonneg (3 * (m : ℝ)))
    linarith
  · have hsq := (sqrt_three_mul_le (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1)).2 hy2
    have hsμ : Real.sqrt (3 * ((m : ℝ) + 1)) * μ ≤ 5 * ((m : ℝ) + 1) * ρ := by
      have h1 := mul_le_mul_of_nonneg_left hμ (Real.sqrt_nonneg (3 * ((m : ℝ) + 1)))
      have h2 := mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ 4 * ρ)
      nlinarith
    have hin : 100 * ((m : ℝ) + 1) * (μ + ε + 3 * cgsPassBound N q u η₀) +
        3 * (3 * ε + 2 * Real.sqrt (3 * ((m : ℝ) + 1)) * μ) ≤ 600 * ((m : ℝ) + 1) * ρ := by
      nlinarith
    calc _ ≤ _ := mul_le_mul_of_nonneg_right hin hA0
      _ = _ := by ring
  · obtain ⟨hlo, hhi⟩ := hc i hi
    exact ⟨by linarith, by linarith⟩

namespace LanczosReorthImplementation

variable {P ι K : Type} [DecidableEq P]

/-- **Lanczos with CGS2 full reorthogonalization, stored matrix.** The seven buffers at the
program tag have lengths $N,N(q+1),q,q+1,1,N,q$. Buffer $0$ decodes to
$\mathbf{b}\ne\mathbf{0}$ and the first $N^2$ ROM words decode column-major to a symmetric
$\mathbf{A}$. Assume the all-range relative-error model with unit roundoff $u$ at this tag,
exact zero addition and unit charges. Let $\rho$ = `NLAlib.lanczosReorthRoundoffBound`
$N\,q\,u$, that is <!-- value lanczosReorthRoundoffBound N q u -->
$$\rho = (101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
If $(q+1)\rho \le 1/1000$ and $0 < \tau$, $132(q+1)\rho \le \tau \le 1$, the
registered tree `NLAlib.lanczosReorthProg.compiled` finishes, keeps the shape, uses at most
`NLAlib.lanczosReorthCount` operations of each kind and at most $N^2 + 2N + 2q + 5$ additional
live cells at its tag, and on every prefix of $m$ steps, $0 < m \le q$, that passes the test
$\tau\nu_j < \beta_j$ for $1 \le j \le m$ on the computed $\nu_j$, $\beta_j$, the decoded
outputs satisfy the following bounds. Any $\tau$ in the range may be chosen after the run.
The prefix length satisfies $m<N$ and its basis satisfies
$\|\mathbf{V}_m^{\mathsf{H}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le 4\sqrt{3m}\,\rho$;
the matrix $\mathbf{T}_m=\mathsf{lanczosCoeffTridiagonal}(\alpha,\beta,m)$ is the exact
Lanczos tridiagonal of $(\mathbf{A}+\mathbf{E},\mathbf{b})$ for a symmetric $\mathbf{E}$ with
$\|\mathbf{E}\|_{\mathsf F} \le 600(m+1)\rho\|\mathbf{A}\|_2$; and the eigenvalues $\theta_i$ of
$\mathbf{T}_m$ satisfy $\lambda_{i+N-m}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) +
e$, $e = 600(m+1)\rho\|\mathbf{A}\|_2$, for $i < m$. [Paige1971, §6.1] analyzes
reorthogonalization corrections. No printed source for this CGS2 program bound.
Result: lanczos-reorth-cgs2-program-guarantees -/
theorem exec_rounded_compiled_guarantees {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (values : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j) (hA : A.IsHermitian)
    (hbnz : b ≠ 0)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) ≤ 1 / 1000)
    {τ : ℝ} (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) ≤ τ)
    (hτ1 : τ ≤ 1) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape = st.store.shape ∧
      out.cnt ≤ st.cnt + lanczosReorthCount tag N q ∧
      (∀ p, out.peak p ≤
        max (st.peak p) (st.cur p + if p = tag then N * N + 2 * N + 2 * q + 5 else 0)) ∧
      ∃ (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
        HoldsDecoded out.store dec tag 1 0 (fun i (j : Fin (q + 1)) => v ((j : ℕ) + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
        HoldsDecoded out.store dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
        ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
          m + 1 ≤ N ∧
          frobNorm ((LanczosReorthRun.basisOf v m)ᴴ * LanczosReorthRun.basisOf v m - 1) ≤
            4 * Real.sqrt (3 * (m : ℝ)) * lanczosReorthRoundoffBound N q (u tag) ∧
          (∃ E : Matrix (Fin N) (Fin N) ℝ, E.IsHermitian ∧
            frobNorm E ≤
              600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) * specNorm A ∧
            lanczosTridiagonal (A + E) b m = lanczosCoeffTridiagonal α β m) ∧
          ∀ i < m,
            eigenvalue A (i + (N - m)) -
                600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) * specNorm A ≤
              eigenvalue (lanczosCoeffTridiagonal α β m) i ∧
            eigenvalue (lanczosCoeffTridiagonal α β m) i ≤ eigenvalue A i +
              600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) * specNorm A := by
  have hu0 := hsem.nonneg (p := tag) trivial
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ,
      η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q (u tag) :=
    ⟨_, rfl⟩
  obtain ⟨hη0, hη, hu, hc₁, hε, -⟩ := cgs2_regime_bounds hu0 hsmall hτ hτlo hη₀
  obtain ⟨out, hexec, hsh, hout⟩ := exec_rounded_compiled I tag hsem hz st N q A b values hshape
    hb hrom hdecode hA hε hbnz hη0 hη hu hc₁ hτ
  have hbnd := (lanczosReorthProg.compiled (ι := ι) tag).bounds_staticCost_of_exec_eq_some I N
    ![q] hexec
  have hch : I.charge = fun k => Finsupp.single k 1 := hc.charge_eq
  have hcount : ((lanczosReorthProg.compiled (ι := ι) tag).staticCost I.charge I.width N
      ![q]).count ≤ lanczosReorthCount tag N q := by
    rw [hch]
    exact lanczosReorthProg.staticCost_count_le (ι := ι) tag I.width N q
  have hpk : ∀ p, out.peak p ≤
      max (st.peak p) (st.cur p + if p = tag then N * N + 2 * N + 2 * q + 5 else 0) :=
    fun p => (hbnd.peak p).trans (max_le_max le_rfl (Nat.add_le_add_left
      (lanczosReorthProg.staticCost_cells_le (ι := ι) tag I.charge I.width N q p) _))
  exact ⟨out, hexec, hsh, fun k => (hbnd.count k).trans (Nat.add_le_add_left (hcount k) _), hpk,
    cgs2_guarantees hu0 hsmall hτ hτlo hτ1 hη₀ hbnz hout⟩

/-- **Lanczos with CGS2 full reorthogonalization, matrix-free.** The seven buffers at the program
tag have lengths $N,N(q+1),q,q+1,1,N,q$, and buffer $0$ decodes to $\mathbf{b}\ne\mathbf{0}$.
Assume the all-range relative-error model with unit roundoff $u$ at this tag, exact zero addition
and unit charges. For symmetric $\mathbf{A}$, the height-$N$ oracle succeeds on every
length-$N$ input with normwise error coefficient
$\eta\|\mathbf{A}\|_2$ (`NLAlib.Computation.IsMatvecErr`) with $\eta \le$
`NLAlib.lanczosImplementationRoundoffBound` $N\,u$, that
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$.
Let $\rho$ = `NLAlib.lanczosReorthRoundoffBound` $N\,q\,u$, that
is <!-- value lanczosReorthRoundoffBound N q u -->
$$\rho = (101/25)\sqrt{q+1}\,(N+q+2)\,u + 16(N+1)^2u.$$
If $(q+1)\rho \le 1/1000$ and $0 < \tau$, $132(q+1)\rho \le \tau \le 1$, the
registered tree `NLAlib.lanczosReorthOracleProg.compiled` finishes, keeps the shape, uses at
most `NLAlib.lanczosReorthOracleCount` operations of each kind and at most $2N + 2q + 5$
additional live cells at its tag, and on every prefix of $m$ steps, $0 < m \le q$, that passes
the test $\tau\nu_j < \beta_j$ for $1 \le j \le m$ on the computed $\nu_j$, $\beta_j$, the
decoded outputs satisfy the following bounds. Any $\tau$ in the range may be chosen after the run.
The prefix length satisfies $m<N$ and its basis satisfies
$\|\mathbf{V}_m^{\mathsf{H}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le 4\sqrt{3m}\,\rho$;
the matrix $\mathbf{T}_m=\mathsf{lanczosCoeffTridiagonal}(\alpha,\beta,m)$ is the exact
Lanczos tridiagonal of $(\mathbf{A}+\mathbf{E},\mathbf{b})$ for a symmetric $\mathbf{E}$ with
$\|\mathbf{E}\|_{\mathsf F} \le 600(m+1)\rho\|\mathbf{A}\|_2$; and the eigenvalues $\theta_i$ of
$\mathbf{T}_m$ satisfy $\lambda_{i+N-m}(\mathbf{A}) - e \le \theta_i \le \lambda_i(\mathbf{A}) +
e$, $e = 600(m+1)\rho\|\mathbf{A}\|_2$, for $i < m$. Oracle backend storage and arithmetic are
outside this access model. [Paige1971, §6.1] analyzes reorthogonalization corrections.
No printed source for this CGS2 program bound.
Result: lanczos-reorth-cgs2-oracle-guarantees -/
theorem exec_rounded_oracle_compiled_guarantees {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
      (tag, 1), (tag, N), (tag, q)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    {η : ℝ} (hmv : IsMatvecErr I o dec tag A (η * specNorm A))
    (hηmv : η ≤ lanczosImplementationRoundoffBound N (u tag)) (hA : A.IsHermitian) (hbnz : b ≠ 0)
    (hsmall : ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) ≤ 1 / 1000)
    {τ : ℝ} (hτ : 0 < τ) (hτlo : 132 * ((q : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) ≤ τ)
    (hτ1 : τ ≤ 1) :
    ∃ out : St P K (OpCount P ι),
      (lanczosReorthOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out.store.shape = st.store.shape ∧
      out.cnt ≤ st.cnt + lanczosReorthOracleCount tag o N q ∧
      (∀ p, out.peak p ≤
        max (st.peak p) (st.cur p + if p = tag then 2 * N + 2 * q + 5 else 0)) ∧
      ∃ (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
        HoldsDecoded out.store dec tag 1 0 (fun i (j : Fin (q + 1)) => v ((j : ℕ) + 1) i) ∧
        HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
        HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
        HoldsDecoded out.store dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
        ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
          m + 1 ≤ N ∧
          frobNorm ((LanczosReorthRun.basisOf v m)ᴴ * LanczosReorthRun.basisOf v m - 1) ≤
            4 * Real.sqrt (3 * (m : ℝ)) * lanczosReorthRoundoffBound N q (u tag) ∧
          (∃ E : Matrix (Fin N) (Fin N) ℝ, E.IsHermitian ∧
            frobNorm E ≤
              600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) * specNorm A ∧
            lanczosTridiagonal (A + E) b m = lanczosCoeffTridiagonal α β m) ∧
          ∀ i < m,
            eigenvalue A (i + (N - m)) -
                600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) * specNorm A ≤
              eigenvalue (lanczosCoeffTridiagonal α β m) i ∧
            eigenvalue (lanczosCoeffTridiagonal α β m) i ≤ eigenvalue A i +
              600 * ((m : ℝ) + 1) * lanczosReorthRoundoffBound N q (u tag) * specNorm A := by
  have hu0 := hsem.nonneg (p := tag) trivial
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ,
      η₀ = 4 * Real.sqrt (3 * ((q : ℝ) + 1)) * lanczosReorthRoundoffBound N q (u tag) :=
    ⟨_, rfl⟩
  obtain ⟨hη0, hη, hu, hc₁, hε, -⟩ := cgs2_regime_bounds hu0 hsmall hτ hτlo hη₀
  obtain ⟨out, hexec, hsh, hout⟩ := exec_rounded_oracle_compiled I tag o hsem hz st N q A b
    hshape hb hmv hηmv hA hε hbnz hη0 hη hu hc₁ hτ
  have hbnd := (lanczosReorthOracleProg.compiled tag o).bounds_staticCost_of_exec_eq_some I N
    ![q] hexec
  have hch : I.charge = fun k => Finsupp.single k 1 := hc.charge_eq
  have hcount : ((lanczosReorthOracleProg.compiled tag o).staticCost I.charge I.width N
      ![q]).count ≤ lanczosReorthOracleCount tag o N q := by
    rw [hch]
    exact lanczosReorthOracleProg.staticCost_count_le tag o I.width N q
  have hpk : ∀ p, out.peak p ≤
      max (st.peak p) (st.cur p + if p = tag then 2 * N + 2 * q + 5 else 0) :=
    fun p => (hbnd.peak p).trans (max_le_max le_rfl (Nat.add_le_add_left
      (lanczosReorthOracleProg.staticCost_cells_le tag o I.charge I.width N q p) _))
  exact ⟨out, hexec, hsh, fun k => (hbnd.count k).trans (Nat.add_le_add_left (hcount k) _), hpk,
    cgs2_guarantees hu0 hsmall hτ hτlo hτ1 hη₀ hbnz hout⟩

end LanczosReorthImplementation

end NLAlib
