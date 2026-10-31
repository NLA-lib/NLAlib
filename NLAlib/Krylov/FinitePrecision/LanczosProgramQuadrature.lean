/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosFunctions
-- The Lanczos program and its rounding analysis are not on `main` yet: they land with their
-- registered targets (branch `pending/program-targets`, `LanczosRounding.lean`).
public import NLAlib.Krylov.Processes.LanczosRounding

/-!
# Lanczos quadrature in finite precision for the dense Lanczos program

The Knizhnerman-type quadrature bound of `NLAlib/Krylov/FinitePrecision/LanczosFunctions.lean`
for the outputs of the dense Lanczos program run under a relative-error semantics.

## Main results

* `NLAlib.HasLanczosQuadratureBound`: the quadrature bound on the outputs of a run.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosQuadratureBound_of_lanczosBasisDenseProg`:
  the quadrature bound for the dense program, end to end.
-/

@[expose] public section

open Polynomial MeasureTheory
open scoped Matrix NNReal

namespace NLAlib

open Computation Builder

/-- The tridiagonal matrix assembled from the output coefficients $\alpha_j$, $\beta_j$
(0-based, as the program writes them): $\alpha_i$ on the diagonal, $\beta_j$ at $(j + 1, j)$
and $(j, j + 1)$. -/
def lanczosOutputTridiagonal (α β : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then α i else if (i : ℕ) = j + 1 then β j else if (j : ℕ) = i + 1 then β i else 0

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

omit [AddMonoid C] in
/-- **The outputs of a Lanczos run satisfy the quadrature bound**: with $k$ the number of steps
before breakdown, $c = 2000k^4\varepsilon\|\mathbf{H}\|_2$ and
$\bar{\mathbf{v}}_1 = \mathbf{v}_1/\|\mathbf{v}_1\|$ the normalised computed first vector, for
every $f$ $L$-Lipschitz on $I_c = [a - c, a' + c]$ and the index $i_0 = 0$ of $\mathbf{T}_k$,
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le 2E_{2k-1}(f; I_c) + Lc .$$ -/
def HasLanczosQuadratureBound (st : St P K C) (p : P)
    (dec : P → K → ℝ) (u ε : ℝ) (alpha beta Q : ℕ) {N : ℕ} (q : ℕ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (a a' : ℝ) : Prop :=
  ∃ (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ), LanczosOutputs st p dec alpha beta Q q α β V ∧
    (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • V 0 = b + δ₀ ∧
      ‖WithLp.toLp 2 δ₀‖ ≤ u * ‖WithLp.toLp 2 b‖) ∧
    ∀ (f : ℝ → ℝ) (Lf : ℝ≥0),
      LipschitzOnWith Lf f (Set.Icc (a - lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)
        (a' + lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)) →
      ∀ i₀ : Fin (lanczosSteps β q), (i₀ : ℕ) = 0 →
      |(‖WithLp.toLp 2 (V 0)‖⁻¹ • V 0) ⬝ᵥ (cfc f H *ᵥ (‖WithLp.toLp 2 (V 0)‖⁻¹ • V 0)) -
          cfc f (lanczosOutputTridiagonal α β (lanczosSteps β q)) i₀ i₀| ≤
        2 * minimaxError f
            (Set.Icc (a - lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)
              (a' + lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H))
            (2 * lanczosSteps β q - 1) +
          Lf * (lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)

/-- **The dense Lanczos program satisfies the Knizhnerman-type quadrature bound** (end to end):
for an interpretation with a relative-error semantics of unit roundoff $u$ that adds zeros
exactly, a stored symmetric $N \times N$ matrix $\mathbf{H}$ with
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$, a nonzero start vector $\mathbf{b}$, $q > 0$
steps, $(N + 4)u < 1$ and $q\varepsilon \le 1/100$ for
$\varepsilon = \max(\sqrt{N}\gamma_N, \gamma_{N+4})$ (`NLAlib.lanczosRoundingEps`), the run of
the dense Lanczos program succeeds and its outputs satisfy
`NLAlib.HasLanczosQuadratureBound`: with $k$ the number of steps before breakdown,
$f$ $L$-Lipschitz on $I_c = [a - c, a' + c]$ and <!-- value lanczosBackwardFactor k -->
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$,
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le 2E_{2k-1}(f; I_c) + Lc .$$
No printed source.
Result: lanczos-quadrature-finite-precision -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosQuadratureBound_of_lanczosBasisDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Hw : Fin N → Fin N → K)
    (hH : (Matrix.of fun i j => dec p (Hw i j))ᵀ = Matrix.of fun i j => dec p (Hw i j))
    {a a' : ℝ} (hs : spectrum ℝ (Matrix.of fun i j => dec p (Hw i j)) ⊆ Set.Icc a a')
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0)
    (hq : 0 < q) (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) ≤
      1 / 100) :
    ∃ st', exec I (lanczosBasisDenseProg p (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Hw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      HasLanczosQuadratureBound st' p dec (u p)
        (lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p))) 2 3 4 q
        (Matrix.of fun i j => dec p (Hw i j)) (fun i => dec p (b i)) a a' := by
  obtain ⟨st', he, hL⟩ :=
    IsRelErrSem.exists_lanczosRun_of_lanczosBasisDenseProg I p h hz q Hw hH b hb hq hu hsmall
  refine ⟨st', he, ?_⟩
  obtain ⟨α, β, V, hout, hstart, -, -, L, hLH, hLε, hcoef, hvec⟩ := hL
  have hv1 : L.normalizedV 1 = ‖WithLp.toLp 2 (V 0)‖⁻¹ • V 0 := by
    rw [L.normalizedV_of_le L.k_pos, hvec 0 (Nat.zero_le _)]
  have hT : lanczosOutputTridiagonal α β (lanczosSteps β q) = L.tridiagonal := by
    ext i j
    simp only [lanczosOutputTridiagonal, LanczosRun.tridiagonal, LanczosData.tridiagonal,
      LanczosRun.toLanczosData, Matrix.of_apply]
    split_ifs with h1 h2 h3
    · exact (hcoef i i.2).1.symm
    · rw [h2]
      exact (hcoef j (by omega)).2.symm
    · rw [h3]
      exact (hcoef i (by omega)).2.symm
    · rfl
  rw [← hLH] at hs
  rw [← hLH, ← hLε]
  refine ⟨α, β, V, hout, hstart, fun f Lf hf i₀ hi₀ => ?_⟩
  rw [hT, show i₀ = L.firstIndex from Fin.ext hi₀, ← hv1]
  exact L.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn hs hf

end NLAlib
