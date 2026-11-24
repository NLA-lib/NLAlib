/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Matchings of the eigenvalues of nearby matrices

For any two complex matrices of order $N = n + 1$ there is a matching of their eigenvalues, with
multiplicity, at distance at most $(2N - 1)(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/N}
\|\mathbf{A}' - \mathbf{A}\|_2^{1/N}$ (the Ostrowski–Elsner theorem, with the constant of the
component argument; [BhatiaElsnerKrause1990] has $4$). The proof is by compactness: eigenvalue
listings move continuously up to a permutation along a converging sequence of matrices, every
eigenvalue of $\mathbf{A}'$ is close to one of $\mathbf{A}$ (Elsner's bound), and along the segment
from $\mathbf{A}$ to $\mathbf{A}'$ the count of eigenvalues in each connected component of the
union of the disks is constant. Through a diagonalizable matrix with a conditioned eigenvector
matrix and separated eigenvalues the matching is linear in the perturbation
(`NLAlib.norm_sub_le_of_matching`), which gives the forward error of an eigenvalue solver with a
backward guarantee: the root of the order is paid only on the part of the perturbation that
leaves the class. [BanksGarzaVargasSrivastava2025]

## Main results

* `NLAlib.exists_tendsto_isEigenvalueListing`: continuity of listings up to a permutation.
* `NLAlib.norm_det_smul_one_sub_le_of_mem_spectrum`,
  `NLAlib.exists_norm_sub_le_rpow_of_mem_spectrum`: Elsner's bound for one eigenvalue.
* `NLAlib.exists_isEigenvalueListing_norm_sub_le_of_continuous`: listings along a path whose
  spectrum stays near the eigenvalues at the start (the component argument).
* `NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`: the Ostrowski–Elsner matching.
* `NLAlib.exists_isEigenvalueListing_norm_sub_le_of_class`: the matching through a
  diagonalizable matrix.
* `NLAlib.IsConditionedDiagonalizable.le_norm_sub_diag_of_add_eq`: the Schur diagonal of a
  perturbed matrix of the class is separated.
-/

@[expose] public section

open Filter Topology
open scoped Matrix

namespace NLAlib

/-- Eigenvalue listings are continuous up to a permutation: if the complex matrices
$\mathbf{A}_j$ of order $n$ tend to $\mathbf{A}$ and $\boldsymbol{\lambda}_j$ lists the
eigenvalues of $\mathbf{A}_j$ with multiplicity, then along a subsequence and after permuting each
listing they converge to a listing of the eigenvalues of $\mathbf{A}$. No printed source. -/
theorem exists_tendsto_isEigenvalueListing {n : ℕ} {A : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {A₀ : Matrix (Fin n) (Fin n) ℂ} (hA : Tendsto A atTop (𝓝 A₀)) {ev : ℕ → Fin n → ℂ}
    (hev : ∀ j, IsEigenvalueListing (A j) (ev j)) :
    ∃ (φ : ℕ → ℕ) (σ : ℕ → Equiv.Perm (Fin n)) (e : Fin n → ℂ), StrictMono φ ∧
      IsEigenvalueListing A₀ e ∧ Tendsto (fun j => ev (φ j) ∘ σ j) atTop (𝓝 e) := by
  -- the listings lie in a compact box, since `‖ev j i‖ ≤ ‖A j‖₂` and `‖A j‖₂` is bounded
  obtain ⟨M, hM⟩ := ((continuous_specNorm.tendsto A₀).comp hA).bddAbove_range
  have hmem : ∀ j, ev j ∈ Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) M :=
    fun j i _ => mem_closedBall_zero_iff.mpr <| (norm_le_specNorm_of_mem_spectrum
      ((hev j).spectrum_eq_range ▸ Set.mem_range_self i)).trans (hM ⟨j, rfl⟩)
  obtain ⟨e, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) M).tendsto_subseq hmem
  -- no relabelling is needed; the limit is a listing because listings form a closed relation
  refine ⟨φ, fun _ => Equiv.refl _, e, hφ, ?_, hlim⟩
  exact isClosed_setOf_isEigenvalueListing.mem_of_tendsto
    ((hA.comp hφ.tendsto_atTop).prodMk_nhds hlim) (Eventually.of_forall fun j => hev (φ j))

/-- The determinant step of Elsner's bound: if $\mu$ is an eigenvalue of the complex matrix
$\mathbf{A}'$ of order $n + 1$, then for every $\mathbf{A}$ of the same order
$$\lvert\det(\mu\mathbf{I} - \mathbf{A})\rvert \le \|\mathbf{A}' - \mathbf{A}\|_2\,
  (\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^n.$$ -/
theorem norm_det_smul_one_sub_le_of_mem_spectrum {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A') :
    ‖(μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A).det‖ ≤
      specNorm (A' - A) * (specNorm A + specNorm A') ^ n := by
  -- a Schur form of `A'` with `μ` first: `Uᴴ A' U = T` upper triangular, `T₀₀ = μ`
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing A'
  obtain ⟨k, hk⟩ : μ ∈ Set.range d := hd.spectrum_eq_range ▸ hμ
  obtain ⟨U, hU, hT, hdiag⟩ :=
    (hd.comp_equiv (Equiv.swap 0 k)).exists_hasOrthonormalCols_isUpperTriangular
  set T := Uᴴ * A' * U
  set M := Uᴴ * (μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A) * U
  have hUU : Uᴴ * U = 1 := hU
  have hdet : M.det = (μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, ← Matrix.det_mul, hUU,
      Matrix.det_one, mul_one]
  have hM : M = (μ • 1 - T) + Uᴴ * (A' - A) * U := by
    simp only [M, T, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU]
    abel
  -- the first column of `M` is that of `Uᴴ (A' - A) U`
  have hcol0 : M.col 0 = (Uᴴ * (A' - A) * U).col 0 := by
    ext i
    rw [hM]
    simp only [Matrix.col_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, add_eq_right, sub_eq_zero]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [hdiag, Function.comp_apply, Equiv.swap_apply_left, hk, if_pos rfl, mul_one]
    · rw [if_neg hi, mul_zero, hT (Fin.pos_iff_ne_zero.mpr hi)]
  have hS : specNorm M ≤ specNorm A + specNorm A' := by
    have hμT : ‖μ‖ ≤ specNorm A' := by
      have h := norm_apply_le_specNorm T 0 0
      rwa [hdiag, Function.comp_apply, Equiv.swap_apply_left, hk,
        hU.specNorm_conjTranspose_mul_mul] at h
    rw [hU.specNorm_conjTranspose_mul_mul]
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_smul, specNorm_one, mul_one]
    linarith
  rw [← hdet]
  refine (norm_det_le_prod_norm_col M).trans ?_
  rw [Fin.prod_univ_succ, hcol0]
  refine mul_le_mul ((norm_toLp_col_le_specNorm _ 0).trans
    (hU.specNorm_conjTranspose_mul_mul _).le) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (specNorm_nonneg _)
  calc ∏ i : Fin n, ‖WithLp.toLp 2 (M.col i.succ)‖
      ≤ ∏ _i : Fin n, (specNorm A + specNorm A') :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          fun i _ => (norm_toLp_col_le_specNorm M i.succ).trans hS
    _ = (specNorm A + specNorm A') ^ n := by rw [Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- Every eigenvalue $\mu$ of a complex matrix $\mathbf{A}'$ of order $n + 1$ is within
$$(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/(n + 1)}\,
  \|\mathbf{A}' - \mathbf{A}\|_2^{1/(n + 1)}$$
of an eigenvalue of $\mathbf{A}$ (Elsner's bound): the step of the Ostrowski–Elsner matching for
one eigenvalue. -/
theorem exists_norm_sub_le_rpow_of_mem_spectrum {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A') :
    ∃ ν ∈ spectrum ℂ A, ‖μ - ν‖ ≤ (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
      specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
  obtain ⟨ev, hev⟩ := exists_isEigenvalueListing A
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - ev i‖)
    Finset.univ_nonempty
  refine ⟨ev i, hev.spectrum_eq_range ▸ Set.mem_range_self i, ?_⟩
  set S := specNorm A + specNorm A'
  set δ := ‖μ - ev i‖
  have hS : 0 ≤ S := add_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hE : 0 ≤ specNorm (A' - A) := specNorm_nonneg _
  -- `δ^(n+1) ≤ ∏ ‖μ - ev j‖ = ‖det(μ I - A)‖ ≤ ‖A' - A‖ S^n`
  have hpow : δ ^ (n + 1) ≤ specNorm (A' - A) * S ^ n := by
    have hdet : (μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A).det = ∏ j, (μ - ev j) := by
      have h := congrArg (Polynomial.eval μ) hev
      rw [Matrix.eval_charpoly, Polynomial.eval_prod, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal] at h
      simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h
    refine le_trans ?_ (norm_det_smul_one_sub_le_of_mem_spectrum (A := A) hμ)
    rw [hdet, norm_prod]
    calc δ ^ (n + 1) = ∏ _j : Fin (n + 1), δ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j, ‖μ - ev j‖ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => hi j (Finset.mem_univ j)
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  calc δ = (δ ^ (n + 1)) ^ (1 / ((n : ℝ) + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        push_cast
        rw [mul_one_div_cancel hN, Real.rpow_one]
    _ ≤ (specNorm (A' - A) * S ^ n) ^ (1 / ((n : ℝ) + 1)) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = S ^ (1 - 1 / ((n : ℝ) + 1)) * specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
        rw [Real.mul_rpow hE (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hS, mul_comm]
        congr 2
        field_simp
        ring

/-! ### Listings along a path that stays near the spectrum -/

/-- The graph of overlapping disks: indices $i \ne j$ are adjacent when
$\lvert\lambda_i - \lambda_j\rvert \le 2r$. -/
private abbrev diskGraph {N : ℕ} (ev : Fin N → ℂ) (r : ℝ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun a b => ‖ev a - ev b‖ ≤ 2 * r

/-- The union of the disks of radius $r$ about the $\lambda_j$ in the component of $i$. -/
private def compDisks {N : ℕ} (ev : Fin N → ℂ) (r : ℝ) (i : Fin N) : Set ℂ :=
  ⋃ j ∈ {j | (diskGraph ev r).Reachable i j}, Metric.closedBall (ev j) r

private theorem mem_compDisks {N : ℕ} {ev : Fin N → ℂ} {r : ℝ} {i : Fin N} {z : ℂ} :
    z ∈ compDisks ev r i ↔ ∃ j, (diskGraph ev r).Reachable i j ∧ ‖z - ev j‖ ≤ r := by
  simp [compDisks, Complex.dist_eq]

private theorem reachable_of_norm_sub_le {N : ℕ} {ev : Fin N → ℂ} {r : ℝ} {j k : Fin N}
    (h : ‖ev j - ev k‖ ≤ 2 * r) : (diskGraph ev r).Reachable j k := by
  by_cases hjk : j = k
  · rw [hjk]
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hjk, Or.inl h⟩)

/-- Two centers in one component are within $2rn$ for $n + 1$ indices. -/
private theorem norm_sub_le_of_reachable {n : ℕ} {ev : Fin (n + 1) → ℂ} {r : ℝ} (hr : 0 ≤ r)
    {i j : Fin (n + 1)} (h : (diskGraph ev r).Reachable i j) : ‖ev i - ev j‖ ≤ 2 * r * n := by
  classical
  have hwalk : ∀ {a b : Fin (n + 1)} (q : (diskGraph ev r).Walk a b),
      ‖ev a - ev b‖ ≤ 2 * r * q.length := by
    intro a b q
    induction q with
    | nil => simp
    | @cons a b c hadj q ih =>
      have h1 : ‖ev a - ev b‖ ≤ 2 * r := by
        rcases ((SimpleGraph.fromRel_adj _ _ _).mp hadj).2 with h | h
        · exact h
        · rwa [norm_sub_rev]
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      calc ‖ev a - ev c‖ ≤ ‖ev a - ev b‖ + ‖ev b - ev c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * r * (q.length + 1) := by linarith
  obtain ⟨p⟩ := h
  have hlen : p.toPath.1.length ≤ n := by
    have := p.toPath.2.length_lt; simp only [Fintype.card_fin] at this; omega
  exact (hwalk p.toPath.1).trans (by gcongr)

/-- The components are separated: some $\delta > 0$ has
$\lvert\lambda_j - \lambda_k\rvert \le 2r$ whenever
$\lvert\lambda_j - \lambda_k\rvert < 2r + \delta$. -/
private theorem exists_pos_norm_sub_lt_imp {N : ℕ} (ev : Fin N → ℂ) (r : ℝ) :
    ∃ δ > 0, ∀ j k, ‖ev j - ev k‖ < 2 * r + δ → ‖ev j - ev k‖ ≤ 2 * r := by
  have h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j k, ‖ev j - ev k‖ < 2 * r + δ → ‖ev j - ev k‖ ≤ 2 * r :=
    Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k => by
      by_cases hjk : ‖ev j - ev k‖ ≤ 2 * r
      · exact Eventually.of_forall fun _ _ => hjk
      · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (sub_pos.2 (not_le.1 hjk)))]
          with δ hδ hlt
        linarith
  obtain ⟨δ, h1, h2⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨δ, h2, h1⟩

/-- The times at which some listing lies in the component disks form a closed set. -/
private theorem isClosed_setOf_exists_forall_mem_compDisks {N : ℕ}
    {P : ℝ → Matrix (Fin N) (Fin N) ℂ} (hP : Continuous P) (ev : Fin N → ℂ) (r : ℝ) :
    IsClosed {t | ∃ e, IsEigenvalueListing (P t) e ∧ ∀ i, e i ∈ compDisks ev r i} := by
  refine IsSeqClosed.isClosed fun t t₀ ht hlim => ?_
  choose e he hc using ht
  have hK : IsCompact (Set.univ.pi (compDisks ev r)) := isCompact_univ_pi fun i =>
    (Set.toFinite _).isCompact_biUnion fun j _ => isCompact_closedBall _ _
  obtain ⟨e₀, he₀, φ, hφ, hlim'⟩ := hK.tendsto_subseq (x := e) fun m i _ => hc m i
  refine ⟨e₀, ?_, fun i => he₀ i (Set.mem_univ i)⟩
  exact isClosed_setOf_isEigenvalueListing.mem_of_tendsto
    (((hP.tendsto t₀).comp (hlim.comp hφ.tendsto_atTop)).prodMk_nhds hlim')
    (Eventually.of_forall fun m => he (φ m))

/-- The times at which no listing lies in the component disks form a closed set, when the
spectrum stays within $r$ of the centers. -/
private theorem isClosed_setOf_not_exists_forall_mem_compDisks {N : ℕ}
    {P : ℝ → Matrix (Fin N) (Fin N) ℂ} (hP : Continuous P) (ev : Fin N → ℂ) (r : ℝ)
    (hspec : ∀ t, ∀ μ ∈ spectrum ℂ (P t), ∃ k, ‖μ - ev k‖ ≤ r) :
    IsClosed {t | ¬ ∃ e, IsEigenvalueListing (P t) e ∧ ∀ i, e i ∈ compDisks ev r i} := by
  refine IsSeqClosed.isClosed fun t t₀ ht hlim => ?_
  rintro ⟨e, he, hc⟩
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_norm_sub_lt_imp ev r
  choose f hf using fun m => exists_isEigenvalueListing (P (t m))
  obtain ⟨φ, σ, e', -, he', hlim'⟩ :=
    exists_tendsto_isEigenvalueListing ((hP.tendsto t₀).comp hlim) hf
  obtain ⟨π, hπ⟩ := he'.exists_equiv_eq he
  obtain ⟨m, hm⟩ := (hlim'.eventually (Metric.ball_mem_nhds e' hδ)).exists
  refine ht (φ m) ⟨f (φ m) ∘ σ m ∘ π.symm, ((hf (φ m)).comp_equiv _).comp_equiv _, fun i => ?_⟩
  set x := f (φ m) (σ m (π.symm i))
  have hx : ‖x - e i‖ < δ := by
    have h1 := (dist_le_pi_dist (f (φ m) ∘ σ m) e' (π.symm i)).trans_lt hm
    simpa only [hπ, Function.comp_apply, Equiv.apply_symm_apply, Complex.dist_eq] using h1
  obtain ⟨k, hk⟩ := hspec _ x ((hf (φ m)).spectrum_eq_range ▸ Set.mem_range_self _)
  obtain ⟨j, hj, hej⟩ := mem_compDisks.mp (hc i)
  have hjk : ‖ev j - ev k‖ ≤ 2 * r := hsep j k <| by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (ev j) (e i) (ev k)
    have h2 := norm_sub_le_norm_sub_add_norm_sub (e i) x (ev k)
    have h3 : ‖ev j - e i‖ ≤ r := by rw [norm_sub_rev]; exact hej
    have h4 : ‖e i - x‖ < δ := by rw [norm_sub_rev]; exact hx
    linarith
  exact mem_compDisks.mpr ⟨k, hj.trans (reachable_of_norm_sub_le hjk), hk⟩

/-- **Listings along a path that stays near the spectrum** (the component argument of the
Ostrowski–Elsner theorem): let $t \mapsto \mathbf{P}(t)$ be a continuous path of complex
matrices of order $n + 1$, $\boldsymbol{\lambda}$ a listing of the eigenvalues of
$\mathbf{P}(0)$, $r \ge 0$, and every eigenvalue of every $\mathbf{P}(t)$ within $r$ of some
$\lambda_k$. Then for every $t$ some listing $\boldsymbol{\mu}$ of the eigenvalues of
$\mathbf{P}(t)$ has $\lvert\mu_i - \lambda_i\rvert \le (2n + 1)r$ for every $i$. The
continuity argument behind [BanksGarzaVargasSrivastava2025, Lemma 1.2]. -/
theorem exists_isEigenvalueListing_norm_sub_le_of_continuous {n : ℕ}
    {P : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hP : Continuous P) {ev : Fin (n + 1) → ℂ}
    (hev : IsEigenvalueListing (P 0) ev) {r : ℝ} (hr : 0 ≤ r)
    (hspec : ∀ t, ∀ μ ∈ spectrum ℂ (P t), ∃ k, ‖μ - ev k‖ ≤ r) (t : ℝ) :
    ∃ e, IsEigenvalueListing (P t) e ∧ ∀ i, ‖e i - ev i‖ ≤ (2 * n + 1) * r := by
  set S := {t | ∃ e, IsEigenvalueListing (P t) e ∧ ∀ i, e i ∈ compDisks ev r i}
  have hS : S = Set.univ := by
    refine IsClopen.eq_univ ⟨isClosed_setOf_exists_forall_mem_compDisks hP ev r,
      isClosed_compl_iff.mp (isClosed_setOf_not_exists_forall_mem_compDisks hP ev r hspec)⟩
      ⟨0, ev, hev, fun i => mem_compDisks.mpr ⟨i, SimpleGraph.Reachable.refl i, by simpa using hr⟩⟩
  obtain ⟨e, he, hc⟩ : t ∈ S := hS ▸ Set.mem_univ t
  refine ⟨e, he, fun i => ?_⟩
  obtain ⟨j, hj, hej⟩ := mem_compDisks.mp (hc i)
  have hij := norm_sub_le_of_reachable hr hj
  calc ‖e i - ev i‖ ≤ ‖e i - ev j‖ + ‖ev j - ev i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ r + 2 * r * n := by rw [norm_sub_rev (ev j)]; exact add_le_add hej hij
    _ = (2 * n + 1) * r := by ring

/-- The matching with the eigenvalues of the matrix of smaller norm as centers. -/
private theorem exists_isEigenvalueListing_norm_sub_le_rpow_of_le {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hAA' : specNorm A ≤ specNorm A')
    {ev : Fin (n + 1) → ℂ} (hev : IsEigenvalueListing A ev) :
    ∃ ev' : Fin (n + 1) → ℂ, IsEigenvalueListing A' ev' ∧ ∀ i,
      ‖ev' i - ev i‖ ≤ (2 * n + 1) * (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
        specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
  set c : ℝ → ℝ := fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)
  set P : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun t => A + (c t : ℂ) • (A' - A)
  have hP : Continuous P := continuous_const.add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)).smul
      continuous_const)
  have hP0 : P 0 = A := by simp [P, c]
  have hP1 : P 1 = A' := by simp [P, c]
  have hα : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hβ : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hspec : ∀ t, ∀ μ ∈ spectrum ℂ (P t), ∃ k, ‖μ - ev k‖ ≤
      (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
        specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
    intro t μ hμ
    obtain ⟨ν, hν, hb⟩ := exists_norm_sub_le_rpow_of_mem_spectrum (A := A) hμ
    obtain ⟨k, rfl⟩ : ν ∈ Set.range ev := hev.spectrum_eq_range ▸ hν
    refine ⟨k, hb.trans ?_⟩
    have hc0 : 0 ≤ c t := (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.1
    have hc1 : c t ≤ 1 := (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.2
    have hd : specNorm (P t - A) ≤ specNorm (A' - A) := by
      rw [show P t - A = (c t : ℂ) • (A' - A) by simp [P], specNorm_smul, Complex.norm_real,
        Real.norm_of_nonneg hc0]
      exact mul_le_of_le_one_left (specNorm_nonneg _) hc1
    have hn : specNorm (P t) ≤ specNorm A' := by
      have he : P t = ((1 - c t : ℝ) : ℂ) • A + (c t : ℂ) • A' := by
        simp only [P, smul_sub, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]; abel
      rw [he]
      refine (specNorm_add_le _ _).trans ?_
      rw [specNorm_smul, specNorm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (sub_nonneg.mpr hc1), Real.norm_of_nonneg hc0]
      nlinarith
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) hα)
      (Real.rpow_le_rpow (specNorm_nonneg _) hd hβ) (by positivity) (by positivity)
  obtain ⟨e, he, hb⟩ := exists_isEigenvalueListing_norm_sub_le_of_continuous hP (hP0 ▸ hev)
    (by positivity) hspec 1
  rw [hP1] at he
  exact ⟨e, he, fun i => (hb i).trans (le_of_eq (by ring))⟩

/-- **The Ostrowski–Elsner matching** ([BanksGarzaVargasSrivastava2025, Lemma 1.2]; the constant
$2N - 1$ of the component argument at the order $N = n + 1$, where Bhatia, Elsner and Krause
have $4$): for complex matrices $\mathbf{A}, \mathbf{A}'$ of order $n + 1$ and every listing
$\boldsymbol{\lambda}$ of the eigenvalues of $\mathbf{A}$ there is a listing
$\boldsymbol{\lambda}'$ of those of $\mathbf{A}'$ with, for every $i$,
$$\lvert\lambda'_i - \lambda_i\rvert \le
  (2n + 1)(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/(n + 1)}
  \|\mathbf{A}' - \mathbf{A}\|_2^{1/(n + 1)}.$$ -/
theorem exists_isEigenvalueListing_norm_sub_le_rpow {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ev : Fin (n + 1) → ℂ}
    (hev : IsEigenvalueListing A ev) :
    ∃ ev' : Fin (n + 1) → ℂ, IsEigenvalueListing A' ev' ∧ ∀ i,
      ‖ev' i - ev i‖ ≤ (2 * n + 1) * (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
        specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
  rcases le_total (specNorm A) (specNorm A') with h | h
  · exact exists_isEigenvalueListing_norm_sub_le_rpow_of_le h hev
  · obtain ⟨d', hd'⟩ := exists_isEigenvalueListing A'
    obtain ⟨e, he, hb⟩ := exists_isEigenvalueListing_norm_sub_le_rpow_of_le h hd'
    obtain ⟨π, hπ⟩ := hev.exists_equiv_eq he
    refine ⟨d' ∘ π, hd'.comp_equiv π, fun i => ?_⟩
    have h' := hb (π i)
    rw [norm_sub_rev, add_comm (specNorm A'), ← specNorm_neg (A - A'), neg_sub] at h'
    subst hπ
    exact h'

/-- **The forward error through a diagonalizable matrix** ([BanksGarzaVargasSrivastava2025,
Corollary 1.3], the matching step): let $\mathbf{A} + \mathbf{E}_1 = \mathbf{V}
\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$
and eigenvalues separated by $g > 0$, and $\|\mathbf{E}_2\|_2 \le g/(16(n + 1)B)$. Then every
listing $\mathbf{r}$ of the eigenvalues of $\mathbf{A} + \mathbf{E}_1 + \mathbf{E}_2$ is matched
to a listing $\boldsymbol{\lambda}$ of those of $\mathbf{A}$ with, for every $i$,
$$\lvert r_i - \lambda_i\rvert \le B\|\mathbf{E}_2\|_2 + (2n + 1)(2\|\mathbf{A}\|_2 +
  \|\mathbf{E}_1\|_2)^{1 - 1/(n + 1)}\|\mathbf{E}_1\|_2^{1/(n + 1)}.$$ -/
theorem exists_isEigenvalueListing_norm_sub_le_of_class {n : ℕ}
    {A E₁ E₂ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {B g : ℝ}
    (hV : IsUnit V) (hAV : (A + E₁) * V = V * Matrix.diagonal d)
    (hB : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hE₂ : specNorm E₂ ≤ g / (16 * (n + 1) * B)) {roots : Fin (n + 1) → ℂ}
    (hroots : IsEigenvalueListing (A + E₁ + E₂) roots) :
    ∃ ev : Fin (n + 1) → ℂ, IsEigenvalueListing A ev ∧ ∀ i,
      ‖roots i - ev i‖ ≤ B * specNorm E₂ + (2 * n + 1) *
        (2 * specNorm A + specNorm E₁) ^ (1 - 1 / ((n : ℝ) + 1)) *
          specNorm E₁ ^ (1 / ((n : ℝ) + 1)) := by
  -- Bauer–Fike with a matching: `roots` is a relabelling of `d'` with `|d' i - d i| ≤ B ‖E₂‖`
  obtain ⟨V', d', hV', hAV', -, -, hm⟩ :=
    exists_pseudoConditionNumber_add_le_and_norm_sub_le hV hAV hB hg hgap hE₂
  have hlin := norm_sub_le_of_matching hV hAV hB hg hgap hE₂ hV' hAV' hm
  have hd' : IsEigenvalueListing (A + E₁ + E₂) d' :=
    isEigenvalueListing_of_mul_eq_mul_diagonal ((Matrix.isUnit_iff_isUnit_det V').mp hV') hAV'
  obtain ⟨π, hπ⟩ := hroots.exists_equiv_eq hd'
  -- Ostrowski–Elsner from `A + E₁` to `A`
  have hd : IsEigenvalueListing (A + E₁) d :=
    isEigenvalueListing_of_mul_eq_mul_diagonal ((Matrix.isUnit_iff_isUnit_det V).mp hV) hAV
  obtain ⟨ev', hev', hb⟩ := exists_isEigenvalueListing_norm_sub_le_rpow (A' := A) hd
  refine ⟨ev' ∘ π, hev'.comp_equiv π, fun i => ?_⟩
  have hα : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hS : specNorm (A + E₁) + specNorm A ≤ 2 * specNorm A + specNorm E₁ := by
    linarith [specNorm_add_le A E₁]
  have hE : specNorm (A - (A + E₁)) = specNorm E₁ := by
    rw [sub_add_cancel_left, specNorm_neg]
  have h2 : ‖d (π i) - ev' (π i)‖ ≤ (2 * n + 1) *
      (2 * specNorm A + specNorm E₁) ^ (1 - 1 / ((n : ℝ) + 1)) *
        specNorm E₁ ^ (1 / ((n : ℝ) + 1)) := by
    rw [norm_sub_rev]
    refine (hb (π i)).trans ?_
    rw [hE]
    gcongr
  rw [hπ, Function.comp_apply, Function.comp_apply]
  calc ‖d' (π i) - ev' (π i)‖ ≤ ‖d' (π i) - d (π i)‖ + ‖d (π i) - ev' (π i)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (hlin (π i)) h2

/-- **The Schur diagonal of a perturbed matrix of the class is separated**: let $\mathbf{X}$ be of
the class $(B, \Gamma)$ with $\Gamma > 0$ and order $n + 1$, $\mathbf{W}$ unitary and $\mathbf{T}$
upper triangular with $\mathbf{X} + \mathbf{E} = \mathbf{W}\mathbf{T}\mathbf{W}^{\mathsf H}$ and
$\|\mathbf{E}\|_2 \le \Gamma/(16(n + 1)B)$. Then
$\lvert t_{ii} - t_{jj}\rvert \ge \tfrac78\Gamma$ for $i \ne j$: the diagonal lists the eigenvalues
of $\mathbf{X} + \mathbf{E}$, each within
$B\|\mathbf{E}\|_2 \le \Gamma/16$ of its own eigenvalue of $\mathbf{X}$
(`NLAlib.exists_isEigenvalueListing_norm_sub_le_of_class` with $\mathbf{E}_1 = \mathbf{0}$). -/
theorem IsConditionedDiagonalizable.le_norm_sub_diag_of_add_eq {n : ℕ} {B Γ : ℝ}
    {X E W T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hX : IsConditionedDiagonalizable B Γ X)
    (hΓ : 0 < Γ) (hW : HasOrthonormalCols W) (hT : T.IsUpperTriangular)
    (hXE : X + E = W * T * Wᴴ) (hE : specNorm E ≤ Γ / (16 * (n + 1) * B)) :
    ∀ i j, i ≠ j → 7 / 8 * Γ ≤ ‖T i i - T j j‖ := by
  obtain ⟨V, d, hV, hXV, hB, hgap⟩ := hX
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  obtain ⟨V', d', hV', hXV', -, hsep⟩ :=
    exists_pseudoConditionNumber_le_and_le_norm_sub hV hXV hB hΓ hgap hE
  have hBE : 2 * B * specNorm E ≤ Γ / 8 := by
    calc 2 * B * specNorm E ≤ 2 * B * (Γ / (16 * (n + 1) * B)) := by gcongr
      _ = Γ / (8 * (n + 1)) := by field_simp; ring
      _ ≤ Γ / 8 := by gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hT' : Wᴴ * (X + E) * W = T := by
    rw [hXE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hW.conjTranspose_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, hW.conjTranspose_mul_self, Matrix.mul_one]
  have hdiag : IsEigenvalueListing (X + E) fun i => T i i := by
    have := hW.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul (A := X + E)
      (by rw [hT']; exact hT)
    simpa only [hT'] using this
  have hd' : IsEigenvalueListing (X + E) d' :=
    isEigenvalueListing_of_mul_eq_mul_diagonal ((Matrix.isUnit_iff_isUnit_det V').mp hV') hXV'
  obtain ⟨π, hπ⟩ := hdiag.exists_equiv_eq hd'
  intro i j hij
  have hi : T i i = d' (π i) := congrFun hπ i
  have hj : T j j = d' (π j) := congrFun hπ j
  rw [hi, hj]
  linarith [hsep (π i) (π j) (π.injective.ne hij)]

end NLAlib
