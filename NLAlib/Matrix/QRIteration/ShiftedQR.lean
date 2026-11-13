/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import NLAlib.Matrix.Factorizations.GivensHessenberg
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# The Hessenberg shifted QR step and its potential

The objects of the exact-arithmetic analysis of the Hessenberg shifted QR algorithm
[BanksGarzaVargasSrivastava2021], and their basic theory. A square matrix is indexed by
`Fin (n + 1)`, so that its last row $\mathbf{e}_n^{\mathsf{H}}\mathbf{H}$ is `H (Fin.last n)` and
its $n$ subdiagonal entries are $\mathbf{H}_{i+1,i}$ for `i : Fin n`.

* `NLAlib.IsDecoupled δ H`: some subdiagonal entry has modulus at most $\delta\|\mathbf{H}\|_2$
  (with $\delta = 0$: $\mathbf{H}$ is reduced).
* `NLAlib.hessenbergPotential k H`: the geometric mean $\psi_k(\mathbf{H})$ of the last $k$
  subdiagonal moduli, the potential that tracks convergence.
* `NLAlib.shiftPoly ss`: the monic polynomial $\prod_{s}(z - s)$ with roots the list `ss`.
* `NLAlib.shiftedQRStep H s`: one single-shift QR step
  $\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$, $\mathbf{Q}$ the unitary factor of Givens QR of
  $\mathbf{H} - s\mathbf{I}$; `NLAlib.multiShiftedQRStep H ss` composes them, which is the degree
  $k$ step with shift polynomial `shiftPoly ss` (the implicit QR step of the paper, in exact
  arithmetic).
* `NLAlib.trailingBlock k H`, `NLAlib.ritzValues k H`: the trailing $k \times k$ block and its
  eigenvalues, the Ritz values.

The step is a specification, not an implementation: Givens coefficients take exact square roots,
the definitions are noncomputable and carry no cost. The finite-precision algorithm of
[BanksGarzaVargasSrivastava2022] is to refine them (design note
`docs/design/Eigensolvers-ShiftedQR.md`, §9).

The results: the last row of $p(\mathbf{H})$ for upper Hessenberg $\mathbf{H}$ and the
variational formula for the potential (Lemma 2.3 there); the step keeps the Hessenberg form,
the norm and the eigenvector condition number, and is a QR step of the shift polynomial
([BanksGarzaVargasSrivastava2022, Lemma 3.2]); the potential after the step is at most
$\tau_p(\mathbf{H})$ (Lemma 2.5 there); and the singular case, which the paper treats in one line:
a singular shift decouples exactly, and an exact zero on the subdiagonal persists.

## Main definitions

* `NLAlib.IsDecoupled`, `NLAlib.hessenbergPotential`, `NLAlib.shiftPoly`,
  `NLAlib.shiftedQRStep`, `NLAlib.multiShiftedQRStep`, `NLAlib.trailingBlock`,
  `NLAlib.ritzValues`.

## Main results

* `NLAlib.IsUpperHessenberg.aeval_apply_last_eq_zero`,
  `NLAlib.IsUpperHessenberg.aeval_apply_last_eq_prod`: the last row of $p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval`,
  `NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq`: the variational formula
  $\psi_k(\mathbf{H})^k = \min_p\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$.
* `NLAlib.hessenbergPotential_le_specNorm`, `NLAlib.isDecoupled_of_hessenbergPotential_le`.
* `NLAlib.IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep`,
  `NLAlib.specNorm_multiShiftedQRStep`,
  `NLAlib.exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep`: invariants of the step.
* `NLAlib.IsUpperHessenberg.exists_isQR_aeval_shiftPoly`: the step is a QR step of
  $p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le`,
  `NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le`: the
  potential after the step is at most $\tau_p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep`,
  `NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero`: a reduced
  matrix stays reduced, and a singular shift polynomial decouples.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- A square matrix is **$\delta$-decoupled** if some subdiagonal entry is small relative to
the norm: $\lvert\mathbf{H}_{i+1,i}\rvert \le \delta\|\mathbf{H}\|_2$ for some $i < n$. With
$\delta = 0$ this says that $\mathbf{H}$ is reduced (a subdiagonal entry vanishes).
[BanksGarzaVargasSrivastava2021, §1], where the decoupling time is the first QR step at which
this holds. -/
def IsDecoupled (δ : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  ∃ i : Fin n, ‖H i.succ i.castSucc‖ ≤ δ * specNorm H

/-- An upper Hessenberg matrix is unreduced exactly when it has no zero-threshold
decoupling. [BanksGarzaVargasSrivastava2021, §1]. -/
theorem IsUpperHessenberg.isUnreducedHessenberg_iff_not_isDecoupled
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) :
    IsUnreducedHessenberg H ↔ ¬ IsDecoupled 0 H := by
  simp [isUnreducedHessenberg_iff, hH, IsDecoupled]

/-- The **potential** $\psi_k(\mathbf{H})$: the geometric mean of the moduli of the last $k$
subdiagonal entries, $\psi_k(\mathbf{H}) = \bigl(\prod_{n - k \le i < n}
\lvert\mathbf{H}_{i+1,i}\rvert\bigr)^{1/k}$ (indices from $0$; for $k > n$ all $n$ entries
enter). [BanksGarzaVargasSrivastava2021, Definition 2.2], where the product is printed with
$k + 1$ factors; $k$ is meant (the proof of Lemma 2.3 there uses $k$). -/
noncomputable def hessenbergPotential (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  (∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖) ^
    ((k : ℝ)⁻¹)

/-- The monic **shift polynomial** $\prod_{s \in \mathrm{ss}} (z - s)$ of a list of shifts. -/
noncomputable def shiftPoly (ss : List ℂ) : Polynomial ℂ :=
  (ss.map fun s => Polynomial.X - Polynomial.C s).prod

/-- One **single-shift QR step** with shift $s$: with $\mathbf{Q}$ the unitary factor of Givens
QR of $\mathbf{H} - s\mathbf{I}$ (`NLAlib.givensHessenbergQ`), the matrix
$\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q} = \mathbf{R}\mathbf{Q} + s\mathbf{I}$. On an upper
Hessenberg matrix it is the exact-arithmetic implicit QR step of
[BanksGarzaVargasSrivastava2021, Definition 2.1]. Givens QR never breaks down, so the step is
defined also when $\mathbf{H} - s\mathbf{I}$ is singular, and it keeps the Hessenberg form then.
[GolubVanLoan2013, §7.5.2].
Algorithm: shifted-qr (specification) -/
noncomputable def shiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))ᴴ * H *
    givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

/-- The **multi-shift QR step**: the single-shift steps with the shifts of `ss` in order,
$\mathsf{multiShiftedQRStep}(\mathbf{H}, [s_1, \dots, s_k]) =
\mathsf{shiftedQRStep}(\cdots\mathsf{shiftedQRStep}(\mathbf{H}, s_1)\cdots, s_k)$. It is a QR
step with shift polynomial $\prod_i (z - s_i)$ (composition, [BanksGarzaVargasSrivastava2022,
Lemma 3.2]), and the degree $k$ implicit QR step of the paper in exact arithmetic. -/
noncomputable def multiShiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  ss.foldl shiftedQRStep H

/-- The **trailing $k \times k$ block** $\mathbf{H}_{(k)}$: the principal submatrix on the last
$k$ indices $n + 1 - k, \dots, n$ (for $k > n + 1$ the indices are clamped at $n$, a junk value
no statement uses). -/
def trailingBlock (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  H.submatrix (fun i : Fin k => ⟨min (n + 1 - k + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩)
    (fun i : Fin k => ⟨min (n + 1 - k + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩)

/-- The **Ritz values** of order $k$: the eigenvalues of the trailing block
$\mathbf{H}_{(k)}$, with multiplicity, as a list (the roots of the characteristic polynomial
$\chi_k$ of $\mathbf{H}_{(k)}$, in an unspecified order).
[BanksGarzaVargasSrivastava2021, §1.1]. -/
noncomputable def ritzValues (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : List ℂ :=
  (trailingBlock k H).charpoly.roots.toList

/-! ### The potential and the last row of a polynomial in a Hessenberg matrix -/

/-- The $k$-th power of the potential is the product of the last $k$ subdiagonal moduli:
for $k \ge 1$,
$\psi_k(\mathbf{H})^k = \prod_{n - k \le i < n}\lvert\mathbf{H}_{i+1,i}\rvert$. -/
theorem hessenbergPotential_pow {k : ℕ} (hk : 0 < k) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    hessenbergPotential k H ^ k =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ := by
  unfold hessenbergPotential
  exact Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => norm_nonneg _) hk.ne'

/-- The potential is nonnegative. -/
theorem hessenbergPotential_nonneg (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    0 ≤ hessenbergPotential k H :=
  Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) _

/-- The last row of $\mathbf{H}^i$ vanishes at columns $j$ with $j + i < n$. -/
private theorem pow_apply_last_eq_zero {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (i : ℕ) :
    ∀ j : Fin (n + 1), (j : ℕ) + i < n → (H ^ i) (Fin.last n) j = 0 := by
  induction i with
  | zero =>
    intro j hj
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  | succ i ih =>
    intro j hj
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : (j : ℕ) + 1 < (m : ℕ)
    · rw [hH m j hm, mul_zero]
    · rw [ih m (by omega), zero_mul]

/-- **The last row of $p(\mathbf{H})$ is supported on the last $k + 1$ columns**: for upper
Hessenberg $\mathbf{H}$ and a polynomial $p$ of degree at most $k$,
$p(\mathbf{H})_{n,j} = 0$ for $j + k < n$. [BanksGarzaVargasSrivastava2021, proof of
Lemma 2.3]. -/
theorem IsUpperHessenberg.aeval_apply_last_eq_zero {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {p : Polynomial ℂ} {k : ℕ} (hp : p.natDegree ≤ k)
    {j : Fin (n + 1)} (hj : (j : ℕ) + k < n) : Polynomial.aeval H p (Fin.last n) j = 0 := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Matrix.smul_apply, pow_apply_last_eq_zero hH i j (by omega), smul_zero]

/-- Helper: the corner entries of the last row of $\mathbf{H}^i$ are the products of the last $i$
subdiagonal entries. -/
private theorem pow_apply_last_eq_prod {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (i : ℕ) :
    ∀ j : Fin (n + 1), (j : ℕ) + i = n →
      (H ^ i) (Fin.last n) j =
        ∏ l ∈ Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + i), H l.succ l.castSucc := by
  induction i with
  | zero =>
    intro j hj
    have hj' : j = Fin.last n := Fin.ext (by simpa using hj)
    subst hj'
    have hempty : Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + 0) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun l _ => ?_
      have := l.isLt
      omega
    rw [hempty, Finset.prod_empty, pow_zero, Matrix.one_apply_eq]
  | succ i ih =>
    intro j hj
    have hjn : (j : ℕ) < n := by omega
    have hfilt : Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + (i + 1)) =
        insert ⟨j, hjn⟩ (Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + i)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotin : (⟨j, hjn⟩ : Fin n) ∉
        Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hfilt, Finset.prod_insert hnotin, pow_succ, Matrix.mul_apply,
      Finset.sum_eq_single (⟨j + 1, by omega⟩ : Fin (n + 1))]
    · rw [ih ⟨j + 1, by omega⟩ (by change (j : ℕ) + 1 + i = n; omega), mul_comm]
      rfl
    · intro m _ hm
      have hmv : (m : ℕ) ≠ j + 1 := fun h => hm (Fin.ext h)
      by_cases hc : (j : ℕ) + 1 < m
      · rw [hH m j hc, mul_zero]
      · rw [pow_apply_last_eq_zero hH i m (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **The corner entry of the last row of $p(\mathbf{H})$ is the product of subdiagonals**: for
upper Hessenberg $\mathbf{H}$, monic $p$ of degree $k$ and the column $j$ with $j + k = n$,
$$p(\mathbf{H})_{n,j} = \prod_{n - k \le i < n}\mathbf{H}_{i+1,i}\,.$$
[BanksGarzaVargasSrivastava2021, proof of Lemma 2.3]. -/
theorem IsUpperHessenberg.aeval_apply_last_eq_prod {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {p : Polynomial ℂ} (hp : p.Monic) {k : ℕ} (hpk : p.natDegree = k)
    {j : Fin (n + 1)} (hj : (j : ℕ) + k = n) :
    Polynomial.aeval H p (Fin.last n) j =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), H i.succ i.castSucc := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply, hpk, Finset.sum_range_succ,
    Finset.sum_eq_zero fun i hi => ?_, zero_add]
  · have hc : p.coeff k = 1 := by rw [← hpk]; exact hp.coeff_natDegree
    rw [Matrix.smul_apply, hc, one_smul]
    exact pow_apply_last_eq_prod hH k j hj
  · rw [Finset.mem_range] at hi
    rw [Matrix.smul_apply, pow_apply_last_eq_zero hH i j (by omega), smul_zero]

/-- **The potential bounds every monic polynomial's last row from below**: for upper Hessenberg
$\mathbf{H}$, $1 \le k \le n$ and monic $p$ of degree $k$,
$\psi_k(\mathbf{H})^k \le \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$.
[BanksGarzaVargasSrivastava2021, Lemma 2.3], the lower bound. -/
theorem IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {p : Polynomial ℂ}
    (hp : p.Monic) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hpk : p.natDegree = k) :
    hessenbergPotential k H ^ k ≤ ‖WithLp.toLp 2 (Polynomial.aeval H p (Fin.last n))‖ := by
  have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Polynomial.aeval H p (Fin.last n)))
    ⟨n - k, by omega⟩
  have h2 := IsUpperHessenberg.aeval_apply_last_eq_prod hH hp hpk (j := ⟨n - k, by omega⟩)
    (by change n - k + k = n; omega)
  rw [hessenbergPotential_pow hk H, ← norm_prod, ← h2]
  exact h1

/-- The last row of $\mathbf{H}^i$, $i \le k$, on the last $k$ columns is the last row of
$\mathbf{H}_{(k)}^i$. -/
private theorem IsUpperHessenberg.pow_apply_last_trailing
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) {i : ℕ} (hi : i ≤ k) (j : Fin k) :
    (H ^ i) (Fin.last n) ⟨min (n + 1 - k + j) n, Nat.lt_succ_of_le (min_le_right _ _)⟩ =
      (trailingBlock k H ^ i) ⟨k - 1, by omega⟩ j := by
  induction i generalizing j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.ext_iff, Fin.val_last]
    congr 1
    apply propext
    omega
  | succ i ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective
      (fun j' : Fin k => (⟨min (n + 1 - k + j') n, Nat.lt_succ_of_le (min_le_right _ _)⟩ :
        Fin (n + 1))) ?_ _ _ ?_ ?_
    · intro a b hab
      simp only [Fin.mk.injEq] at hab
      ext; omega
    · intro c hc
      have hc' : (c : ℕ) + k ≤ n := by
        by_contra hcon
        exact hc ⟨⟨c - (n + 1 - k), by omega⟩, Fin.ext (by simp only; omega)⟩
      have := hH.aeval_apply_last_eq_zero (p := Polynomial.X ^ i) (k := i)
        (by rw [Polynomial.natDegree_X_pow]) (j := c) (by omega)
      rw [Polynomial.aeval_X_pow] at this
      rw [this, zero_mul]
    · intro j'
      rw [ih (by omega) j']
      rfl

/-- **The variational formula for the potential**: for upper Hessenberg $\mathbf{H}$ and
$1 \le k \le n$, the characteristic polynomial $\chi_k$ of the trailing block
$\mathbf{H}_{(k)}$ attains the lower bound,
$$\|\mathbf{e}_n^{\mathsf{H}}\chi_k(\mathbf{H})\| = \psi_k(\mathbf{H})^k\,,$$
so $\psi_k(\mathbf{H})^k = \min_p \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$ over monic $p$ of
degree $k$. [BanksGarzaVargasSrivastava2021, Lemma 2.3]; [TrefethenBau1997, Theorem 34.1]. -/
theorem IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) :
    ‖WithLp.toLp 2 (Polynomial.aeval H (trailingBlock k H).charpoly (Fin.last n))‖ =
      hessenbergPotential k H ^ k := by
  set T := trailingBlock k H
  have hdeg : T.charpoly.natDegree = k := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  set v := Polynomial.aeval H T.charpoly (Fin.last n)
  have htrail : ∀ c : Fin (n + 1), n + 1 - k ≤ (c : ℕ) → v c = 0 := by
    intro c hc
    have hc' : c = ⟨min (n + 1 - k + (⟨c - (n + 1 - k), by omega⟩ : Fin k)) n,
        Nat.lt_succ_of_le (min_le_right _ _)⟩ := Fin.ext (by simp only; omega)
    have hT := congrFun (congrFun (Matrix.aeval_self_charpoly T) ⟨k - 1, by omega⟩)
      ⟨c - (n + 1 - k), by omega⟩
    rw [Polynomial.aeval_eq_sum_range] at hT
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at hT
    rw [hc', ← hT]
    simp only [v, Polynomial.aeval_eq_sum_range, Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact congrArg _ (hH.pow_apply_last_trailing hk hkn (j := ⟨c - (n + 1 - k), by omega⟩)
      (by rw [Finset.mem_range] at hi; omega))
  set c₀ : Fin (n + 1) := ⟨n - k, by omega⟩
  have hv : v = Pi.single c₀ (v c₀) := by
    funext c
    by_cases hc : c = c₀
    · subst hc; simp
    · rw [Pi.single_eq_of_ne hc]
      rcases lt_or_ge ((c : ℕ) + k) n with h | h
      · exact hH.aeval_apply_last_eq_zero hdeg.le h
      · exact htrail c (by have : (c : ℕ) ≠ n - k := fun h' => hc (Fin.ext h'); omega)
  rw [hv, PiLp.toLp_single, PiLp.norm_single, show v c₀ = Polynomial.aeval H T.charpoly
    (Fin.last n) c₀ from rfl,
    hH.aeval_apply_last_eq_prod (Matrix.charpoly_monic T) hdeg (by simp only [c₀]; omega),
    norm_prod, hessenbergPotential_pow hk]

/-- The last $k \le n$ subdiagonal indices are $k$ in number. -/
private theorem card_filter_le_add {k : ℕ} (hkn : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).card = k := by
  rw [← Finset.card_map Fin.valEmbedding,
    show (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).map Fin.valEmbedding =
      Finset.Ico (n - k) n by
        ext m
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Ico]
        exact ⟨by rintro ⟨i, hi, rfl⟩; exact ⟨by omega, i.isLt⟩,
          fun ⟨h1, h2⟩ => ⟨⟨m, h2⟩, by change n ≤ m + k; omega, rfl⟩⟩,
    Nat.card_Ico]
  omega

/-- **The potential is at most the norm**: for $1 \le k \le n$,
$\psi_k(\mathbf{H}) \le \|\mathbf{H}\|_2$. [BanksGarzaVargasSrivastava2021, proof of
Theorem 1.6]. -/
theorem hessenbergPotential_le_specNorm {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : hessenbergPotential k H ≤ specNorm H := by
  have hcard := card_filter_le_add hkn
  have hS : 0 ≤ specNorm H := specNorm_nonneg H
  have hP : ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ ≤
      specNorm H ^ k := by
    calc _ ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), specNorm H :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => norm_apply_le_specNorm _ _ _
      _ = specNorm H ^ k := by rw [Finset.prod_const, hcard]
  unfold hessenbergPotential
  calc _ ≤ (specNorm H ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => norm_nonneg _) hP (by positivity)
    _ = specNorm H := Real.pow_rpow_inv_natCast hS hk.ne'

/-- **A small potential means decoupling**: for $1 \le k \le n$ and $\delta \ge 0$, if
$\psi_k(\mathbf{H}) \le \delta\|\mathbf{H}\|_2$ then some subdiagonal entry has
$\lvert\mathbf{H}_{i+1,i}\rvert \le \delta\|\mathbf{H}\|_2$. [BanksGarzaVargasSrivastava2021,
proof of Theorem 1.6]. -/
theorem isDecoupled_of_hessenbergPotential_le {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) {δ : ℝ}
    (hδ : 0 ≤ δ) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : hessenbergPotential k H ≤ δ * specNorm H) : IsDecoupled δ H := by
  have hcard := card_filter_le_add hkn
  have hne : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).Nonempty :=
    ⟨⟨n - k, by omega⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩
  obtain ⟨i0, hi0, hmin⟩ :=
    Finset.exists_min_image _ (fun i : Fin n => ‖H i.succ i.castSucc‖) hne
  have hδS : 0 ≤ δ * specNorm H := mul_nonneg hδ (specNorm_nonneg H)
  have hψ0 : 0 ≤ hessenbergPotential k H :=
    hessenbergPotential_nonneg _ _
  have hmk : ∏ _i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i0.succ i0.castSucc‖ ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ :=
    Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => hmin i hi
  rw [Finset.prod_const, hcard] at hmk
  have h3 : ‖H i0.succ i0.castSucc‖ ^ k ≤ (δ * specNorm H) ^ k :=
    hmk.trans ((hessenbergPotential_pow hk H).symm ▸ pow_le_pow_left₀ hψ0 h k)
  exact ⟨i0, (pow_le_pow_iff_left₀ (norm_nonneg _) hδS hk.ne').mp h3⟩

/-! ### The shift polynomial -/

/-- The shift polynomial is monic. -/
theorem shiftPoly_monic (ss : List ℂ) : (shiftPoly ss).Monic := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    rw [show shiftPoly (s :: ss) = (Polynomial.X - Polynomial.C s) * shiftPoly ss by
      simp [shiftPoly]]
    exact (Polynomial.monic_X_sub_C s).mul ih

/-- The shift polynomial of $k$ shifts has degree $k$. -/
theorem natDegree_shiftPoly (ss : List ℂ) : (shiftPoly ss).natDegree = ss.length := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons s ss ih =>
    rw [show shiftPoly (s :: ss) = (Polynomial.X - Polynomial.C s) * shiftPoly ss by
      simp [shiftPoly], (Polynomial.monic_X_sub_C s).natDegree_mul (shiftPoly_monic ss),
      Polynomial.natDegree_X_sub_C, ih, List.length_cons, add_comm]

/-- The modulus of the shift polynomial is the product of the distances to the shifts:
$\lvert\prod_{s}(z - s)\rvert = \prod_s \lvert z - s\rvert$. -/
theorem norm_eval_shiftPoly (ss : List ℂ) (z : ℂ) :
    ‖(shiftPoly ss).eval z‖ = (ss.map fun s => ‖z - s‖).prod := by
  induction ss with
  | nil => simp [shiftPoly]
  | cons a l ih =>
    simp only [shiftPoly, List.map_cons, List.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_mul] at ih ⊢
    rw [ih]

/-- The shift polynomial does not vanish at a point that is no shift. -/
theorem eval_shiftPoly_ne_zero {ss : List ℂ} {z : ℂ} (h : ∀ s ∈ ss, z ≠ s) :
    (shiftPoly ss).eval z ≠ 0 := by
  rw [shiftPoly, Polynomial.eval_list_prod, List.map_map]
  refine List.prod_ne_zero fun h0 => ?_
  obtain ⟨s, hs, hs0⟩ := List.mem_map.mp h0
  exact h s hs (sub_eq_zero.mp (by simpa using hs0))

/-- The shift polynomial of a concatenation is the product: $p_{a +\!+ b} = p_a\,p_b$. -/
theorem shiftPoly_append (a b : List ℂ) : shiftPoly (a ++ b) = shiftPoly a * shiftPoly b := by
  simp [shiftPoly, List.map_append, List.prod_append]

/-- The shift polynomial of a repeated shift is a power: $p(\mathbf{H}) = (\mathbf{H} -
r\mathbf{I})^k$ for the list of $k$ copies of $r$. -/
theorem aeval_shiftPoly_replicate (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k : ℕ) (r : ℂ) :
    Polynomial.aeval H (shiftPoly (List.replicate k r)) =
      (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ^ k := by
  simp [shiftPoly, List.map_replicate, List.prod_replicate, Algebra.algebraMap_eq_smul_one]

/-! ### The shifted QR step -/

/-- The shifted QR step is $\mathbf{R}\mathbf{Q} + s\mathbf{I}$ for the Givens factors of
$\mathbf{H} - s\mathbf{I}$, for every $\mathbf{H}$. -/
private theorem shiftedQRStep_eq_mul_add_smul_one (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (s : ℂ) :
    shiftedQRStep H s =
      givensHessenbergR (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) *
        givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) + s • 1 := by
  set A := H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA
  set Q := givensHessenbergQ A
  set R := givensHessenbergR A
  have hQR : Q * R = A := givensHessenbergState_fst_mul_snd A _
  have hQQ : Qᴴ * Q = 1 := (hasOrthonormalCols_givensHessenbergQ A).conjTranspose_mul_self
  change Qᴴ * H * Q = _
  calc Qᴴ * H * Q = Qᴴ * (A + s • 1) * Q := by rw [hA, sub_add_cancel]
    _ = (Qᴴ * Q) * R * Q + s • (Qᴴ * Q) := by
      rw [← hQR]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    _ = R * Q + s • 1 := by rw [hQQ, Matrix.one_mul]

/-- The shifted QR step keeps the Hessenberg form: for upper Hessenberg $\mathbf{H}$ and any
shift $s$, `NLAlib.shiftedQRStep` $\mathbf{H}$ $s$ is upper Hessenberg, also when
$\mathbf{H} - s\mathbf{I}$ is singular. -/
theorem IsUpperHessenberg.isUpperHessenberg_shiftedQRStep {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (s : ℂ) : IsUpperHessenberg (shiftedQRStep H s) := by
  have h1 : IsUpperHessenberg (givensHessenbergR (H - s • 1) * givensHessenbergQ (H - s • 1)) :=
    IsUpperHessenberg.isUpperTriangular_mul
      (isUpperTrapezoidal_givensHessenbergR (hH.sub_smul_one s))
      (isUpperHessenberg_givensHessenbergQ _)
  intro i j hij
  rw [shiftedQRStep_eq_mul_add_smul_one, Matrix.add_apply, h1 i j hij, Matrix.smul_apply,
    Matrix.one_apply_ne (fun h => by subst h; omega), smul_zero, add_zero]

/-- The multi-shift QR step keeps the Hessenberg form: for upper Hessenberg $\mathbf{H}$
and any list of shifts, `NLAlib.multiShiftedQRStep` $\mathbf{H}$ `ss` is upper Hessenberg. -/
theorem IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (ss : List ℂ) :
    IsUpperHessenberg (multiShiftedQRStep H ss) := by
  induction ss generalizing H with
  | nil => exact hH
  | cons s ss ih => exact ih (hH.isUpperHessenberg_shiftedQRStep s)

/-- A unitary conjugation commutes with polynomial evaluation:
$p(\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}) =
\mathbf{Q}^{\mathsf{H}}p(\mathbf{H})\mathbf{Q}$. -/
private theorem aeval_conjTranspose_mul_mul
    {H Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hQ : Qᴴ * Q = 1) (p : Polynomial ℂ) :
    Polynomial.aeval (Qᴴ * H * Q) p = Qᴴ * Polynomial.aeval H p * Q := by
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ
  let f : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ →ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    { toFun := fun M => Qᴴ * M * Q
      map_one' := by simp only [Matrix.mul_one, hQ]
      map_mul' := fun A B => by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᴴ, hQQ, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun A B => by simp [Matrix.mul_add, Matrix.add_mul]
      commutes' := fun c => by
        simp [Algebra.algebraMap_eq_smul_one, hQ] }
  exact Polynomial.aeval_algHom_apply f H p

/-- A square Hessenberg matrix has a Givens QR factorization in the square form. -/
private theorem isQR_givensHessenberg_sq {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) :
    IsQR H (givensHessenbergQ H) (givensHessenbergR H) := by
  have h := isQR_givensHessenberg hH (le_refl (n + 1))
  rwa [Fin.castLE_rfl, Matrix.submatrix_id_id] at h

/-- **The multi-shift QR step is a QR step of the shift polynomial**: for upper Hessenberg
$\mathbf{H}$ and shifts $s_1, \dots, s_k$, there are $\mathbf{Q}$ unitary and $\mathbf{R}$
upper triangular with $p(\mathbf{H}) = \mathbf{Q}\mathbf{R}$, $p(z) = \prod_i (z - s_i)$, and
`NLAlib.multiShiftedQRStep` $\mathbf{H}$ `ss` $= \mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$. No
invertibility is assumed. [BanksGarzaVargasSrivastava2022, Lemma 3.2], there for invertible
$p(\mathbf{H})$ with the positive-diagonal factorization. -/
theorem IsUpperHessenberg.exists_isQR_aeval_shiftPoly {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (ss : List ℂ) :
    ∃ Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsQR (Polynomial.aeval H (shiftPoly ss)) Q R ∧ multiShiftedQRStep H ss = Qᴴ * H * Q := by
  induction ss generalizing H with
  | nil =>
    refine ⟨1, 1, ⟨?_, ?_, Matrix.blockTriangular_one⟩, ?_⟩
    · simp [shiftPoly]
    · simp [HasOrthonormalCols]
    · simp [multiShiftedQRStep]
  | cons s ss ih =>
    obtain ⟨Q', R', hQ', hstep'⟩ := ih (hH.isUpperHessenberg_shiftedQRStep s)
    have hQR := isQR_givensHessenberg_sq (hH.sub_smul_one s)
    have hP : Polynomial.aeval H (shiftPoly (s :: ss)) =
        Polynomial.aeval H (shiftPoly ss) * (H - s • 1) := by
      rw [show s :: ss = [s] ++ ss from rfl, shiftPoly_append, mul_comm, map_mul]
      simp [shiftPoly, Algebra.algebraMap_eq_smul_one]
    have hH1 : shiftedQRStep H s =
        (givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))ᴴ * H *
          givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := rfl
    generalize givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) = Q1
      at hQR hH1
    generalize givensHessenbergR (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) = R1
      at hQR
    have hQ1 : Q1ᴴ * Q1 = 1 := hQR.hasOrthonormalCols
    have hQ1' : Q1 * Q1ᴴ = 1 := hQR.hasOrthonormalCols.mul_conjTranspose_self
    -- `p(H) = Q₁ q(H₁) Q₁ᴴ` for `H₁ = Q₁ᴴ H Q₁`
    have hconj : ∀ p : Polynomial ℂ,
        Polynomial.aeval H p = Q1 * Polynomial.aeval (shiftedQRStep H s) p * Q1ᴴ := fun p => by
      rw [hH1, aeval_conjTranspose_mul_mul hQ1]
      simp only [← Matrix.mul_assoc, hQ1', Matrix.one_mul]
      rw [Matrix.mul_assoc, hQ1', Matrix.mul_one]
    refine ⟨Q1 * Q', R' * R1, ⟨?_, hQR.hasOrthonormalCols.mul hQ'.hasOrthonormalCols,
      hQ'.isUpperTriangular.mul hQR.isUpperTriangular⟩, ?_⟩
    · rw [hP, hconj (shiftPoly ss), hQ'.eq_mul, hQR.eq_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Q1ᴴ Q1 R1, hQ1, Matrix.one_mul]
    · rw [show multiShiftedQRStep H (s :: ss) = multiShiftedQRStep (shiftedQRStep H s) ss
        from rfl, hstep', hH1, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]

/-- The multi-shift QR step preserves the norm:
$\|\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})\|_2 = \|\mathbf{H}\|_2$. -/
theorem specNorm_multiShiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    specNorm (multiShiftedQRStep H ss) = specNorm H := by
  induction ss generalizing H with
  | nil => rfl
  | cons s ss ih =>
    exact (ih (shiftedQRStep H s)).trans
      ((hasOrthonormalCols_givensHessenbergQ _).specNorm_conjTranspose_mul_mul _)

/-- One shifted QR step carries an eigenvector matrix $\mathbf{V}$ to
$\mathbf{Q}^{\mathsf{H}}\mathbf{V}$, with the same pseudo-condition number. -/
private theorem exists_isUnit_mul_eq_mul_diagonal_shiftedQRStep
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (s : ℂ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      shiftedQRStep H s * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  set Q := givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
  have hQ : HasOrthonormalCols Q := hasOrthonormalCols_givensHessenbergQ _
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ.conjTranspose_mul_self
  have hU : IsUnit Qᴴ := ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQQ⟩, rfl⟩
  have hinv : (Qᴴ * V)⁻¹ = V⁻¹ * Q := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _
      ((Matrix.isUnit_iff_isUnit_det V).mp hV), hQ.conjTranspose_mul_self]
  refine ⟨Qᴴ * V, hU.mul hV, ?_, ?_⟩
  · change Qᴴ * H * Q * (Qᴴ * V) = _
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQ, Matrix.one_mul, hHV]
  · rw [pseudoConditionNumber_of_isUnit (hU.mul hV), pseudoConditionNumber_of_isUnit hV, hinv,
      hQ.specNorm_mul_right, ← specNorm_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hQ.specNorm_mul_right, specNorm_conjTranspose]

/-- **The multi-shift QR step carries the eigenvector matrix**: if
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
then $\widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has
$\widehat{\mathbf{H}}\mathbf{V}' = \mathbf{V}'\operatorname{diag}(\mathbf{d})$ for an invertible
$\mathbf{V}'$ with the same condition number, $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 =
\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$; so $\kappa_V$ is invariant along the iteration.
[BanksGarzaVargasSrivastava2021, §4]. -/
theorem exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (ss : List ℂ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      multiShiftedQRStep H ss * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  induction ss generalizing H V with
  | nil => exact ⟨V, hV, hHV, rfl⟩
  | cons s ss ih =>
    obtain ⟨V1, h1, e1, p1⟩ := exists_isUnit_mul_eq_mul_diagonal_shiftedQRStep hV hHV s
    obtain ⟨V2, h2, e2, p2⟩ := ih h1 e1
    exact ⟨V2, h2, e2, p2.trans p1⟩

/-- A row of a matrix with $\mathbf{M}\mathbf{M}^{\mathsf{H}} = \mathbf{I}$ has Euclidean norm
one. -/
private theorem norm_toLp_row_eq_one {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hM : M * Mᴴ = 1)
    (i : Fin (n + 1)) : ‖WithLp.toLp 2 (fun j => M i j)‖ = 1 := by
  have h := congrFun (congrFun hM i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_one] at h
  rw [EuclideanSpace.norm_eq, h, Real.sqrt_one]

/-- **The potential after a QR step is at most $\tau_p$**: for upper Hessenberg $\mathbf{H}$,
shifts $s_1, \dots, s_k$ with $1 \le k \le n$ and $p(\mathbf{H})$ invertible,
$p(z) = \prod_i (z - s_i)$,
$$\psi_k(\widehat{\mathbf{H}})^k\,\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1}\| \le 1\,,
\qquad \widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})\,,$$
that is $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H}) =
\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1}\|^{-1/k}$.
[BanksGarzaVargasSrivastava2021, Lemma 2.5], the invertible case. -/
theorem IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {ss : List ℂ}
    (hk : 0 < ss.length) (hkn : ss.length ≤ n) (hp : IsUnit (Polynomial.aeval H (shiftPoly ss))) :
    hessenbergPotential ss.length (multiShiftedQRStep H ss) ^ ss.length *
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖ ≤ 1 := by
  obtain ⟨Q, R, hQR, hHs⟩ := exists_isQR_aeval_shiftPoly hH ss
  have hmon := shiftPoly_monic ss
  have hdeg := natDegree_shiftPoly ss
  have hpot := hessenbergPotential_pow_le_norm_aeval
    (isUpperHessenberg_multiShiftedQRStep hH ss) hmon hk hkn hdeg
  have hQ : Qᴴ * Q = 1 := hQR.hasOrthonormalCols
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ
  have hRt : R.IsUpperTriangular := hQR.isUpperTriangular
  have hPQ := hQR.eq_mul
  set P := Polynomial.aeval H (shiftPoly ss) with hPdef
  have hdetP : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hp).ne_zero
  have hRnn : R (Fin.last n) (Fin.last n) ≠ 0 := by
    have hdetR : R.det ≠ 0 := by
      intro h0; apply hdetP; rw [hPQ, Matrix.det_mul, h0, mul_zero]
    rw [Matrix.det_of_isUpperTriangular hRt] at hdetR
    exact Finset.prod_ne_zero_iff.mp hdetR _ (Finset.mem_univ _)
  set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 with he
  have hrowe : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      M (Fin.last n) = e ᵥ* M := by
    intro M; ext j; simp [he, Matrix.vecMul, dotProduct, Pi.single_apply]
  have hRrow : e ᵥ* R = R (Fin.last n) (Fin.last n) • e := by
    ext j
    by_cases hj : j = Fin.last n
    · subst hj; simp [he, Matrix.vecMul, dotProduct, Pi.single_apply]
    · have hlt : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
      have h0 : R (Fin.last n) j = 0 := hRt hlt
      simp [he, Matrix.vecMul, dotProduct, Pi.single_apply, hj, h0]
  have hPR : Qᴴ * P * Q = R * Q := by
    rw [hPQ, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  -- the potential bound, rewritten along the step
  rw [hHs, aeval_conjTranspose_mul_mul hQ, hPR] at hpot
  rw [hHs]
  have hRQrow : (R * Q) (Fin.last n) = R (Fin.last n) (Fin.last n) • (e ᵥ* Q) := by
    rw [hrowe (R * Q), ← Matrix.vecMul_vecMul, hRrow, Matrix.smul_vecMul]
  have hxw : e ᵥ* P⁻¹ = (R (Fin.last n) (Fin.last n))⁻¹ • (e ᵥ* Qᴴ) := by
    have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hp)
    have key : ((R (Fin.last n) (Fin.last n))⁻¹ • (e ᵥ* Qᴴ)) ᵥ* P = e := by
      rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, hPQ, ← Matrix.mul_assoc, hQ, Matrix.one_mul,
        hRrow, smul_smul, inv_mul_cancel₀ hRnn, one_smul]
    calc e ᵥ* P⁻¹ = (((R (Fin.last n) (Fin.last n))⁻¹ • (e ᵥ* Qᴴ)) ᵥ* P) ᵥ* P⁻¹ := by rw [key]
      _ = ((R (Fin.last n) (Fin.last n))⁻¹ • (e ᵥ* Qᴴ)) ᵥ* (P * P⁻¹) := by
          rw [Matrix.vecMul_vecMul]
      _ = _ := by rw [hPinv, Matrix.vecMul_one]
  have hn1 : ‖WithLp.toLp 2 (e ᵥ* Q)‖ = 1 := by
    rw [← hrowe Q]; exact norm_toLp_row_eq_one hQQ (Fin.last n)
  have hn2 : ‖WithLp.toLp 2 (e ᵥ* Qᴴ)‖ = 1 := by
    rw [← hrowe Qᴴ]
    exact norm_toLp_row_eq_one (by rw [Matrix.conjTranspose_conjTranspose]; exact hQ) (Fin.last n)
  rw [hRQrow, WithLp.toLp_smul, norm_smul, hn1, mul_one] at hpot
  rw [hrowe P⁻¹, hxw, WithLp.toLp_smul, norm_smul, hn2, norm_inv, mul_one]
  have hinv : ‖R (Fin.last n) (Fin.last n)‖ * ‖R (Fin.last n) (Fin.last n)‖⁻¹ = 1 :=
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hRnn)
  have hψ := mul_le_mul_of_nonneg_right hpot
    (inv_nonneg.mpr (norm_nonneg (R (Fin.last n) (Fin.last n))))
  linarith [hψ, hinv]

/-- A zero subdiagonal entry persists under a shifted QR step: for upper Hessenberg
$\mathbf{H}$ with $\mathbf{H}_{i+1,i} = 0$ and any shift $s$, the step has
$(\mathsf{shiftedQRStep}(\mathbf{H}, s))_{i+1,i} = 0$. -/
theorem IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {i : Fin n}
    (hi : H i.succ i.castSucc = 0) (s : ℂ) : shiftedQRStep H s i.succ i.castSucc = 0 := by
  set A := H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA
  have hAi : A i.succ i.castSucc = 0 := by
    rw [hA, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne (fun h => by simpa using congrArg Fin.val h), smul_zero, sub_zero, hi]
  -- row `i + 1` is untouched before step `i`, so rotation `i` is diagonal and `Q (i+1) i = 0`
  have key : ((givensHessenbergState A (n + 1)).1ᴴ *ᵥ Pi.single i.succ 1) i.castSucc = 0 := by
    rw [(givensHessenbergState_apply_of_lt A _ (k := i + 1) (j := n + 1) (by omega)
      (a := i.castSucc) (by simp)).2, conjTranspose_givensHessenbergState_succ_fst_mulVec,
      givensHessenbergStep_of_lt _ (by omega) (by omega) (by omega),
      givensHessenbergState_snd_apply_of_eq_add_one A le_rfl (a := ⟨i + 1, by omega⟩) rfl,
      show (⟨i + 1, by omega⟩ : Fin (n + 1)) = i.succ from rfl,
      show (⟨i, by omega⟩ : Fin (n + 1)) = i.castSucc from rfl, hAi, givensCoeffs_snd_zero,
      givens_mulVec_apply_left (Fin.ne_of_val_ne (by simp)),
      givensHessenbergState_fst_mulVec_apply_eq_zero_of_le A (i := i)
        (fun a ha => Pi.single_eq_of_ne (Fin.ne_of_val_ne (by simp; omega)) _) le_rfl _ (by simp)]
    ring
  have hQ0 : givensHessenbergQ A i.succ i.castSucc = 0 := by
    rwa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply,
      star_eq_zero] at key
  rw [shiftedQRStep_eq_mul_add_smul_one, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (fun h => by simpa using congrArg Fin.val h), smul_zero, add_zero,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_trichotomy (l : ℕ) (i + 1) with h | h | h
  · rw [show givensHessenbergR A i.succ l = 0 from
      isUpperTrapezoidal_givensHessenbergR (hH.sub_smul_one s) i.succ l (by simp; omega), zero_mul]
  · rw [show l = i.succ from Fin.ext (by simp; omega), ← hA, hQ0, mul_zero]
  · rw [show givensHessenbergQ A l i.castSucc = 0 from
      isUpperHessenberg_givensHessenbergQ A l i.castSucc (by simp; omega), mul_zero]

/-- A reduced Hessenberg matrix stays reduced under multi-shift QR steps: for upper
Hessenberg $\mathbf{H}$ with a zero subdiagonal entry, every
$\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has one (at the same index). -/
theorem IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (h : IsDecoupled 0 H)
    (ss : List ℂ) : IsDecoupled 0 (multiShiftedQRStep H ss) := by
  induction ss generalizing H with
  | nil => exact h
  | cons s ss ih =>
    obtain ⟨i, hi⟩ := h
    have hs := hH.shiftedQRStep_apply_succ_castSucc_eq_zero (by simpa using hi) s
    exact ih (hH.isUpperHessenberg_shiftedQRStep s) ⟨i, by simp [hs]⟩

/-- **A singular shift decouples exactly**: for upper Hessenberg $\mathbf{H}$ of size at least
$2$ and a shift $s$ with $\det(\mathbf{H} - s\mathbf{I}) = 0$, the step
$\mathsf{shiftedQRStep}(\mathbf{H}, s)$ has a zero subdiagonal entry, at $(n, n - 1)$ when
$\mathbf{H}$ is unreduced. [BanksGarzaVargasSrivastava2021, proof of Lemma 2.5], where the claim
that $\mathbf{R}_{n,n} = 0$ for every QR factorization is used without the unreduced hypothesis
it needs. -/
theorem IsUpperHessenberg.isDecoupled_zero_shiftedQRStep_of_det_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (hn : 0 < n) {s : ℂ}
    (hs : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0) :
    IsDecoupled 0 (shiftedQRStep H s) := by
  by_cases hred : IsDecoupled 0 H
  · simpa [multiShiftedQRStep] using hH.isDecoupled_zero_multiShiftedQRStep hred [s]
  have hu := hH.isUnreducedHessenberg_iff_not_isDecoupled.mpr hred
  set A := H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA
  set Q := givensHessenbergQ A
  set R := givensHessenbergR A
  have hR := isUpperTrapezoidal_givensHessenbergR (hH.sub_smul_one s)
  -- the pivots before the last are nonzero, as the subdiagonal is
  have hpiv : ∀ j : Fin (n + 1), (j : ℕ) < n → R j j ≠ 0 := by
    intro j hj
    have hv : A ⟨j + 1, by omega⟩ j ≠ 0 := by
      rw [hA, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (fun h => by simpa using congrArg Fin.val h), smul_zero, sub_zero]
      exact hu.subdiagonal_ne_zero _ _ rfl
    rw [show R j j = (givensHessenbergState A (j + 1)).2 j j from
      (givensHessenbergState_apply_of_lt A 0 (k := j + 1) (j := n + 1) (by omega) (a := j)
        (by omega)).1 j, givensHessenbergState_succ_snd,
      givensHessenbergStep_of_lt _ (by omega) (by omega) (by omega)]
    simp only [Fin.eta]
    rw [givens_mul_apply_left (Fin.ne_of_val_ne (by simp)), givensCoeffs_fst_mul_add,
      givensHessenbergState_snd_apply_of_eq_add_one A le_rfl (a := ⟨j + 1, by omega⟩) rfl]
    have := norm_pos_iff.mpr hv
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  -- so the last pivot vanishes
  have hlast : R (Fin.last n) (Fin.last n) = 0 := by
    have hdet : Q.det * R.det = 0 := by
      rw [← Matrix.det_mul, show Q * R = A from givensHessenbergState_fst_mul_snd A (n + 1), hA, hs]
    rw [mul_eq_zero, or_iff_right (Matrix.det_ne_zero_of_left_inverse
      (hasOrthonormalCols_givensHessenbergQ A).conjTranspose_mul_self),
      Matrix.det_of_isUpperTriangular (fun i j h => hR i j h), Finset.prod_eq_zero_iff] at hdet
    obtain ⟨j, -, hj⟩ := hdet
    by_cases hjn : (j : ℕ) < n
    · exact absurd hj (hpiv j hjn)
    · rwa [show j = Fin.last n from Fin.ext (by simp; omega)] at hj
  refine ⟨⟨n - 1, by omega⟩, ?_⟩
  rw [show (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n from Fin.ext (by simp; omega),
    shiftedQRStep_eq_mul_add_smul_one, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (fun h => by have := congrArg Fin.val h; simp at this; omega), smul_zero,
    add_zero, Matrix.mul_apply, Finset.sum_eq_zero fun l _ => ?_]
  · simp
  rcases lt_or_ge (l : ℕ) n with h | h
  · exact mul_eq_zero_of_left (hR _ l (by simpa using h)) _
  · rw [show l = Fin.last n from Fin.ext (by simp; omega)]
    exact mul_eq_zero_of_left hlast _

/-- A unitary similarity keeps the determinant of a shifted matrix:
$\det(\mathsf{shiftedQRStep}(\mathbf{H}, s) - t\mathbf{I}) = \det(\mathbf{H} - t\mathbf{I})$. -/
private theorem det_shiftedQRStep_sub_smul (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s t : ℂ) :
    (shiftedQRStep H s - t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det =
      (H - t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det := by
  set Q := givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
  have hQ : Qᴴ * Q = 1 := (hasOrthonormalCols_givensHessenbergQ _).conjTranspose_mul_self
  change (Qᴴ * H * Q - t • 1).det = _
  rw [show Qᴴ * H * Q - t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Qᴴ * (H - t • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) * Q by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ],
    Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, hQ, Matrix.det_one, one_mul]

/-- If the shift polynomial of a list of shifts is singular, one of its shifts is an eigenvalue. -/
private theorem exists_mem_det_sub_smul_eq_zero_of_det_aeval
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (h : (Polynomial.aeval H (shiftPoly ss)).det = 0) :
    ∃ s ∈ ss, (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 := by
  induction ss with
  | nil => simp [shiftPoly] at h
  | cons s ss ih =>
    rw [show s :: ss = [s] ++ ss from rfl, shiftPoly_append, map_mul, Matrix.det_mul] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact ⟨s, List.mem_cons_self, by simpa [shiftPoly, Algebra.algebraMap_eq_smul_one] using h1⟩
    · obtain ⟨t, ht, h2⟩ := ih h1
      exact ⟨t, List.mem_cons_of_mem _ ht, h2⟩

/-- **A singular shift polynomial decouples exactly**: for upper Hessenberg $\mathbf{H}$ of size
at least $2$ and shifts with $\det p(\mathbf{H}) = 0$, $p(z) = \prod_i (z - s_i)$, the step
$\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has a zero subdiagonal entry. This is the
singular case of [BanksGarzaVargasSrivastava2021, Lemma 2.5], where it reads
$\psi_k(\widehat{\mathbf{H}}) = 0$. -/
theorem IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (hn : 0 < n)
    {ss : List ℂ} (h : (Polynomial.aeval H (shiftPoly ss)).det = 0) :
    IsDecoupled 0 (multiShiftedQRStep H ss) := by
  obtain ⟨t, ht, hdet⟩ := exists_mem_det_sub_smul_eq_zero_of_det_aeval H ss h
  clear h
  induction ss generalizing H with
  | nil => simp at ht
  | cons s ss ih =>
    have hH' := hH.isUpperHessenberg_shiftedQRStep s
    by_cases hs : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0
    · exact hH'.isDecoupled_zero_multiShiftedQRStep
        (hH.isDecoupled_zero_shiftedQRStep_of_det_eq_zero hn hs) ss
    · rcases List.mem_cons.mp ht with rfl | ht'
      · exact absurd hdet hs
      · exact ih hH' ht' (by rw [det_shiftedQRStep_sub_smul]; exact hdet)

/-- **The potential after a degree $k$ step with one repeated shift**: for upper Hessenberg
$\mathbf{H}$, $1 \le k \le n$ and a shift $r$ that is no eigenvalue,
$$\psi_k(\widehat{\mathbf{H}})^k\,\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|
\le 1\,,\qquad \widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, [r, \dots, r])\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 2.5], for $p(z) = (z - r)^k$. -/
theorem IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) {r : ℂ} (hr : (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0) :
    hessenbergPotential k (multiShiftedQRStep H (List.replicate k r)) ^ k *
      ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
        (Fin.last n))‖ ≤ 1 := by
  have h := hH.hessenbergPotential_multiShiftedQRStep_pow_mul_le (ss := List.replicate k r)
    (by simpa using hk) (by simpa using hkn) (by
      rw [aeval_shiftPoly_replicate]
      exact ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hr)).pow _)
  rwa [List.length_replicate, aeval_shiftPoly_replicate, ← Matrix.inv_pow'] at h

end NLAlib
