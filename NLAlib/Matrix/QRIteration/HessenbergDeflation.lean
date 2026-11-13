/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Spectral.EigenvectorPairing

/-!
# Deflation of a Hessenberg matrix into diagonal blocks

The shifted QR algorithm deflates: when a subdiagonal entry of an active diagonal block is at
most a threshold $\tau$, it sets the entry to zero and continues on the two diagonal blocks
separately; a block small enough is handed to an eigenvalue routine. The diagonal blocks are
contiguous ranges $[lo, lo + d)$ of the indices, and the matrix they come from is block upper
triangular for the partition into ranges. This file states the invariant of that process in
exact arithmetic, `NLAlib.DeflationInv`: the current blocks are the diagonal blocks of a matrix
$\mathbf{M} = \mathbf{U}^{\mathsf{H}}(\mathbf{H} + \mathbf{E})\mathbf{U}$, $\mathbf{U}$ unitary
and $\|\mathbf{E}\|_2 \le \varepsilon$, block upper triangular for the ranges, and the
eigenvalues written for the finished ranges are those of their blocks. Each zeroed entry adds
its modulus to $\varepsilon$; at the end the output is exactly the spectrum of
$\mathbf{H} + \mathbf{E}$ (a backward error), and by Bauer–Fike each output is within
$\kappa_V\varepsilon$ of an eigenvalue of $\mathbf{H}$. [BanksGarzaVargasSrivastava2022, §6]
(Deflate and the while loop of ShiftedQR), here in exact arithmetic and for eigenvalues only.

Matrices have order $n + 1$, so that a block with a range past the end is read with clamped
indices (a junk value no statement uses), as `NLAlib.trailingBlock`.

## Main definitions

* `NLAlib.blockIndex`, `NLAlib.subBlock`, `NLAlib.subVec`, `NLAlib.setSubBlock`: the block of a
  range, read and written.
* `NLAlib.IsRangePartition`, `NLAlib.rangeLabel`: a partition of the indices into ranges, and
  the start of the range of an index (the block label).
* `NLAlib.DeflationInv`: the invariant of deflation.

## Main results

* `NLAlib.IsUpperHessenberg.subBlock`: a diagonal block of a Hessenberg matrix is Hessenberg.
* `NLAlib.IsUpperHessenberg.deflationInv_init`: the start, one active block.
* `NLAlib.DeflationInv.conj`: a unitary similarity of an active block.
* `NLAlib.DeflationInv.split`: a split at a small subdiagonal entry.
* `NLAlib.DeflationInv.finish`: a block's eigenvalues written.
* `NLAlib.DeflationInv.perm`, `NLAlib.DeflationInv.length_le`: the order and the number of
  ranges.
* `NLAlib.DeflationInv.exists_roots_eq`: the backward error at the end.
* `NLAlib.DeflationInv.exists_norm_sub_le`: the forward error at the end (Bauer–Fike).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The **index of position $i$ of the range** $r = (lo, d)$ in $\{0, \dots, n\}$:
$\min(lo + i, n)$ (clamped past the end). -/
def blockIndex (n : ℕ) (r : ℕ × ℕ) (i : Fin r.2) : Fin (n + 1) :=
  ⟨min (r.1 + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The **diagonal block of the range** $r = (lo, d)$: the $d \times d$ principal submatrix on
the indices $lo, \dots, lo + d - 1$ (clamped at $n$). -/
def subBlock (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℕ × ℕ) :
    Matrix (Fin r.2) (Fin r.2) ℂ :=
  M.submatrix (blockIndex n r) (blockIndex n r)

/-- The **part of a vector on the range** $r = (lo, d)$: its coordinates $lo, \dots,
lo + d - 1$ (clamped at $n$). -/
def subVec (v : Fin (n + 1) → ℂ) (r : ℕ × ℕ) : Fin r.2 → ℂ :=
  v ∘ blockIndex n r

/-- The matrix $\mathbf{A}$ with the **diagonal block of the range** $r = (lo, d)$ replaced by
$\mathbf{B}$: entries with both indices in $[lo, lo + d)$ from $\mathbf{B}$, the others from
$\mathbf{A}$. -/
def setSubBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℕ × ℕ)
    (B : Matrix (Fin r.2) (Fin r.2) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j =>
    if h : r.1 ≤ (i : ℕ) ∧ (i : ℕ) < r.1 + r.2 ∧ r.1 ≤ (j : ℕ) ∧ (j : ℕ) < r.1 + r.2 then
      B ⟨i - r.1, by omega⟩ ⟨j - r.1, by omega⟩
    else A i j

/-- A list of ranges $(lo, d)$ is a **partition of $\{0, \dots, N - 1\}$ into ranges**: no
range is listed twice, every range is nonempty and inside, and every index lies in exactly one
range. -/
def IsRangePartition (N : ℕ) (rs : List (ℕ × ℕ)) : Prop :=
  rs.Nodup ∧ (∀ r ∈ rs, 1 ≤ r.2 ∧ r.1 + r.2 ≤ N) ∧
    ∀ i < N, ∃! r, r ∈ rs ∧ r.1 ≤ i ∧ i < r.1 + r.2

/-- The **label of an index** for a list of ranges: the start $lo$ of the first range
$(lo, d)$ containing it ($0$ if none does). For a partition into ranges a matrix is block upper
triangular for these labels (`Matrix.BlockTriangular`) when its entries below the diagonal
blocks vanish. -/
def rangeLabel {N : ℕ} (rs : List (ℕ × ℕ)) (i : Fin N) : ℕ :=
  ((rs.find? fun r => decide (r.1 ≤ (i : ℕ) ∧ (i : ℕ) < r.1 + r.2)).map Prod.fst).getD 0

/-- **The invariant of deflation** in exact arithmetic, for the input $\mathbf{H}$, the
accumulated perturbation bound $\varepsilon$, the active ranges, the finished ranges, the
current matrix $\mathbf{A}$ (whose active diagonal blocks are being iterated) and the output
vector of eigenvalues: there are $\mathbf{M}$, a unitary $\mathbf{U}$ and $\mathbf{E}$ with
$\|\mathbf{E}\|_2 \le \varepsilon$ and $\mathbf{M} = \mathbf{U}^{\mathsf{H}}(\mathbf{H} +
\mathbf{E})\mathbf{U}$, such that the active and finished ranges partition the indices,
$\mathbf{M}$ is block upper triangular for them, every active block of $\mathbf{M}$ is the block
of $\mathbf{A}$ and upper Hessenberg, and every finished block of $\mathbf{M}$ has as
eigenvalues (the roots of its characteristic polynomial, with multiplicity) the output on its
range. [BanksGarzaVargasSrivastava2022, §6]. -/
def DeflationInv (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ε : ℝ)
    (active done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (out : Fin (n + 1) → ℂ) : Prop :=
  ∃ M U E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols U ∧ specNorm E ≤ ε ∧
    M = Uᴴ * (H + E) * U ∧ IsRangePartition (n + 1) (active ++ done) ∧
    M.BlockTriangular (rangeLabel (active ++ done)) ∧
    (∀ r ∈ active, subBlock M r = subBlock A r ∧ IsUpperHessenberg (subBlock A r)) ∧
    ∀ r ∈ done, (subBlock M r).charpoly.roots = (List.ofFn (subVec out r) : Multiset ℂ)

/-- A diagonal block of an upper Hessenberg matrix on a range inside the indices is upper
Hessenberg. -/
theorem IsUpperHessenberg.subBlock {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {r : ℕ × ℕ} (hr : r.1 + r.2 ≤ n + 1) :
    IsUpperHessenberg (NLAlib.subBlock H r) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  simp only [NLAlib.subBlock, Matrix.submatrix_apply]
  apply hH
  simp only [blockIndex]
  rw [min_eq_left (show r.1 + (j : ℕ) ≤ n by omega), min_eq_left (show r.1 + (i : ℕ) ≤ n by omega)]
  omega

/-- The start of deflation: an upper Hessenberg $\mathbf{H}$ is one active block, with no
perturbation, no finished block and any output vector. -/
theorem IsUpperHessenberg.deflationInv_init {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (out : Fin (n + 1) → ℂ) :
    DeflationInv H 0 [(0, n + 1)] [] H out := by
  unfold DeflationInv
  refine ⟨H, 1, 0, hasOrthonormalCols_one, by simp [specNorm_zero], by simp, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp, fun r hr => ?_, fun i hi => ⟨(0, n + 1), ⟨by simp, by simp, by omega⟩, ?_⟩⟩
    · simp only [List.append_nil, List.mem_singleton] at hr
      subst hr
      simp
    · rintro q ⟨hq, hq1, hq2⟩
      simp only [List.append_nil, List.mem_singleton] at hq
      subst hq
      rfl
  · have hz : ∀ k : Fin (n + 1), rangeLabel ([(0, n + 1)] ++ []) k = 0 := by
      intro k
      simp only [rangeLabel, List.append_nil, List.find?_cons, List.find?_nil]
      split <;> simp
    intro i j hij
    rw [hz, hz] at hij
    exact absurd hij (lt_irrefl 0)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨rfl, IsUpperHessenberg.subBlock hH (by simp)⟩
  · intro r hr
    simp at hr

/-- The label of an index in a range of a partition is the start of that range. -/
private theorem rangeLabel_eq_of_mem_conj {N : ℕ} {rs : List (ℕ × ℕ)}
    (hrs : IsRangePartition N rs) {r : ℕ × ℕ} (hr : r ∈ rs) {k : Fin N} (hk₁ : r.1 ≤ (k : ℕ))
    (hk₂ : (k : ℕ) < r.1 + r.2) : rangeLabel rs k = r.1 := by
  unfold rangeLabel
  cases hf : rs.find? (fun r => (r.1 ≤ (k : ℕ) ∧ (k : ℕ) < r.1 + r.2 : Bool)) with
  | none =>
    exact absurd (List.find?_eq_none.mp hf r hr) (by simp [hk₁, hk₂])
  | some r₀ =>
    have h₀ := List.find?_some hf
    simp only [decide_eq_true_eq] at h₀
    have := (hrs.2.2 k k.2).unique ⟨List.mem_of_find?_eq_some hf, h₀⟩ ⟨hr, hk₁, hk₂⟩
    simp [this]

/-- The block of a range is read by the coordinate embedding of the range. -/
private theorem subBlock_eq_embed_conj (r : ℕ × ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    subBlock X r = ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id (blockIndex n r))ᴴ *
      X * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id (blockIndex n r) := by
  ext a b
  simp [subBlock, Matrix.mul_apply, Matrix.one_apply]

/-- Writing the block of a range of a partition and reading it back, on the same range or on
another range of the partition. -/
private theorem subBlock_setSubBlock_conj {rs : List (ℕ × ℕ)} (hrs : IsRangePartition (n + 1) rs)
    {r : ℕ × ℕ} (hr : r ∈ rs) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Matrix (Fin r.2) (Fin r.2) ℂ) :
    subBlock (setSubBlock A r B) r = B ∧
      ∀ r' ∈ rs, r' ≠ r → subBlock (setSubBlock A r B) r' = subBlock A r' := by
  have hidx : ∀ r' ∈ rs, ∀ a : Fin r'.2, (blockIndex n r' a : ℕ) = r'.1 + a :=
    fun r' hr' a => by
      have := (hrs.2.1 r' hr').2
      simp only [blockIndex]; omega
  refine ⟨?_, fun r' hr' hne => ?_⟩
  · ext a b
    simp only [subBlock, setSubBlock, Matrix.submatrix_apply, Matrix.of_apply, hidx r hr]
    rw [dif_pos (by omega)]; congr 1 <;> ext <;> simp
  · ext a b
    simp only [subBlock, setSubBlock, Matrix.submatrix_apply, Matrix.of_apply]
    rw [dif_neg]
    rintro ⟨h₁, h₂, -, -⟩
    have := hidx r' hr' a
    exact hne ((hrs.2.2 _ (blockIndex n r' a).2).unique ⟨hr', by omega, by omega⟩ ⟨hr, h₁, h₂⟩)

/-- **The embedding of a unitary block**: for a range $r$ of a partition and $\mathbf{U}_r$
unitary, the identity with block $r$ replaced by $\mathbf{U}_r$ is unitary, block triangular
with its adjoint, and conjugating by it conjugates block $r$ by $\mathbf{U}_r$ and leaves the
other blocks unchanged. -/
private theorem exists_embed_conj {rs : List (ℕ × ℕ)} (hrs : IsRangePartition (n + 1) rs)
    {r : ℕ × ℕ} (hrm : r ∈ rs) {Ub : Matrix (Fin r.2) (Fin r.2) ℂ} (hU : HasOrthonormalCols Ub) :
    ∃ W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols W ∧
      W.BlockTriangular (rangeLabel rs) ∧ Wᴴ.BlockTriangular (rangeLabel rs) ∧
      (∀ X, subBlock (Wᴴ * X * W) r = Ubᴴ * subBlock X r * Ub) ∧
      ∀ r' ∈ rs, r' ≠ r → ∀ X, subBlock (Wᴴ * X * W) r' = subBlock X r' := by
  set L := rangeLabel rs
  have hrr := hrs.2.1 r hrm
  -- the embedding of the coordinates of a range
  let Q : ∀ r' : ℕ × ℕ, Matrix (Fin (n + 1)) (Fin r'.2) ℂ := fun r' =>
    (1 : Matrix _ _ ℂ).submatrix id (blockIndex n r')
  have hQ : ∀ r' i a, Q r' i a = if i = blockIndex n r' a then 1 else 0 := fun r' i a => by
    simp [Q, Matrix.one_apply]
  have hidx : ∀ r' ∈ rs, ∀ a : Fin r'.2, (blockIndex n r' a : ℕ) = r'.1 + a :=
    fun r' hr' a => by
      have := (hrs.2.1 r' hr').2
      simp only [blockIndex]; omega
  have hQQ : (Q r)ᴴ * Q r = 1 := by
    ext a b
    have hinj : blockIndex n r a = blockIndex n r b ↔ a = b := by
      rw [Fin.ext_iff, Fin.ext_iff, hidx r hrm, hidx r hrm]; omega
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hQ, Matrix.one_apply,
      apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hinj]
  have hQQ' : ∀ r' ∈ rs, r' ≠ r → (Q r)ᴴ * Q r' = 0 := by
    intro r' hr' hne; ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hQ, Matrix.zero_apply,
      apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [if_neg]
    intro hab
    have h₁ := hidx r' hr' b
    have h₂ := hidx r hrm a
    rw [← hab] at h₁
    exact hne ((hrs.2.2 _ (blockIndex n r a).2).unique ⟨hr', by omega, by omega⟩
      ⟨hrm, by omega, by omega⟩)
  have hblk : ∀ Y : Matrix (Fin r.2) (Fin r.2) ℂ,
      (1 + Q r * Y * (Q r)ᴴ).BlockTriangular L := by
    have hrow : ∀ i : Fin (n + 1), (∃ a, i = blockIndex n r a) → L i = r.1 := by
      rintro i ⟨a, rfl⟩
      exact rangeLabel_eq_of_mem_conj hrs hrm (by rw [hidx r hrm]; omega)
        (by rw [hidx r hrm]; omega)
    intro Y i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (fun h => (h ▸ hij).false), zero_add]
    by_cases hi : ∃ a, i = blockIndex n r a
    · by_cases hj : ∃ b, j = blockIndex n r b
      · exact absurd hij (by rw [hrow i hi, hrow j hj]; exact lt_irrefl _)
      · push Not at hj
        simp [Matrix.mul_apply, hQ, hj]
    · push Not at hi
      simp [Matrix.mul_apply, hQ, hi]
  set W := 1 + Q r * (Ub - 1) * (Q r)ᴴ with hW
  have hWH : Wᴴ = 1 + Q r * (Ubᴴ - 1) * (Q r)ᴴ := by
    simp [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.mul_assoc]
  have hQQY : ∀ {m : Type} (Y : Matrix (Fin r.2) m ℂ), (Q r)ᴴ * (Q r * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
  have key : (Ubᴴ - 1) + (Ub - 1) + (Ubᴴ - 1) * (Ub - 1) = 0 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, hU.conjTranspose_mul_self, Matrix.mul_one,
      Matrix.one_mul]
    abel
  refine ⟨W, ?_, hblk _, hWH ▸ hblk _, fun X => ?_, fun r' hr' hne X => ?_⟩
  · rw [hasOrthonormalCols_iff, hWH]
    calc _ = 1 + Q r * ((Ubᴴ - 1) + (Ub - 1) + (Ubᴴ - 1) * (Ub - 1)) * (Q r)ᴴ := by
          simp only [W, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
            Matrix.mul_assoc, hQQY]
          abel
      _ = 1 := by rw [key]; simp
  · have hWQ : W * Q r = Q r * Ub := by
      simp only [W, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQQ, Matrix.mul_one,
        Matrix.mul_sub]
      abel
    calc _ = (W * Q r)ᴴ * X * (W * Q r) := by
          rw [subBlock_eq_embed_conj]; simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [hWQ, subBlock_eq_embed_conj]
          simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · have hWQ' : W * Q r' = Q r' := by
      simp only [W, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQQ' r' hr' hne,
        Matrix.mul_zero, add_zero]
    calc _ = (W * Q r')ᴴ * X * (W * Q r') := by
          rw [subBlock_eq_embed_conj]; simp only [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hWQ', subBlock_eq_embed_conj]

/-- A unitary similarity of an active block keeps the invariant: replacing the active block
$\mathbf{A}_r$ of the range $r$ by $\mathbf{U}_r^{\mathsf{H}}\mathbf{A}_r\mathbf{U}_r$, with
$\mathbf{U}_r$ unitary and the result upper Hessenberg (a shifted QR step of the block). -/
theorem DeflationInv.conj {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ}
    {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out)
    {r : ℕ × ℕ} (hr : r ∈ active) {Ub : Matrix (Fin r.2) (Fin r.2) ℂ} (hU : HasOrthonormalCols Ub)
    (hHess : IsUpperHessenberg (Ubᴴ * subBlock A r * Ub)) :
    DeflationInv H ε active done (setSubBlock A r (Ubᴴ * subBlock A r * Ub)) out := by
  obtain ⟨M, U, E, hUU, hE, rfl, hpart, hbt, hact, hdone⟩ := h
  have hrm : r ∈ active ++ done := List.mem_append_left _ hr
  obtain ⟨W, hWW, hW, hWH, hself, hother⟩ := exists_embed_conj hpart hrm hU
  have hset := subBlock_setSubBlock_conj hpart hrm A (Ubᴴ * subBlock A r * Ub)
  refine ⟨Wᴴ * (Uᴴ * (H + E) * U) * W, U * W, E, ?_, hE, ?_, hpart, (hWH.mul hbt).mul hW,
    fun r' hr' => ?_, fun r' hr' => ?_⟩
  · exact hUU.mul hWW
  · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · by_cases hne : r' = r
    · rw [hne, hset.1, hself, (hact r hr).1]
      exact ⟨rfl, hHess⟩
    · have hr'm := List.mem_append_left done hr'
      rw [hset.2 r' hr'm hne, hother r' hr'm hne]
      exact hact r' hr'
  · have hne : r' ≠ r := fun h => (List.nodup_append.mp hpart.1).2.2 r hr r' hr' h.symm
    rw [hother r' (List.mem_append_right _ hr') hne]
    exact hdone r' hr'

/-- The label of an index in a range of a partition is the start of that range. -/
private theorem rangeLabel_eq_of_mem_split {N : ℕ} {rs : List (ℕ × ℕ)}
    (hrs : IsRangePartition N rs) {r : ℕ × ℕ} (hr : r ∈ rs) {k : Fin N} (hk₁ : r.1 ≤ (k : ℕ))
    (hk₂ : (k : ℕ) < r.1 + r.2) : rangeLabel rs k = r.1 := by
  unfold rangeLabel
  cases hf : rs.find? (fun r => (r.1 ≤ (k : ℕ) ∧ (k : ℕ) < r.1 + r.2 : Bool)) with
  | none => exact absurd (List.find?_eq_none.mp hf r hr) (by simp [hk₁, hk₂])
  | some r₀ =>
    have h₀ := List.find?_some hf
    simp only [decide_eq_true_eq] at h₀
    have := (hrs.2.2 k k.2).unique ⟨List.mem_of_find?_eq_some hf, h₀⟩ ⟨hr, hk₁, hk₂⟩
    simp [this]

/-- Splitting a range of a partition into two consecutive ranges gives a partition. -/
private theorem isRangePartition_split {N lo d i : ℕ} {rest : List (ℕ × ℕ)}
    (h : IsRangePartition N ((lo, d) :: rest)) (hi : i + 1 < d) :
    IsRangePartition N ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest) := by
  obtain ⟨hnd, hval, huniq⟩ := h
  have hlo := hval (lo, d) List.mem_cons_self
  -- a range of `rest` meets no index of `(lo, d)`
  have hpar : ∀ r ∈ rest, ∀ k < N, r.1 ≤ k → k < r.1 + r.2 → ¬(lo ≤ k ∧ k < lo + d) := by
    intro r hr k hk h₁ h₂ h₃
    have := (huniq k hk).unique ⟨List.mem_cons_of_mem _ hr, h₁, h₂⟩ ⟨List.mem_cons_self, h₃⟩
    exact (List.nodup_cons.mp hnd).1 (this ▸ hr)
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, (List.nodup_cons.mp hnd).2⟩⟩
    · simp only [List.mem_cons, Prod.mk.injEq, not_or]
      refine ⟨by omega, fun hr => hpar _ hr lo (by simp at hlo; omega) le_rfl
        (by simp) ⟨le_rfl, by simp at hlo; omega⟩⟩
    · exact fun hr => hpar _ hr (lo + i + 1) (by simp at hlo; omega) le_rfl (by simp; omega)
        ⟨by omega, by omega⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    simp at hlo
    rcases hr with rfl | rfl | hr
    · simp; omega
    · simp; omega
    · exact hval r (List.mem_cons_of_mem _ hr)
  · intro k hk
    by_cases hkb : lo ≤ k ∧ k < lo + d
    · by_cases hk' : k < lo + i + 1
      · refine ⟨(lo, i + 1), ⟨List.mem_cons_self, by simp; omega⟩, ?_⟩
        rintro r' ⟨hr', h₁, h₂⟩
        simp only [List.mem_cons] at hr'
        rcases hr' with rfl | rfl | hr'
        · rfl
        · simp at h₁; omega
        · exact absurd hkb (hpar r' hr' k hk h₁ h₂)
      · refine ⟨(lo + i + 1, d - i - 1), ⟨by simp, by simp; omega⟩, ?_⟩
        rintro r' ⟨hr', h₁, h₂⟩
        simp only [List.mem_cons] at hr'
        rcases hr' with rfl | rfl | hr'
        · simp at h₂; omega
        · rfl
        · exact absurd hkb (hpar r' hr' k hk h₁ h₂)
    · obtain ⟨r₀, ⟨hr₀, h₁, h₂⟩, hu⟩ := huniq k hk
      have hr₀' : r₀ ∈ rest := by
        rcases List.mem_cons.mp hr₀ with rfl | h
        · exact absurd ⟨h₁, h₂⟩ hkb
        · exact h
      refine ⟨r₀, ⟨by simp [hr₀'], h₁, h₂⟩, ?_⟩
      rintro r' ⟨hr', h₁', h₂'⟩
      simp only [List.mem_cons] at hr'
      rcases hr' with rfl | rfl | hr'
      · simp at h₁' h₂'; omega
      · simp at h₁' h₂'; omega
      · exact hu r' ⟨List.mem_cons_of_mem _ hr', h₁', h₂'⟩

/-- Conjugating a one-entry matrix by a unitary matrix does not increase its norm beyond the
modulus of the entry. -/
private theorem specNorm_mul_single_mul_le_split {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hUU : HasOrthonormalCols U) (p q : Fin (n + 1)) (c : ℂ) :
    specNorm (U * Matrix.single p q c * Uᴴ) ≤ ‖c‖ := by
  have hUc : HasOrthonormalCols U := hUU
  rw [Matrix.mul_assoc, hUc.specNorm_mul_left, ← specNorm_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hUc.specNorm_mul_left,
    specNorm_conjTranspose]
  refine (specNorm_le_frobNorm _).trans ?_
  rw [← sq_le_sq₀ (frobNorm_nonneg _) (norm_nonneg _), frobNorm_sq_eq_sum,
    Finset.sum_eq_single p (fun b _ hb => by simp [Ne.symm hb]) (by simp),
    Finset.sum_eq_single q (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- Zeroing the entry $(lo + i + 1, lo + i)$ of a matrix block triangular for a partition, whose
block $(lo, d)$ is upper Hessenberg, gives a matrix block triangular for the partition with
$(lo, d)$ split into $(lo, i + 1)$ and $(lo + i + 1, d - i - 1)$. -/
private theorem blockTriangular_sub_single_split {lo d i : ℕ} {rest : List (ℕ × ℕ)}
    (hpart : IsRangePartition (n + 1) ((lo, d) :: rest)) (hi : i + 1 < d)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hbt : M.BlockTriangular (rangeLabel ((lo, d) :: rest)))
    (hH : IsUpperHessenberg (subBlock M (lo, d))) {p q : Fin (n + 1)}
    (hp : (p : ℕ) = lo + i + 1) (hq : (q : ℕ) = lo + i) :
    (M - Matrix.single p q (M p q)).BlockTriangular
      (rangeLabel ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest)) := by
  have hpart' := isRangePartition_split hpart hi
  have hlo := (hpart.2.1 (lo, d) List.mem_cons_self).2
  simp only at hlo
  have hpar : ∀ r ∈ rest, ∀ k : Fin (n + 1), r.1 ≤ k → (k : ℕ) < r.1 + r.2 →
      ¬(lo ≤ k ∧ (k : ℕ) < lo + d) := by
    intro r hr k h₁ h₂ h₃
    have := (hpart.2.2 k k.2).unique ⟨List.mem_cons_of_mem _ hr, h₁, h₂⟩
      ⟨List.mem_cons_self, h₃⟩
    exact (List.nodup_cons.mp hpart.1).1 (this ▸ hr)
  set L := rangeLabel ((lo, d) :: rest)
  set L' := rangeLabel ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest)
  have hlab : ∀ k : Fin (n + 1), (lo ≤ k ∧ (k : ℕ) < lo + i + 1 ∧ L k = lo ∧ L' k = lo) ∨
      (lo + i + 1 ≤ k ∧ (k : ℕ) < lo + d ∧ L k = lo ∧ L' k = lo + i + 1) ∨
      (¬(lo ≤ k ∧ (k : ℕ) < lo + d) ∧ L k = L' k ∧ (L k < lo ∨ lo + d ≤ L k)) := by
    intro k
    by_cases hk : lo ≤ k ∧ (k : ℕ) < lo + d
    · have hL : L k = lo :=
        rangeLabel_eq_of_mem_split hpart List.mem_cons_self hk.1 hk.2
      by_cases hk' : (k : ℕ) < lo + i + 1
      · exact Or.inl ⟨hk.1, hk', hL,
          rangeLabel_eq_of_mem_split hpart' List.mem_cons_self hk.1 (by simp; omega)⟩
      · exact Or.inr (Or.inl ⟨by omega, hk.2, hL, rangeLabel_eq_of_mem_split hpart'
          (r := (lo + i + 1, d - i - 1)) (by simp) (by simp; omega) (by simp; omega)⟩)
    · obtain ⟨r, ⟨hr, h₁, h₂⟩, -⟩ := hpart.2.2 k k.2
      have hr' : r ∈ rest := by
        rcases List.mem_cons.mp hr with rfl | h
        · exact absurd ⟨h₁, h₂⟩ hk
        · exact h
      have hrv := hpart.2.1 r hr
      have e₁ : L k = r.1 := rangeLabel_eq_of_mem_split hpart hr h₁ h₂
      have e₂ : L' k = r.1 := rangeLabel_eq_of_mem_split hpart' (by simp [hr']) h₁ h₂
      have := hpar r hr' ⟨r.1, by omega⟩ le_rfl (by simp; omega)
      exact Or.inr (Or.inr ⟨hk, e₁.trans e₂.symm, by rw [e₁]; simp at this; omega⟩)
  intro a b hab
  rw [Matrix.sub_apply]
  by_cases hpq : a = p ∧ b = q
  · obtain ⟨rfl, rfl⟩ := hpq
    rw [Matrix.single_apply_same, sub_self]
  have hS0 : Matrix.single p q (M p q) a b = 0 :=
    Matrix.single_apply_of_ne p q _ a b (by rintro ⟨rfl, rfl⟩; exact hpq ⟨rfl, rfl⟩)
  rw [hS0, sub_zero]
  have hpq' : ¬((a : ℕ) = lo + i + 1 ∧ (b : ℕ) = lo + i) :=
    fun h => hpq ⟨Fin.ext (h.1.trans hp.symm), Fin.ext (h.2.trans hq.symm)⟩
  have hcase : L b < L a ∨ (lo ≤ (b : ℕ) ∧ (b : ℕ) + 1 < a ∧ (a : ℕ) < lo + d) := by
    rcases hlab a with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;>
      rcases hlab b with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _⟩ <;> omega
  rcases hcase with h | h
  · exact hbt h
  · have := hH ⟨a - lo, by omega⟩ ⟨b - lo, by omega⟩ (by simp; omega)
    simp only [subBlock, Matrix.submatrix_apply, blockIndex] at this
    convert this using 2 <;> ext <;> simp <;> omega

/-- **A split at a small subdiagonal entry**: if entry $(i + 1, i)$ of the first active block
$(lo, d)$ has modulus at most $\tau$, the invariant holds with the two ranges $(lo, i + 1)$ and
$(lo + i + 1, d - i - 1)$ in its place and $\varepsilon + \tau$ in place of $\varepsilon$ (the
entry is set to zero in $\mathbf{M}$, a perturbation of norm at most $\tau$).
[BanksGarzaVargasSrivastava2022, §6], Deflate. -/
theorem DeflationInv.split {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε τ : ℝ} {lo d : ℕ}
    {rest done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε ((lo, d) :: rest) done A out) {i : ℕ} (hi : i + 1 < d)
    (hτ : ‖subBlock A (lo, d) ⟨i + 1, hi⟩ ⟨i, Nat.lt_of_succ_lt hi⟩‖ ≤ τ) :
    DeflationInv H (ε + τ) ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest) done A out := by
  obtain ⟨M, U, E, hUU, hE, rfl, hpart, hbt, hact, hdone⟩ := h
  set M := Uᴴ * (H + E) * U with hMdef
  have hlo := (hpart.2.1 (lo, d) List.mem_cons_self).2
  simp only at hlo
  have hpart' : IsRangePartition (n + 1)
      ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest ++ done) :=
    isRangePartition_split (rest := rest ++ done) hpart hi
  set p : Fin (n + 1) := ⟨lo + i + 1, by omega⟩
  set q : Fin (n + 1) := ⟨lo + i, by omega⟩
  set S := Matrix.single p q (M p q) with hS
  have hblk := hact (lo, d) List.mem_cons_self
  have hMA : M p q = subBlock A (lo, d) ⟨i + 1, hi⟩ ⟨i, Nat.lt_of_succ_lt hi⟩ := by
    rw [← hblk.1]; simp only [subBlock, Matrix.submatrix_apply, blockIndex]
    congr 1 <;> ext <;> simp only [p, q] <;> omega
  -- a range of `rest ++ done` meets no index of `(lo, d)`
  have hpar : ∀ r ∈ rest ++ done, ∀ k : Fin (n + 1), r.1 ≤ k → (k : ℕ) < r.1 + r.2 →
      ¬(lo ≤ k ∧ (k : ℕ) < lo + d) := by
    intro r hr k h₁ h₂ h₃
    have := (hpart.2.2 k k.2).unique ⟨List.mem_cons_of_mem _ hr, h₁, h₂⟩
      ⟨List.mem_cons_self, h₃⟩
    exact (List.nodup_cons.mp hpart.1).1 (this ▸ hr)
  -- blocks avoiding the zeroed entry are unchanged
  have hSsub : ∀ r' : ℕ × ℕ, (∀ x y : Fin r'.2,
      ¬(blockIndex n r' x = p ∧ blockIndex n r' y = q)) → subBlock (M - S) r' = subBlock M r' := by
    intro r' h; ext x y
    simp only [subBlock, Matrix.submatrix_apply, Matrix.sub_apply, hS]
    rw [Matrix.single_apply_of_ne p q _ _ _ (fun h' => h x y ⟨h'.1.symm, h'.2.symm⟩), sub_zero]
  have hnot : ∀ r ∈ rest ++ done, ∀ x y : Fin r.2,
      ¬(blockIndex n r x = p ∧ blockIndex n r y = q) := by
    rintro r hr x y ⟨hx, -⟩
    have hrv := (hpart.2.1 r (List.mem_cons_of_mem _ hr)).2
    have hx' := congrArg Fin.val hx
    simp only [blockIndex, p] at hx'
    exact hpar r hr p (by simp only [p]; omega) (by simp only [p]; omega)
      ⟨by simp only [p]; omega, by simp only [p]; omega⟩
  have hsubr : ∀ (s m : ℕ) (hsm : s + m ≤ d) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      subBlock X (lo + s, m) = (subBlock X (lo, d)).submatrix
        (fun x : Fin m => ⟨s + x, by omega⟩) (fun x : Fin m => ⟨s + x, by omega⟩) := by
    intro s m hsm X; ext x y
    simp only [subBlock, Matrix.submatrix_apply, blockIndex]
    congr 1 <;> ext <;> simp <;> omega
  have hhalf : ∀ (s m : ℕ) (hsm : s + m ≤ d), (∀ x y : Fin m,
      ¬(blockIndex n (lo + s, m) x = p ∧ blockIndex n (lo + s, m) y = q)) →
      subBlock (M - S) (lo + s, m) = subBlock A (lo + s, m) ∧
        IsUpperHessenberg (subBlock A (lo + s, m)) := by
    intro s m hsm h
    refine ⟨by rw [hSsub _ h, hsubr s m hsm, hblk.1, ← hsubr s m hsm], ?_⟩
    rw [hsubr s m hsm]
    intro x y hxy
    exact hblk.2 _ _ (by simp; omega)
  refine ⟨M - S, U, E - U * S * Uᴴ, hUU, ?_, ?_, hpart', ?_, ?_, ?_⟩
  · rw [← hMA] at hτ
    exact (specNorm_sub_le _ _).trans (add_le_add hE ((specNorm_mul_single_mul_le_split hUU p q
      (M p q)).trans hτ))
  · simp only [hMdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc, hUU.conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_one]
    abel
  · exact blockTriangular_sub_single_split hpart hi hbt (by rw [hblk.1]; exact hblk.2) rfl rfl
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · refine hhalf 0 (i + 1) (by omega) fun x y ⟨hx, _⟩ => ?_
      have hx' := congrArg Fin.val hx
      simp only [blockIndex, p] at hx'
      omega
    · refine hhalf (i + 1) (d - i - 1) (by omega) fun x y ⟨_, hy⟩ => ?_
      have hy' := congrArg Fin.val hy
      simp only [blockIndex, q] at hy'
      omega
    · rw [hSsub r (hnot r (List.mem_append_left _ hr))]
      exact hact r (List.mem_cons_of_mem _ hr)
  · intro r hr
    rw [hSsub r (hnot r (List.mem_append_right _ hr))]
    exact hdone r hr

/-- A finished block: if the output `out'` agrees with `out` off the first active range $r$ and
its part on $r$ is the list of eigenvalues of the block $\mathbf{A}_r$ (the roots of its
characteristic polynomial, with multiplicity), the range moves from active to finished. -/
theorem DeflationInv.finish {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {r : ℕ × ℕ}
    {rest done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε (r :: rest) done A out) {out' : Fin (n + 1) → ℂ}
    (hout : ∀ j : Fin (n + 1), ¬(r.1 ≤ (j : ℕ) ∧ (j : ℕ) < r.1 + r.2) → out' j = out j)
    (hroots : (subBlock A r).charpoly.roots = (List.ofFn (subVec out' r) : Multiset ℂ)) :
    DeflationInv H ε rest (r :: done) A out' := by
  unfold DeflationInv at h ⊢
  obtain ⟨M, U, E, hU, hE, hM, hpart, hBT, hact, hdone⟩ := h
  have key : ∀ (L L' : List (ℕ × ℕ)), L.Perm L' → ∀ i : ℕ,
      (∀ a ∈ L, ∀ b ∈ L, a.1 ≤ i → i < a.1 + a.2 → b.1 ≤ i → i < b.1 + b.2 → a = b) →
      L.find? (fun q => decide (q.1 ≤ i ∧ i < q.1 + q.2)) =
        L'.find? (fun q => decide (q.1 ≤ i ∧ i < q.1 + q.2)) := by
    intro L L' hp i
    induction hp with
    | nil => intro _; rfl
    | cons x _ ih =>
      intro hu
      rw [List.find?_cons, List.find?_cons,
        ih fun a ha b hb => hu a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)]
    | swap x y l =>
      intro hu
      by_cases hx : x.1 ≤ i ∧ i < x.1 + x.2 <;> by_cases hy : y.1 ≤ i ∧ i < y.1 + y.2
      · obtain rfl := hu x (by simp) y (by simp) hx.1 hx.2 hy.1 hy.2
        rfl
      all_goals simp [hx, hy]
    | trans h1 h2 ih1 ih2 =>
      intro hu
      exact (ih1 hu).trans (ih2 fun a ha b hb => hu a (h1.mem_iff.mpr ha) b (h1.mem_iff.mpr hb))
  have hperm : (rest ++ r :: done).Perm (r :: rest ++ done) := List.perm_middle
  have huniq : ∀ i : ℕ, i < n + 1 → ∀ a ∈ r :: rest ++ done, ∀ b ∈ r :: rest ++ done,
      a.1 ≤ i → i < a.1 + a.2 → b.1 ≤ i → i < b.1 + b.2 → a = b := by
    intro i hi a ha b hb h1 h2 h3 h4
    obtain ⟨c, -, hc⟩ := hpart.2.2 i hi
    exact (hc a ⟨ha, h1, h2⟩).trans (hc b ⟨hb, h3, h4⟩).symm
  have hlab : @rangeLabel (n + 1) (r :: rest ++ done) =
      @rangeLabel (n + 1) (rest ++ r :: done) := by
    funext k
    unfold rangeLabel
    rw [key _ _ hperm.symm k (huniq k k.isLt)]
  refine ⟨M, U, E, hU, hE, hM,
    ⟨hperm.nodup_iff.mpr hpart.1, fun s hs => hpart.2.1 s (hperm.mem_iff.mp hs),
      fun i hi => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨c, ⟨hc1, hc2, hc3⟩, hcu⟩ := hpart.2.2 i hi
    exact ⟨c, ⟨hperm.mem_iff.mpr hc1, hc2, hc3⟩,
      fun y hy => hcu y ⟨hperm.mem_iff.mp hy.1, hy.2.1, hy.2.2⟩⟩
  · rw [← hlab]
    exact hBT
  · intro s hs
    exact hact s (List.mem_cons_of_mem _ hs)
  · intro s hs
    rcases List.mem_cons.mp hs with h | hs
    · rw [h, (hact r (by simp)).1]
      exact hroots
    · rw [(hdone s hs)]
      congr 1
      have hsmem : s ∈ r :: rest ++ done := List.mem_append_right _ hs
      have hrmem : r ∈ r :: rest ++ done := by simp
      obtain ⟨hs1, hs2⟩ := (hpart.2.1 s hsmem)
      have hsv : subVec out' s = subVec out s := by
        funext k
        simp only [subVec, Function.comp_apply]
        apply hout
        rintro ⟨h1, h2⟩
        have hj : ((blockIndex n s k : Fin (n + 1)) : ℕ) = s.1 + k := by
          change min (s.1 + (k : ℕ)) n = s.1 + k
          have := k.isLt
          exact min_eq_left (by omega)
        have hEq := huniq (blockIndex n s k : ℕ) (blockIndex n s k).isLt r hrmem s hsmem h1 h2
          (by rw [hj]; omega) (by rw [hj]; omega)
        have hnd := hpart.1
        exact (List.nodup_append.mp hnd).2.2 r (by simp) s hs hEq
      rw [hsv]

/-- The order of the active ranges does not matter: the invariant holds for every
permutation of them. -/
theorem DeflationInv.perm {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ}
    {active active' done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) (hp : active.Perm active') :
    DeflationInv H ε active' done A out := by
  unfold DeflationInv at h ⊢
  obtain ⟨M, U, E, hU, hE, hM, hpart, hBT, hact, hdone⟩ := h
  have hp' : (active ++ done).Perm (active' ++ done) := hp.append_right done
  have key : ∀ (L L' : List (ℕ × ℕ)), L.Perm L' → ∀ i : ℕ,
      (∀ a ∈ L, ∀ b ∈ L, a.1 ≤ i → i < a.1 + a.2 → b.1 ≤ i → i < b.1 + b.2 → a = b) →
      L.find? (fun q => decide (q.1 ≤ i ∧ i < q.1 + q.2)) =
        L'.find? (fun q => decide (q.1 ≤ i ∧ i < q.1 + q.2)) := by
    intro L L' hp i
    induction hp with
    | nil => intro _; rfl
    | cons x _ ih =>
      intro hu
      rw [List.find?_cons, List.find?_cons,
        ih fun a ha b hb => hu a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)]
    | swap x y l =>
      intro hu
      by_cases hx : x.1 ≤ i ∧ i < x.1 + x.2 <;> by_cases hy : y.1 ≤ i ∧ i < y.1 + y.2
      · obtain rfl := hu x (by simp) y (by simp) hx.1 hx.2 hy.1 hy.2
        rfl
      all_goals simp [hx, hy]
    | trans h1 h2 ih1 ih2 =>
      intro hu
      exact (ih1 hu).trans (ih2 fun a ha b hb => hu a (h1.mem_iff.mpr ha) b (h1.mem_iff.mpr hb))
  have huniq : ∀ i : ℕ, i < n + 1 → ∀ a ∈ active ++ done, ∀ b ∈ active ++ done,
      a.1 ≤ i → i < a.1 + a.2 → b.1 ≤ i → i < b.1 + b.2 → a = b := by
    intro i hi a ha b hb h1 h2 h3 h4
    obtain ⟨c, -, hc⟩ := hpart.2.2 i hi
    exact (hc a ⟨ha, h1, h2⟩).trans (hc b ⟨hb, h3, h4⟩).symm
  have hlab : @rangeLabel (n + 1) (active ++ done) = @rangeLabel (n + 1) (active' ++ done) := by
    funext k
    unfold rangeLabel
    rw [key _ _ hp' k (huniq k k.isLt)]
  refine ⟨M, U, E, hU, hE, hM, ⟨hp'.nodup_iff.mp hpart.1,
    fun s hs => hpart.2.1 s (hp'.mem_iff.mpr hs), fun i hi => ?_⟩, ?_, ?_, hdone⟩
  · obtain ⟨c, ⟨hc1, hc2, hc3⟩, hcu⟩ := hpart.2.2 i hi
    exact ⟨c, ⟨hp'.mem_iff.mp hc1, hc2, hc3⟩,
      fun y hy => hcu y ⟨hp'.mem_iff.mpr hy.1, hy.2.1, hy.2.2⟩⟩
  · rw [← hlab]
    exact hBT
  · intro s hs
    exact hact s (hp.mem_iff.mpr hs)

/-- There are at most $n + 1$ ranges, active and finished: they are nonempty and disjoint. -/
theorem DeflationInv.length_le {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ}
    {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) : (active ++ done).length ≤ n + 1 := by
  unfold DeflationInv at h
  obtain ⟨M, U, E, -, -, -, hpart, -, -, -⟩ := h
  have hlt : ∀ r ∈ active ++ done, r.1 < n + 1 := fun r hr => by
    have := hpart.2.1 r hr
    omega
  have hinj : ∀ x ∈ active ++ done, ∀ y ∈ active ++ done, x.1 = y.1 → x = y := by
    intro x hx y hy hxy
    have hx' := hpart.2.1 x hx
    have hy' := hpart.2.1 y hy
    obtain ⟨c, -, hc⟩ := hpart.2.2 x.1 (hlt x hx)
    exact (hc x ⟨hx, le_refl _, by omega⟩).trans (hc y ⟨hy, by omega, by omega⟩).symm
  have hnd : ((active ++ done).map Prod.fst).Nodup :=
    List.Nodup.map_on (fun x hx y hy hxy => hinj x hx y hy hxy) hpart.1
  have hsub : (active ++ done).map Prod.fst ⊆ List.range (n + 1) := fun a ha => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr (hlt r hr)
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-- **The fuel of the worklist**: while a range is active, the progress measure
$2\lvert\mathrm{done}\rvert + \lvert\mathrm{active}\rvert$ is below $2(n + 1)$, so a loop
of fuel $2N$ whose measure is the iteration count plus one never runs out (exactly tight). -/
theorem DeflationInv.two_mul_length_add_length_lt {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ε : ℝ} {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) (hne : active ≠ []) :
    2 * done.length + active.length < 2 * (n + 1) := by
  have h1 := DeflationInv.length_le h
  have hpos : 0 < active.length := List.length_pos_of_ne_nil hne
  simp only [List.length_append] at h1
  omega

/-- The label of an index in a range of a partition is the start of that range. -/
private theorem rangeLabel_eq_of_mem_roots {N : ℕ} {rs : List (ℕ × ℕ)}
    (hrs : IsRangePartition N rs) {r : ℕ × ℕ} (hr : r ∈ rs) {k : Fin N} (hk₁ : r.1 ≤ (k : ℕ))
    (hk₂ : (k : ℕ) < r.1 + r.2) : rangeLabel rs k = r.1 := by
  unfold rangeLabel
  cases hf : rs.find? (fun r => (r.1 ≤ (k : ℕ) ∧ (k : ℕ) < r.1 + r.2 : Bool)) with
  | none => exact absurd (List.find?_eq_none.mp hf r hr) (by simp [hk₁, hk₂])
  | some r₀ =>
    have h₀ := List.find?_some hf
    simp only [decide_eq_true_eq] at h₀
    have := (hrs.2.2 k k.2).unique ⟨List.mem_of_find?_eq_some hf, h₀⟩ ⟨hr, hk₁, hk₂⟩
    simp [this]

/-- For a partition into ranges, the diagonal block of the label of a range is its `subBlock`
up to reindexing, so the roots of its characteristic polynomial are those of `subBlock`. -/
private theorem roots_charpoly_toSquareBlock_eq {rs : List (ℕ × ℕ)}
    (hrs : IsRangePartition (n + 1) rs) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    {r : ℕ × ℕ} (hr : r ∈ rs) (out : Fin (n + 1) → ℂ)
    (hroots : (subBlock M r).charpoly.roots = (List.ofFn (subVec out r) : Multiset ℂ)) :
    (M.toSquareBlock (rangeLabel rs) r.1).charpoly.roots =
      (Finset.univ.filter fun i => rangeLabel rs i = r.1).val.map out := by
  have hrv := hrs.2.1 r hr
  have hidx : ∀ a : Fin r.2, (blockIndex n r a : ℕ) = r.1 + a := fun a => by
    simp only [blockIndex]; omega
  let φ : Fin r.2 → {i // rangeLabel rs i = r.1} := fun a =>
    ⟨blockIndex n r a, rangeLabel_eq_of_mem_roots hrs hr (by rw [hidx]; omega)
      (by rw [hidx]; omega)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => ?_, fun ⟨i, hi⟩ => ?_⟩
    · have := congrArg (fun x : {i // rangeLabel rs i = r.1} => ((x : Fin (n + 1)) : ℕ)) hab
      simp only [φ, hidx] at this
      exact Fin.ext (by omega)
    · obtain ⟨r', ⟨hr', h₁, h₂⟩, -⟩ := hrs.2.2 i i.2
      have hr'v := hrs.2.1 r' hr'
      have hlab := rangeLabel_eq_of_mem_roots hrs hr' h₁ h₂
      have : r' = r := (hrs.2.2 r.1 (by omega)).unique ⟨hr', by omega, by omega⟩
        ⟨hr, le_rfl, by omega⟩
      subst this
      exact ⟨⟨i - r'.1, by omega⟩, Subtype.ext (Fin.ext (by rw [hidx]; simp; omega))⟩
  let e := Equiv.ofBijective φ hφ
  have hblk : subBlock M r =
      Matrix.reindex e.symm e.symm (M.toSquareBlock (rangeLabel rs) r.1) := by
    ext a b; simp [subBlock, Matrix.toSquareBlock, Matrix.toSquareBlockProp, e, φ]
  rw [← Matrix.charpoly_reindex e.symm, ← hblk, hroots, ← Fin.univ_val_map,
    ← Finset.univ_val_map_subtype_restrict, ← Multiset.map_univ_val_equiv e, Multiset.map_map]
  rfl

/-- **The backward error of deflation**: when no range is active, the output is exactly the
list of eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some $\mathbf{E}$ with
$\|\mathbf{E}\|_2 \le \varepsilon$. [BanksGarzaVargasSrivastava2022, §6], in exact
arithmetic. -/
theorem DeflationInv.exists_roots_eq {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ}
    {done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε [] done A out) :
    ∃ E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, specNorm E ≤ ε ∧
      (H + E).charpoly.roots = (List.ofFn out : Multiset ℂ) := by
  obtain ⟨M, U, E, hUU, hE, rfl, hpart, hbt, -, hdone⟩ := h
  simp only [List.nil_append] at hpart hbt
  refine ⟨E, hE, ?_⟩
  have hUU' : U * Uᴴ = 1 := hUU.mul_conjTranspose_self
  have hchar : (H + E).charpoly = (Uᴴ * (H + E) * U).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
  have hsing : ∀ s : Finset (Fin (n + 1)), s.val.map out = ∑ i ∈ s, ({out i} : Multiset ℂ) := by
    intro s
    have := Multiset.sum_map_singleton (s.val.map out)
    rw [Multiset.map_map] at this
    exact this.symm
  -- the roots of each diagonal block are the outputs on its range
  have hblock : ∀ a ∈ Finset.univ.image (rangeLabel (N := n + 1) done),
      ((Uᴴ * (H + E) * U).toSquareBlock (rangeLabel done) a).charpoly.roots =
        ∑ i ∈ Finset.univ.filter fun i => rangeLabel done i = a, ({out i} : Multiset ℂ) := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r, ⟨hr, h₁, h₂⟩, -⟩ := hpart.2.2 k k.2
    rw [rangeLabel_eq_of_mem_roots hpart hr h₁ h₂,
      roots_charpoly_toSquareBlock_eq hpart _ hr out (hdone r hr), hsing]
  have hne : ∏ a ∈ Finset.univ.image (rangeLabel (N := n + 1) done),
      ((Uᴴ * (H + E) * U).toSquareBlock (rangeLabel done) a).charpoly ≠ 0 :=
    (Polynomial.monic_prod_of_monic _ _ fun a _ => Matrix.charpoly_monic _).ne_zero
  rw [hchar, hbt.charpoly, Polynomial.roots_prod _ _ hne, ← Fin.univ_val_map, hsing]
  change ∑ a ∈ _, _ = _
  rw [Finset.sum_congr rfl hblock, Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem (rangeLabel done) (Finset.mem_univ i))]

/-- **The forward error of deflation** (Bauer–Fike): when no range is active and
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
every output is within $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\,\varepsilon$ of some
$\mathbf{d}_j$. [GolubVanLoan2013, Theorem 7.2.2]. -/
theorem DeflationInv.exists_norm_sub_le {H A V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ε : ℝ} {done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε [] done A out)
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (i : Fin (n + 1)) :
    ∃ j, ‖d j - out i‖ ≤ pseudoConditionNumber V * ε := by
  obtain ⟨E, hE, hroots⟩ := h.exists_roots_eq
  have hmem : out i ∈ (H + E).charpoly.roots := by
    rw [hroots, Multiset.mem_coe, List.mem_ofFn]; exact ⟨i, rfl⟩
  obtain ⟨x, hx, hEx⟩ := exists_mulVec_eq_smul_of_mem_spectrum (A := H + E) (μ := out i)
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ((Polynomial.mem_roots'.mp hmem).2))
  obtain ⟨j, hj⟩ := exists_norm_sub_mul_norm_le_pseudoConditionNumber_mul hV hHV x (out i)
  have hres : H *ᵥ x - out i • x = -(E *ᵥ x) := by
    rw [Matrix.add_mulVec] at hEx
    rw [← sub_eq_zero] at hEx
    rw [eq_neg_iff_add_eq_zero, ← hEx]; abel
  have hxpos : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by simpa using hx)
  refine ⟨j, le_of_mul_le_mul_right ?_ hxpos⟩
  calc ‖d j - out i‖ * ‖WithLp.toLp 2 x‖ ≤ pseudoConditionNumber V * ‖WithLp.toLp 2 (E *ᵥ x)‖ := by
        rw [hres, WithLp.toLp_neg, norm_neg] at hj; exact hj
    _ ≤ pseudoConditionNumber V * (ε * ‖WithLp.toLp 2 x‖) := by
        gcongr
        exact (norm_toLp_mulVec_le E x).trans (by gcongr)
    _ = pseudoConditionNumber V * ε * ‖WithLp.toLp 2 x‖ := by ring

end NLAlib
