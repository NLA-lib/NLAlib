/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.StoredProducts
public import NLAlib.Ops.Blas.BlockCopy
public import NLAlib.Matrix.Perturbation.UnitarySimilarity

/-!
# Rectangular blocks of a stored square matrix

A square matrix of order $N$ stored column-major (`NLAlib.HoldsMatrix`) has its rectangular block
with corner $(r_0, c_0)$, $m$ rows and $q$ columns at the strided view of offset
$2(c_0 N + r_0)$ and leading dimension $N$. This file reads such a block entry by entry, copies a
dense block into it (`NLAlib.Ops.copyStrided`) and describes the result, and bounds the error of
replacing a block of columns: the column block of $\mathbf{U}$ is the product by the column
selection of the identity, which has orthonormal columns.

## Main definitions

* `NLAlib.subRect`: the rectangular block of a square matrix.
* `NLAlib.setRect`: a square matrix with a rectangular block replaced.

## Main results

* `NLAlib.HoldsMatrix.readBlock_rect`: the entries of a block through its strided view.
* `NLAlib.copyStrided_writes_rect`: copying a dense block into a rectangular block.
* `NLAlib.subRect_cols_eq_mul`, `NLAlib.hasOrthonormalCols_subRect_one`: a column block is a
  product by a column selection.
* `NLAlib.mul_embedBlock_eq_setRect`: the product by an embedded block replaces a column block.
* `NLAlib.specNorm_setRect_matMulWord_sub_le`: a column block replaced by its stored product with
  a near-unitary block, against the product by the embedded unitary.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

/-- The **rectangular block** of $\mathbf{A}$ with corner $(r_0, c_0)$, $m$ rows and $q$
columns: its entry $(i, j)$ is $a_{r_0 + i, c_0 + j}$ (zero off the matrix). -/
def subRect {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (r0 c0 m q : ℕ) : Matrix (Fin m) (Fin q) ℂ :=
  Matrix.of fun i j =>
    if h : r0 + (i : ℕ) < N ∧ c0 + (j : ℕ) < N then A ⟨r0 + i, h.1⟩ ⟨c0 + j, h.2⟩ else 0

/-- $\mathbf{A}$ with the **rectangular block** of corner $(r_0, c_0)$ and the shape of
$\mathbf{B}$ replaced by $\mathbf{B}$. -/
def setRect {N m q : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (r0 c0 : ℕ) (B : Matrix (Fin m) (Fin q) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if h : r0 ≤ (i : ℕ) ∧ (i : ℕ) < r0 + m ∧ c0 ≤ (j : ℕ) ∧ (j : ℕ) < c0 + q then
      B ⟨i - r0, by omega⟩ ⟨j - c0, by omega⟩
    else A i j

/-- The component words of a finite complex matrix, extended by zero off its domain. -/
private def rectPairs {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℂ) (i j : ℕ) : ℝ × ℝ :=
  if hi : i < r then if hj : j < c then ((A ⟨i, hi⟩ ⟨j, hj⟩).re,
    (A ⟨i, hi⟩ ⟨j, hj⟩).im) else (0, 0) else (0, 0)

/-- Each entry of a rectangular block inside the matrix is read through the strided view of
offset $2(c_0 N + r_0)$ and leading dimension $N$. -/
theorem HoldsMatrix.readBlock_rect {N r0 c0 m q : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} {s : Store ℝ} (h : HoldsMatrix a A s) (hr : r0 + m ≤ N)
    (hc : c0 + q ≤ N) (i : Fin m) (j : Fin q) :
    s.readBlock a.1 (a.2 + 2 * (c0 * N + r0) + 2 * (j * N + i)) 2 =
      some [(subRect A r0 c0 m q i j).re, (subRect A r0 c0 m q i j).im] := by
  have hi := i.isLt
  have hj := j.isLt
  have e : a.2 + 2 * (c0 * N + r0) + 2 * (j * N + i) =
      a.2 + 2 * (((⟨c0 + j, by omega⟩ : Fin N) : ℕ) * N + ((⟨r0 + i, by omega⟩ : Fin N) : ℕ)) := by
    simp only; ring
  rw [e, h.read_entry]
  simp [subRect, show r0 + (i : ℕ) < N by omega, show c0 + (j : ℕ) < N by omega]

/-- The words of a rectangular block inside the matrix occupy only the matrix's block. -/
theorem rectFp_le {N r0 c0 m q : ℕ} (a : ℕ × ℕ) (hr : r0 + m ≤ N) (hc : c0 + q ≤ N) :
    (EntryCodec.pair ℝ).regionFp a.1 (a.2 + 2 * (c0 * N + r0)) q
      (fun i j => j * N + i) (fun _ => m) ≤ Store.inBlock a.1 a.2 (2 * (N * N)) := by
  rintro c x ⟨i, j, ⟨hj, hi⟩ | ⟨_, hi⟩, hx⟩
  · have hi' : i < m := hi
    have hj' : j < q := hj
    have hb := Idx.add_lt_mul (show c0 + j < N by omega) (show r0 + i < N by omega)
    change c = a.1 ∧ a.2 + 2 * (c0 * N + r0) + 2 * (j * N + i) ≤ x ∧
      x < a.2 + 2 * (c0 * N + r0) + 2 * (j * N + i) + 2 at hx
    exact ⟨hx.1, by nlinarith [hx.2.1], by nlinarith [hx.2.2]⟩
  · omega

/-- Writing a rectangular block replaces exactly that submatrix: if the words of the block
of corner $(r_0, c_0)$ hold $\mathbf{B}$ and every other word is kept, the store holds
`NLAlib.setRect`. -/
private theorem HoldsMatrix.of_rect_write {N r0 c0 m q : ℕ} {a : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} {B : Matrix (Fin m) (Fin q) ℂ}
    {st st' : Store ℝ} (hA : HoldsMatrix a A st) (hr : r0 + m ≤ N)
    (hfr : st.EqOff ((EntryCodec.pair ℝ).regionFp a.1 (a.2 + 2 * (c0 * N + r0)) q
      (fun i j => j * N + i) (fun _ => m)) st')
    (hB : st'.HoldsEntries (EntryCodec.pair ℝ) ⟨a.1, a.2 + 2 * (c0 * N + r0), m, q, N⟩
      (rectPairs B)) :
    HoldsMatrix a (setRect A r0 c0 B) st' := by
  have hget (i j : Fin N) (z : Fin 2) :
      st'.get a.1 (a.2 + 2 * (j * N + i) + z) =
        some ((EntryCodec.pair ℝ).words (rectPairs (setRect A r0 c0 B) i j) z) := by
    by_cases hm : r0 ≤ (i : ℕ) ∧ (i : ℕ) < r0 + m ∧ c0 ≤ (j : ℕ) ∧ (j : ℕ) < c0 + q
    · have hi : (i : ℕ) - r0 < m := by omega
      have hj : (j : ℕ) - c0 < q := by omega
      have he : a.2 + 2 * (c0 * N + r0) + 2 * (((j : ℕ) - c0) * N + ((i : ℕ) - r0)) =
          a.2 + 2 * (j * N + i) := by
        have hmul := congrArg (· * N) (Nat.sub_add_cancel hm.2.2.1)
        have hadd := Nat.sub_add_cancel hm.1
        nlinarith
      have hw := hB _ hi _ hj z
      simpa [rectPairs, i.isLt, j.isLt, hi, hj, setRect, hm, he] using hw
    · have hnot : ¬(EntryCodec.pair ℝ).regionFp a.1 (a.2 + 2 * (c0 * N + r0)) q
          (fun u v => v * N + u) (fun _ => m) a.1 (a.2 + 2 * (j * N + i) + z) := by
        rintro ⟨u, v, ⟨hv, hu⟩ | ⟨_, hu⟩, hw⟩
        · have hu' : u < m := hu
          have hv' : v < q := hv
          have he : a.2 + 2 * (c0 * N + r0) + 2 * (v * N + u) =
              a.2 + 2 * ((c0 + v) * N + (r0 + u)) := by ring
          have hlo : a.2 + 2 * (c0 * N + r0) + 2 * (v * N + u) ≤
              a.2 + 2 * (j * N + i) + z := hw.2.1
          have hhi : a.2 + 2 * (j * N + i) + z <
              a.2 + 2 * (c0 * N + r0) + 2 * (v * N + u) + 2 := hw.2.2
          rw [he] at hlo hhi
          have hz := z.isLt
          have hidx : j * N + i = (c0 + v) * N + (r0 + u) := by omega
          have hri := congrArg (· % N) hidx
          have hcj := congrArg (· / N) hidx
          have hub : r0 + u < N := by omega
          simp only [Idx.mod_add i.isLt, Idx.mod_add hub] at hri
          simp only [Idx.div_add i.isLt, Idx.div_add hub] at hcj
          exact hm ⟨by omega, by omega, by omega, by omega⟩
        · omega
      rw [hfr.get_eq hnot]
      fin_cases z
      · simpa [rectPairs, i.isLt, j.isLt, setRect, hm] using hA.get_re i j
      · simpa [rectPairs, i.isLt, j.isLt, setRect, hm] using hA.get_im i j
  apply HoldsMatrix.of_get
  · intro i j
    simpa [rectPairs, i.isLt, j.isLt] using hget i j 0
  · intro i j
    simpa [rectPairs, i.isLt, j.isLt, Nat.add_assoc] using hget i j 1

variable {Op Tst : Type} [Has ScalarOp Op]

/-- **Copying a dense block into a rectangular block** on a scalar machine and every tape:
`NLAlib.Ops.copyStrided` with $m$ rows, $q$ columns, the source leading dimension $m$ and the
destination leading dimension $N$, from $\mathbf{B}$ stored densely at `w` into the view of
offset $2(c_0 N + r_0)$ of the square matrix $\mathbf{A}$ of order $N$ stored at `a`, writes
only the words of that block and leaves `NLAlib.setRect`.
Shared by the trees of `NLAlib.ShiftedQR.copyToWork`, `NLAlib.ShiftedQR.copyToGlobal`,
`NLAlib.ShiftedQR.roundedLeafUpdate`. -/
theorem copyStrided_writes_rect {M : Machine ℝ} {I : Interp Op Tst ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {μ : Mem ℝ} {N r0 c0 m q : ℕ} {a w : ℕ × ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} {B : Matrix (Fin m) (Fin q) ℂ}
    (hl : μ.Live [w, a]) (hA : HoldsMatrix a A μ.store) (hB : HoldsMatrix w B μ.store)
    (hr : r0 + m ≤ N) (hc : c0 + q ≤ N) (ha : a.2 + 2 * (N * N) ≤ μ.store.len a.1)
    (hd : Fp.Disj (Store.inBlock w.1 w.2 (2 * (q * m))) (Store.inBlock a.1 a.2 (2 * (N * N)))) :
    Writes .total I τ (copyStrided (Op := Op) (Tst := Tst))
      (Env.frame [m, q, m, N] [w, (a.1, a.2 + 2 * (c0 * N + r0))])
      ((EntryCodec.pair ℝ).regionFp a.1 (a.2 + 2 * (c0 * N + r0)) q
        (fun i j => j * N + i) (fun _ => m))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix a (setRect A r0 c0 B) μ'.store) μ := by
  have hsrc := (EntryCodec.pair ℝ).regionFp_le_inBlock w.1 w.2 q (q * m)
    (fun i j => j * m + i) (fun _ => m) (fun _ hj _ hi => Idx.add_lt_mul hj hi)
  have hentries : μ.store.HoldsEntries (EntryCodec.pair ℝ) ⟨w.1, w.2, m, q, m⟩ (rectPairs B) := by
    intro i hi j hj z
    have hi' : i < m := hi
    have hj' : j < q := hj
    fin_cases z
    · simpa [rectPairs, hi', hj'] using hB.get_re ⟨i, hi'⟩ ⟨j, hj'⟩
    · simpa [rectPairs, hi', hj', Nat.add_assoc] using hB.get_im ⟨i, hi'⟩ ⟨j, hj'⟩
  have hc' := copyStrided_writes (τ := τ) hS (rectPairs B)
    (x := w) (y := (a.1, a.2 + 2 * (c0 * N + r0)))
    (by simpa [Mem.Live] using hl) hentries (by omega)
    (fun j hj i hi => by
      have hb := Idx.add_lt_mul (show c0 + j < N by omega) (show r0 + i < N by omega)
      dsimp only
      nlinarith) (hd.mono hsrc (rectFp_le a hr hc))
  refine (hc'.mono le_rfl ?_)
  intro μ' hfr ⟨he, hp⟩
  exact ⟨hp, hA.of_rect_write hr hfr he⟩

/-! ### Column blocks -/

/-- The column block of $\mathbf{U}$ on $[c_0, c_0 + q)$ is the product of $\mathbf{U}$ by the
same column block of the identity. -/
theorem subRect_cols_eq_mul {N c0 q : ℕ} (hc : c0 + q ≤ N) (U : Matrix (Fin N) (Fin N) ℂ) :
    subRect U 0 c0 N q = U * subRect (1 : Matrix (Fin N) (Fin N) ℂ) 0 c0 N q := by
  ext i j
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨c0 + j, by omega⟩ : Fin N)]
  · simp [subRect, show c0 + (j : ℕ) < N by omega, Matrix.one_apply]
  · intro k _ hk
    have : (k : ℕ) ≠ c0 + j := fun h => hk (Fin.ext h)
    simp [subRect, Matrix.one_apply, Fin.ext_iff, this]
  · simp

/-- A column block of the identity has orthonormal columns. -/
theorem hasOrthonormalCols_subRect_one {N c0 q : ℕ} (hc : c0 + q ≤ N) :
    HasOrthonormalCols (subRect (1 : Matrix (Fin N) (Fin N) ℂ) 0 c0 N q) := by
  rw [hasOrthonormalCols_iff]
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨c0 + a, by omega⟩ : Fin N)]
  · by_cases hab : a = b
    · subst hab
      simp [subRect, show c0 + (a : ℕ) < N by omega, Matrix.one_apply]
    · have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
      simp [subRect, show c0 + (a : ℕ) < N by omega, show c0 + (b : ℕ) < N by omega,
        Matrix.one_apply, Fin.ext_iff, hab, hab']
  · intro k _ hk
    have : (k : ℕ) ≠ c0 + a := fun h => hk (Fin.ext h)
    simp [subRect, Matrix.one_apply, Fin.ext_iff, this]
  · simp

/-- Replacing the column block $[c_0, c_0 + q)$ of the zero matrix by $\mathbf{D}$ is the product
of $\mathbf{D}$ by the adjoint column selection. -/
theorem setRect_zero_cols_eq_mul {N c0 q : ℕ}
    (D : Matrix (Fin N) (Fin q) ℂ) :
    setRect (0 : Matrix (Fin N) (Fin N) ℂ) 0 c0 D =
      D * (subRect (1 : Matrix (Fin N) (Fin N) ℂ) 0 c0 N q)ᴴ := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : c0 ≤ (j : ℕ) ∧ (j : ℕ) < c0 + q
  · rw [Finset.sum_eq_single (⟨(j : ℕ) - c0, by omega⟩ : Fin q)]
    · have e : c0 + ((j : ℕ) - c0) = j := by omega
      simp [setRect, hj, subRect, e, Matrix.one_apply]
    · intro k _ hk
      have : (j : ℕ) ≠ c0 + k := fun h => hk (Fin.ext (by simp; omega))
      simp [subRect, Matrix.one_apply, Fin.ext_iff, this]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [setRect, hj]
    · intro k _
      have : (j : ℕ) ≠ c0 + k := fun h => hj ⟨by omega, by have := k.isLt; omega⟩
      simp [subRect, Matrix.one_apply, Fin.ext_iff, this]

/-- The product by $\operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})$ (the block on
$[c_0, c_0 + q)$) replaces the column block $\mathbf{X}$ of $\mathbf{U}$ on that range by
$\mathbf{X}\mathbf{V}$. -/
theorem mul_embedBlock_eq_setRect {N c0 q : ℕ} (hc : c0 + q ≤ N) (U : Matrix (Fin N) (Fin N) ℂ)
    (V : Matrix (Fin q) (Fin q) ℂ) :
    U * embedBlock c0 V = setRect U 0 c0 (subRect U 0 c0 N q * V) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : c0 ≤ (j : ℕ) ∧ (j : ℕ) < c0 + q
  · simp only [setRect, Matrix.of_apply, Nat.zero_le, zero_add, i.isLt, hj, and_self,
      true_and, dite_true, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (fun a : Fin q => (⟨c0 + a, by omega⟩ : Fin N))
      (fun a b h => Fin.ext (by simpa using h)) _ _ (fun k hk => ?_) (fun a => ?_)
    · have hk' : ¬(c0 ≤ (k : ℕ) ∧ (k : ℕ) < c0 + q) := fun h =>
        hk ⟨⟨(k : ℕ) - c0, by omega⟩, Fin.ext (by simp; omega)⟩
      have hkj : k ≠ j := fun h => hk' (h ▸ hj)
      simp [embedBlock, hk', hkj]
    · have ha := a.isLt
      simp [subRect, embedBlock, show c0 + (a : ℕ) < N by omega, hj]
  · rw [Finset.sum_eq_single j]
    · simp [embedBlock, setRect, hj]
    · intro k _ hk
      by_cases hk' : c0 ≤ (k : ℕ) ∧ (k : ℕ) < c0 + q
      · simp [embedBlock, hk', hj]
      · simp [embedBlock, hk', hk]
    · simp

/-- Two replacements of the same column block differ by the replacement of the zero matrix with
the difference. -/
theorem setRect_sub_setRect {N c0 q : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (W W' : Matrix (Fin N) (Fin q) ℂ) :
    setRect U 0 c0 W - setRect U 0 c0 W' = setRect 0 0 c0 (W - W') := by
  ext i j
  simp only [setRect, Matrix.sub_apply, Matrix.of_apply, Matrix.zero_apply]
  split_ifs <;> simp

/-- Replacing a column block of the zero matrix does not increase the spectral norm. -/
theorem specNorm_setRect_zero_cols_le {N c0 q : ℕ} (hc : c0 + q ≤ N)
    (D : Matrix (Fin N) (Fin q) ℂ) :
    specNorm (setRect (0 : Matrix (Fin N) (Fin N) ℂ) 0 c0 D) ≤ specNorm D := by
  rw [setRect_zero_cols_eq_mul]
  refine (specNorm_mul_le _ _).trans ?_
  rw [specNorm_conjTranspose]
  exact mul_le_of_le_one_right (specNorm_nonneg D)
    (hasOrthonormalCols_subRect_one hc).specNorm_le_one

/-- A column block has spectral norm at most that of the matrix. -/
theorem specNorm_subRect_cols_le {N c0 q : ℕ} (hc : c0 + q ≤ N) (U : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (subRect U 0 c0 N q) ≤ specNorm U := by
  rw [subRect_cols_eq_mul hc]
  exact (specNorm_mul_le _ _).trans
    (mul_le_of_le_one_right (specNorm_nonneg U) (hasOrthonormalCols_subRect_one hc).specNorm_le_one)

/-- The growth of a stored product of $q$ terms, as a power of $1 + 24\boldsymbol{u}$: with
$a = 6\boldsymbol{u} + 5\boldsymbol{u}^2$ and $0 \le \boldsymbol{u} \le 1/8$,
$q(1 + a)^q(5\boldsymbol{u} + qa) \le (1 + 24\boldsymbol{u})^{2q(q+2)} - 1$. -/
theorem matMul_growth_le_pow {u : ℝ} (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) (q : ℕ) :
    (1 + (6 * u + 5 * u ^ 2)) ^ q * (5 * u + q * (6 * u + 5 * u ^ 2)) * q ≤
      (1 + 24 * u) ^ (2 * q * (q + 2)) - 1 := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha : 6 * u + 5 * u ^ 2 ≤ 24 * u := by nlinarith
  have hP : (1 + (6 * u + 5 * u ^ 2)) ^ q ≤ (1 + 24 * u) ^ q :=
    pow_le_pow_left₀ (by positivity) (by linarith) q
  have hP1 : 1 ≤ (1 + 24 * u) ^ q := one_le_pow₀ (by linarith)
  have hB := one_add_mul_le_pow (show (-2 : ℝ) ≤ 24 * u by linarith) (2 * q * q + 3 * q)
  have hsplit : (1 + 24 * u) ^ (2 * q * (q + 2)) =
      (1 + 24 * u) ^ q * (1 + 24 * u) ^ (2 * q * q + 3 * q) := by
    rw [← pow_add]; congr 1; ring
  have hc : (5 * u + q * (6 * u + 5 * u ^ 2)) * q ≤ (1 + 24 * u) ^ (2 * q * q + 3 * q) - 1 := by
    push_cast at hB
    have h5 : (q : ℝ) * (6 * u + 5 * u ^ 2) ≤ q * (53 / 8 * u) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hq
    nlinarith [mul_nonneg hq hu0, mul_nonneg (mul_nonneg hq hq) hu0]
  have hc0 : 0 ≤ (5 * u + q * (6 * u + 5 * u ^ 2)) * q := by positivity
  rw [hsplit]
  calc (1 + (6 * u + 5 * u ^ 2)) ^ q * (5 * u + q * (6 * u + 5 * u ^ 2)) * q
      = (1 + (6 * u + 5 * u ^ 2)) ^ q * ((5 * u + q * (6 * u + 5 * u ^ 2)) * q) := by ring
    _ ≤ (1 + 24 * u) ^ q * ((1 + 24 * u) ^ (2 * q * q + 3 * q) - 1) :=
        mul_le_mul hP hc hc0 (by positivity)
    _ ≤ _ := by nlinarith

/-- **A column block replaced by its stored product with a near-unitary block**: under the
standard model at $0 \le \boldsymbol{u} \le 1/8$, if $\|\mathbf{U}_b - \mathbf{V}\|_2 \le
\varepsilon_L$ with $\mathbf{V}$ unitary of order $q$ and $\varepsilon_L \ge 0$, then replacing
the column block $\mathbf{X}$ of $\mathbf{U}$ on $[c_0, c_0 + q)$ by
$\mathrm{fl}(\mathbf{X}\mathbf{U}_b)$ gives a matrix within
$((1 + 24\boldsymbol{u})^{2q(q+2)}(1 + \varepsilon_L) - 1)\|\mathbf{U}\|_2$ of
$\mathbf{U}\operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})$. -/
theorem specNorm_setRect_matMulWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) {N c0 q : ℕ} (hc : c0 + q ≤ N)
    (U : Matrix (Fin N) (Fin N) ℂ) {Ub V : Matrix (Fin q) (Fin q) ℂ} (hV : HasOrthonormalCols V)
    {εL : ℝ} (hεL : 0 ≤ εL) (hUb : specNorm (Ub - V) ≤ εL) :
    specNorm (setRect U 0 c0 (matMulWord M (subRect U 0 c0 N q) Ub) - U * embedBlock c0 V) ≤
      ((1 + 24 * u) ^ (2 * q * (q + 2)) * (1 + εL) - 1) * specNorm U := by
  set X := subRect U 0 c0 N q
  have hX : specNorm X ≤ specNorm U := specNorm_subRect_cols_le hc U
  have hU0 := specNorm_nonneg U
  have hUbn : specNorm Ub ≤ 1 + εL := by
    have := specNorm_add_le (Ub - V) V
    rw [sub_add_cancel] at this
    linarith [hV.specNorm_le_one]
  have hq : (0 : ℝ) ≤ √(q : ℝ) := Real.sqrt_nonneg _
  have hqq : √(q : ℝ) * √(q : ℝ) = q := Real.mul_self_sqrt (Nat.cast_nonneg q)
  have hXF : frobNorm X ≤ √(q : ℝ) * specNorm U := by
    refine (frobNorm_le_sqrt_card_mul_specNorm X).trans ?_
    rw [Fintype.card_fin]; exact mul_le_mul_of_nonneg_left hX hq
  have hUbF : frobNorm Ub ≤ √(q : ℝ) * (1 + εL) := by
    refine (frobNorm_le_sqrt_card_mul_specNorm Ub).trans ?_
    rw [Fintype.card_fin]; exact mul_le_mul_of_nonneg_left hUbn hq
  set g := (1 + (6 * u + 5 * u ^ 2)) ^ q * (5 * u + q * (6 * u + 5 * u ^ 2)) with hg
  have hg0 : 0 ≤ g := by positivity
  have hW := hM.specNorm_matMulWord_sub_le_growth hu0 hu8 X Ub
  have hFF : frobNorm X * frobNorm Ub ≤ q * (1 + εL) * specNorm U := by
    calc frobNorm X * frobNorm Ub ≤ (√(q : ℝ) * specNorm U) * (√(q : ℝ) * (1 + εL)) :=
          mul_le_mul hXF hUbF (frobNorm_nonneg _) (by positivity)
      _ = (√(q : ℝ) * √(q : ℝ)) * (1 + εL) * specNorm U := by ring
      _ = q * (1 + εL) * specNorm U := by rw [hqq]
  have hXV : specNorm (X * (Ub - V)) ≤ specNorm U * εL :=
    (specNorm_mul_le _ _).trans (mul_le_mul hX hUb (specNorm_nonneg _) hU0)
  have hgr := matMul_growth_le_pow hu0 hu8 q
  rw [mul_embedBlock_eq_setRect hc, setRect_sub_setRect]
  refine (specNorm_setRect_zero_cols_le hc _).trans ?_
  have e : matMulWord M X Ub - X * V = (matMulWord M X Ub - X * Ub) + X * (Ub - V) := by
    rw [Matrix.mul_sub]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  have h1 : specNorm (matMulWord M X Ub - X * Ub) ≤ g * q * (1 + εL) * specNorm U := by
    refine hW.trans ?_
    calc g * (frobNorm X * frobNorm Ub) ≤ g * (q * (1 + εL) * specNorm U) :=
          mul_le_mul_of_nonneg_left hFF hg0
      _ = g * q * (1 + εL) * specNorm U := by ring
  have h2 : g * q * (1 + εL) * specNorm U ≤
      ((1 + 24 * u) ^ (2 * q * (q + 2)) - 1) * (1 + εL) * specNorm U :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgr (by linarith)) hU0
  nlinarith

end NLAlib
