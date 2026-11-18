/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.DeflationHypotheses

/-!
# Range updates and quantitative invariants of Hessenberg deflation

Disjoint ranges retain their output coordinates when one block is finished. A unitary
similarity and split preserve the existing deflation invariant. Global spectral separation
and conditioning hypotheses imply the quantitative decoupling assumptions of each active
block, with the same accumulated perturbation bound.

## Main results

* `NLAlib.IsRangePartition.disjoint`: distinct partition ranges do not overlap.
* `NLAlib.IsRangePartition.perm`, `NLAlib.IsRangePartition.split_cons`,
  `NLAlib.IsRangePartition.split_append`: permuting and splitting the ranges of a partition.
* `NLAlib.IsRangePartition.subBlock_apply`, `NLAlib.IsRangePartition.subBlock_eq_of_agree`,
  `NLAlib.IsRangePartition.subBlock_eq_of_block`: the blocks of a partition.
* `NLAlib.subVec_setSubVec_self`: reading a written range returns its new values.
* `NLAlib.DeflationInv.rapidDecouplingHyps`: raw global assumptions imply block assumptions.
* `NLAlib.DeflationInv.conj_split`: one block similarity followed by a split.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- The active and finished ranges of a deflation state partition all matrix indices. -/
theorem DeflationInv.partition {n : ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ε : ℝ} {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) : IsRangePartition (n + 1) (active ++ done) := by
  obtain ⟨_, _, _, _, _, _, hp, _⟩ := h
  exact hp

/-- An active range is nonempty, lies inside the global matrix, and is upper Hessenberg. -/
theorem DeflationInv.active_block {n : ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ε : ℝ} {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) {r : ℕ × ℕ} (hr : r ∈ active) :
    1 ≤ r.2 ∧ r.1 + r.2 ≤ n + 1 ∧ IsUpperHessenberg (subBlock A r) := by
  have hp := h.partition.2.1 r (List.mem_append_left _ hr)
  obtain ⟨_, _, _, _, _, _, _, _, ha, _⟩ := h
  exact ⟨hp.1, hp.2, (ha r hr).2⟩

/-- Two different ranges of a partition do not overlap. -/
theorem IsRangePartition.disjoint {N : ℕ} {rs : List (ℕ × ℕ)} (h : IsRangePartition N rs)
    {x y : ℕ × ℕ} (hx : x ∈ rs) (hy : y ∈ rs) (hne : x ≠ y) :
    x.1 + x.2 ≤ y.1 ∨ y.1 + y.2 ≤ x.1 := by
  by_contra hc
  push Not at hc
  obtain ⟨hx1, hx2⟩ := h.2.1 x hx
  obtain ⟨hy1, hy2⟩ := h.2.1 y hy
  rcases le_total x.1 y.1 with hle | hle
  · obtain ⟨c, -, hu⟩ := h.2.2 y.1 (by omega)
    exact hne ((hu x ⟨hx, hle, by omega⟩).trans (hu y ⟨hy, le_rfl, by omega⟩).symm)
  · obtain ⟨c, -, hu⟩ := h.2.2 x.1 (by omega)
    exact hne ((hu x ⟨hx, le_rfl, by omega⟩).trans (hu y ⟨hy, hle, by omega⟩).symm)

section Out
variable {n : ℕ}

/-- The vector `out` with its part on the range $r$ replaced by `v`. -/
def setSubVec (out : Fin (n + 1) → ℂ) (r : ℕ × ℕ) (v : Fin r.2 → ℂ) : Fin (n + 1) → ℂ :=
  fun j => if h : r.1 ≤ (j : ℕ) ∧ (j : ℕ) < r.1 + r.2 then v ⟨j - r.1, by omega⟩ else out j

/-- `NLAlib.setSubVec` changes nothing outside the range. -/
theorem setSubVec_apply_of_not_mem (out : Fin (n + 1) → ℂ) (r : ℕ × ℕ) (v : Fin r.2 → ℂ)
    (j : Fin (n + 1)) (hj : ¬(r.1 ≤ (j : ℕ) ∧ (j : ℕ) < r.1 + r.2)) :
    setSubVec out r v j = out j := by
  simp only [setSubVec, dif_neg hj]

/-- `NLAlib.subVec` reads back the part that `NLAlib.setSubVec` wrote. -/
theorem subVec_setSubVec_self (out : Fin (n + 1) → ℂ) (r : ℕ × ℕ) (v : Fin r.2 → ℂ)
    (hr : r.1 + r.2 ≤ n + 1) : subVec (setSubVec out r v) r = v := by
  ext i
  have hb : (blockIndex n r i : ℕ) = r.1 + i := by
    simp only [blockIndex]; have := i.2; omega
  simp only [subVec, Function.comp, setSubVec]
  rw [dif_pos (by rw [hb]; have := i.2; omega)]
  congr 1
  ext
  simp only [hb]; omega

/-- `NLAlib.setSubVec` changes nothing on a range disjoint from the one it writes. -/
theorem subVec_setSubVec_of_disjoint (out : Fin (n + 1) → ℂ) (r r' : ℕ × ℕ) (v : Fin r.2 → ℂ)
    (hr' : r'.1 + r'.2 ≤ n + 1) (hd : r'.1 + r'.2 ≤ r.1 ∨ r.1 + r.2 ≤ r'.1) :
    subVec (setSubVec out r v) r' = subVec out r' := by
  ext i
  have hb : (blockIndex n r' i : ℕ) = r'.1 + i := by
    simp only [blockIndex]; have := i.2; omega
  simp only [subVec, Function.comp]
  apply setSubVec_apply_of_not_mem
  rw [hb]; have := i.2; omega

/-- `NLAlib.subBlock` reads back the block that `NLAlib.setSubBlock` wrote. -/
theorem subBlock_setSubBlock_self (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℕ × ℕ)
    (Bm : Matrix (Fin r.2) (Fin r.2) ℂ) (hr : r.1 + r.2 ≤ n + 1) :
    subBlock (setSubBlock A r Bm) r = Bm := by
  ext i j
  have hbi : ∀ i : Fin r.2, (blockIndex n r i : ℕ) = r.1 + i := fun i => by
    simp only [blockIndex]; have := i.2; omega
  have hi := i.2
  have hj := j.2
  simp only [subBlock, Matrix.submatrix_apply, setSubBlock, Matrix.of_apply]
  rw [dif_pos (by rw [hbi, hbi]; omega)]
  congr 1 <;> ext <;> simp only [hbi] <;> omega

end Out


/-- An active block has norm at most $\|\mathbf{H}\|_2 + \varepsilon$. -/
theorem DeflationInv.specNorm_subBlock_le {n : ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ε : ℝ} {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) {r : ℕ × ℕ} (hr : r ∈ active) :
    specNorm (subBlock A r) ≤ specNorm H + ε := by
  obtain ⟨M, U, E, hUU, hE, rfl, hpart, hbt, hact, hdone⟩ := h
  have hrr := hpart.2.1 r (List.mem_append_left _ hr)
  rw [← (hact r hr).1]
  have hQ : HasOrthonormalCols U := by rw [hasOrthonormalCols_iff]; exact hUU
  have hinj : Function.Injective (blockIndex n r) := by
    intro a b hab
    have := congrArg Fin.val hab
    simp only [blockIndex] at this
    have ha := a.2
    have hb := b.2
    exact Fin.ext (by omega)
  calc specNorm (subBlock (Uᴴ * (H + E) * U) r)
      ≤ specNorm (Uᴴ * (H + E) * U) := specNorm_submatrix_le _ hinj hinj
    _ = specNorm (H + E) := hQ.specNorm_conjTranspose_mul_mul _
    _ ≤ specNorm H + specNorm E := specNorm_add_le _ _
    _ ≤ specNorm H + ε := by linarith

/-- The hypotheses of rapid decoupling on the first active block, from those of the whole run
(with $\delta/2$ in place of $\delta$: the block's norm is at most twice that of the input). -/
theorem DeflationInv.rapidDecouplingHyps {n n' : ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ε : ℝ} {lo : ℕ} {rest done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε ((lo, n' + 1) :: rest) done A out) {B θ α γ δ g : ℝ} {m F : ℕ}
    (hS : ShiftedQRHyps H B θ α γ δ g m F)
    (hε : ε ≤ ((rest.length + done.length : ℕ) : ℝ) * (δ * frobNorm H)) :
    RapidDecouplingHyps (subBlock A (lo, n' + 1)) (δ * frobNorm H) B θ α γ (δ / 2) m F := by
  have hlen := DeflationInv.length_le h
  simp only [List.length_append, List.length_cons] at hlen
  obtain ⟨⟨V, dv, hV, hHV, hκ, hgap⟩, hg, hm1, hθ, hα, hBα, hγ0, hγ1, hδ0, hτ1, hτ2, hF⟩ := hS
  have hτ0 : 0 ≤ δ * frobNorm H := mul_nonneg hδ0.le (frobNorm_nonneg _)
  have hcast : ((rest.length + done.length : ℕ) : ℝ) ≤ ((n + 1 - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : rest.length + done.length ≤ n + 1 - 1)
  have hε1 : ε ≤ ((n + 1 - 1 : ℕ) : ℝ) * (δ * frobNorm H) :=
    hε.trans (mul_le_mul_of_nonneg_right hcast hτ0)
  have hmem : ((lo, n' + 1) : ℕ × ℕ) ∈ (lo, n' + 1) :: rest := List.mem_cons_self
  have hB2 : pseudoConditionNumber V ≤ B / 2 := by linarith
  have hεg : ε ≤ g / (16 * ((n : ℝ) + 1) * (B / 2)) := by
    refine hε1.trans (hτ1.trans (le_of_eq ?_))
    push_cast
    congr 1
    ring
  obtain ⟨Vr, dr, hVr, hVrd, hκr⟩ := h.exists_pseudoConditionNumber_subBlock_le hV hHV hB2 hg
    hgap hεg hmem
  have hnorm := h.specNorm_subBlock_le hmem
  have hsp : (δ / 2) * specNorm (subBlock A (lo, n' + 1)) ≤ δ * frobNorm H := by
    have h1 : specNorm (subBlock A (lo, n' + 1)) ≤ 2 * frobNorm H := by
      have := specNorm_le_frobNorm H
      linarith [hε1.trans hτ2]
    calc (δ / 2) * specNorm (subBlock A (lo, n' + 1)) ≤ (δ / 2) * (2 * frobNorm H) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = δ * frobNorm H := by ring
  refine ⟨⟨Vr, dr, hVr, hVrd, by linarith⟩, hm1, hθ, hα, hBα, hγ0, hγ1, half_pos hδ0, hsp, ?_⟩
  rw [one_div_div]
  exact hF

/-- An active range and a finished range do not overlap, and the finished range is inside. -/
theorem DeflationInv.disjoint_of_mem {n : ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ}
    {active done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε active done A out) {x r : ℕ × ℕ} (hx : x ∈ active) (hr : r ∈ done) :
    (r.1 + r.2 ≤ x.1 ∨ x.1 + x.2 ≤ r.1) ∧ r.1 + r.2 ≤ n + 1 := by
  obtain ⟨M, U, E, -, -, -, hpart, -⟩ := h
  have hne : x ≠ r := by
    rintro rfl
    exact (List.nodup_append.mp hpart.1).2.2 x hx x hr rfl
  have hd := hpart.disjoint (List.mem_append_left _ hx) (List.mem_append_right _ hr) hne
  exact ⟨hd.symm, (hpart.2.1 r (List.mem_append_right _ hr)).2⟩


/-- A shifted QR step of the first block, then its split: if the first active block of
$\mathbf{A}$ is replaced by $\mathbf{H}' = \mathbf{U}^{\mathsf H}\mathbf{A}_r\mathbf{U}$
(unitary $\mathbf{U}$, upper Hessenberg result) and $\lvert h'_{i+1,i}\rvert \le \tau$, the
invariant holds with the ranges $(lo, i + 1)$ and $(lo + i + 1, d - i - 1)$ in its place and
$\varepsilon + \tau$. -/
theorem DeflationInv.conj_split {n n' lo : ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ}
    {rest done : List (ℕ × ℕ)} {out : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε ((lo, n' + 1) :: rest) done A out)
    {U H' : Matrix (Fin (n' + 1)) (Fin (n' + 1)) ℂ} (hU : HasOrthonormalCols U)
    (hH' : H' = Uᴴ * subBlock A (lo, n' + 1) * U) (hHess : IsUpperHessenberg H')
    (hr : lo + (n' + 1) ≤ n + 1) {i : ℕ} (hi : i < n') {τ : ℝ}
    (hτ : ‖H' (Fin.succ ⟨i, hi⟩) (Fin.castSucc ⟨i, hi⟩)‖ ≤ τ) :
    DeflationInv H (ε + τ) ((lo, i + 1) :: (lo + i + 1, n' + 1 - i - 1) :: rest) done
      (setSubBlock A (lo, n' + 1) H') out := by
  have hconj := h.conj (r := (lo, n' + 1)) List.mem_cons_self (Ub := U) hU
    (by rw [← hH']; exact hHess)
  rw [← hH'] at hconj
  exact hconj.split (i := i) (τ := τ) (by omega) (by
    rw [subBlock_setSubBlock_self A (lo, n' + 1) H' hr]; exact hτ)


/-- A partition into ranges stays one under a permutation of the list. -/
theorem IsRangePartition.perm {N : ℕ} {L L' : List (ℕ × ℕ)}
    (h : IsRangePartition N L) (hp : L.Perm L') : IsRangePartition N L' :=
  ⟨hp.nodup_iff.mp h.1, fun r hr => h.2.1 r (hp.mem_iff.mpr hr), fun i hi => by
    obtain ⟨c, ⟨hc1, hc2, hc3⟩, hcu⟩ := h.2.2 i hi
    exact ⟨c, ⟨hp.mem_iff.mp hc1, hc2, hc3⟩,
      fun y hy => hcu y ⟨hp.mem_iff.mpr hy.1, hy.2.1, hy.2.2⟩⟩⟩

/-- Splitting the first range of a partition into two consecutive ranges gives a partition. -/
theorem IsRangePartition.split_cons {N lo d i : ℕ} {rest : List (ℕ × ℕ)}
    (h : IsRangePartition N ((lo, d) :: rest)) (hi : i + 1 < d) :
    IsRangePartition N ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest) := by
  obtain ⟨hnd, hval, huniq⟩ := h
  have hlo := hval (lo, d) List.mem_cons_self
  have hpar : ∀ r ∈ rest, ∀ k < N, r.1 ≤ k → k < r.1 + r.2 → ¬(lo ≤ k ∧ k < lo + d) := by
    intro r hr k hk h₁ h₂ h₃
    have := (huniq k hk).unique ⟨List.mem_cons_of_mem _ hr, h₁, h₂⟩ ⟨List.mem_cons_self, h₃⟩
    exact (List.nodup_cons.mp hnd).1 (this ▸ hr)
  simp only at hlo
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, (List.nodup_cons.mp hnd).2⟩⟩
    · simp only [List.mem_cons, Prod.mk.injEq, not_or]
      exact ⟨by omega, fun hr => hpar _ hr lo (by omega) le_rfl (by simp) ⟨le_rfl, by omega⟩⟩
    · exact fun hr => hpar _ hr (lo + i + 1) (by omega) le_rfl (by simp; omega)
        ⟨by omega, by omega⟩
  · intro r hr
    simp only [List.mem_cons] at hr
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

/-- Splitting a range in the middle of a partition into two consecutive ranges, the right one
first, gives a partition. -/
theorem IsRangePartition.split_append {N lo d i : ℕ} {rs done : List (ℕ × ℕ)}
    (h : IsRangePartition N (rs ++ [(lo, d)] ++ done)) (hi : i + 1 < d) :
    IsRangePartition N (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)] ++ done) := by
  have hp0 : (rs ++ [(lo, d)] ++ done).Perm ((lo, d) :: (rs ++ done)) := by
    simp [List.perm_middle]
  have hp1 : ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: (rs ++ done)).Perm
      (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)] ++ done) := by
    refine (List.Perm.swap _ _ _).trans ?_
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact (List.perm_middle.trans (List.Perm.cons _ List.perm_middle)).symm
  exact ((h.perm hp0).split_cons hi).perm hp1

/-- The block of a range of a partition is read without clamping. -/
theorem IsRangePartition.subBlock_apply {n : ℕ} {L : List (ℕ × ℕ)}
    (hL : IsRangePartition (n + 1) L) {r : ℕ × ℕ} (hr : r ∈ L)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a b : Fin r.2) :
    subBlock A r a b = A ⟨r.1 + a, by have := (hL.2.1 r hr).2; omega⟩
      ⟨r.1 + b, by have := (hL.2.1 r hr).2; omega⟩ := by
  simp only [subBlock, Matrix.submatrix_apply]
  congr 1 <;> exact Fin.ext (hL.val_blockIndex hr _)

/-- A matrix that agrees with $\mathbf{A}$ off the range $(lo, d)$ of a partition has the same
blocks on the other ranges. -/
theorem IsRangePartition.subBlock_eq_of_agree {n : ℕ} {L : List (ℕ × ℕ)}
    (hL : IsRangePartition (n + 1) L) {lo d : ℕ} (hr : (lo, d) ∈ L) {q : ℕ × ℕ} (hq : q ∈ L)
    (hne : q ≠ (lo, d)) {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hag : ∀ i j : Fin (n + 1), ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) →
      ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) → A' i j = A i j) :
    subBlock A' q = subBlock A q := by
  have hd := hL.disjoint hq hr hne
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [subBlock, Matrix.submatrix_apply]
  apply hag <;> rw [hL.val_blockIndex hq] <;> simp only at hd <;> omega

/-- The block of the range $(lo, d)$ of a partition read from its entries. -/
theorem IsRangePartition.subBlock_eq_of_block {n : ℕ} {L : List (ℕ × ℕ)}
    (hL : IsRangePartition (n + 1) L) {lo d : ℕ} (hr : (lo, d) ∈ L)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : ∀ (a b : Fin d) (i j : Fin (n + 1)), (i : ℕ) = lo + a → (j : ℕ) = lo + b →
      A i j = B a b) : subBlock A (lo, d) = B := by
  ext a b
  exact hB a b _ _ (hL.val_blockIndex hr a) (hL.val_blockIndex hr b)

end NLAlib
