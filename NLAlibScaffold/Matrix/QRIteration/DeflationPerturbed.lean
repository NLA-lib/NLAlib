/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.HessenbergDeflation
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Matrix.Spectral.Schur
public import NLAlibScaffold.Matrix.Perturbation.EigenvalueBackward

/-!
# Deflation with perturbed block steps

The deflation invariant `NLAlib.DeflationInv` records the current blocks as the diagonal blocks
of $\mathbf{U}^{\mathsf H}(\mathbf{H} + \mathbf{E})\mathbf{U}$ with $\|\mathbf{E}\|_2 \le
\varepsilon$. In exact arithmetic an active block changes by a unitary similarity
(`NLAlib.DeflationInv.conj`); in floating point it changes by a **perturbed** unitary similarity,
and a small eigenvalue routine returns the roots of a perturbed block. Both add their backward
error to $\varepsilon$, because a perturbation of one diagonal block embeds into the whole matrix
with the same spectral norm and keeps the block triangular structure
(`NLAlib.IsPerturbedUnitarySimilar.exists_submatrix`). The invariant can also be re-based at the
current matrix: the accumulated perturbation becomes one perturbed unitary similarity from
$\mathbf{H}$, and the invariant holds with error $0$ from there. This is how a worklist round is
composed as a backward step ([BanksGarzaVargasSrivastava2022, §6], Theorem 6.3, backward half).

## Main results

* `NLAlib.DeflationInv.exists_isPerturbedUnitarySimilar_rebase`: re-basing at the current matrix.
* `NLAlib.DeflationInv.setSubBlock_of_isPerturbedUnitarySimilar`: a perturbed similarity of an
  active block.
* `NLAlib.DeflationInv.finish_of_specNorm_le`: a block finished with the roots of a perturbed
  block.
* `NLAlib.IsEigenvalueListing.exists_injective_eq_comp_of_charpoly_dvd`: the eigenvalues of a
  matrix whose characteristic polynomial divides one with simple roots are a subfamily of them.
* `Matrix.BlockTriangular.charpoly_subBlock_dvd`: a diagonal block's characteristic polynomial
  divides the whole.
* `NLAlib.DeflationInv.exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub`: condition and
  separation of the active blocks after a perturbation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Re-basing the deflation invariant**: if the invariant holds for $\mathbf{H}$ with error
$\varepsilon$, there is a matrix $\mathbf{M}$, a perturbed unitary similarity of $\mathbf{H}$ with
backward error $\varepsilon$, for which the invariant holds with error $0$ and the same ranges,
current matrix and outputs. -/
theorem DeflationInv.exists_isPerturbedUnitarySimilar_rebase
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H M ε ∧
      DeflationInv M 0 active done A out := by
  obtain ⟨M, U, E, hU, hE, hM, hrest⟩ := h
  exact ⟨M, ⟨U, E, hU, hE, hM⟩, M, 1, 0, hasOrthonormalCols_one, by rw [specNorm_zero],
    by simp, hrest⟩

/-- **A perturbed unitary similarity of an active block**: if the invariant holds with error
$\varepsilon$, $r$ is an active range, and $\mathbf{B}'$ is upper Hessenberg and a perturbed
unitary similarity of the block of $\mathbf{A}$ on $r$ with backward error $e$, the invariant
holds with error $\varepsilon + e$ after writing $\mathbf{B}'$ into that block. -/
theorem DeflationInv.setSubBlock_of_isPerturbedUnitarySimilar
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε e : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out) {r : ℕ × ℕ}
    (hr : r ∈ active) {B' : Matrix (Fin r.2) (Fin r.2) ℂ}
    (hB : IsPerturbedUnitarySimilar (subBlock A r) B' e) (hHess : IsUpperHessenberg B') :
    DeflationInv H (ε + e) active done (setSubBlock A r B') out := by
  obtain ⟨M, U, E, hUU, hE, hM, hpart, hbt, hact, hdone⟩ := h
  have hrm : r ∈ active ++ done := List.mem_append_left _ hr
  have hBM : IsPerturbedUnitarySimilar (M.submatrix (blockIndex n r) (blockIndex n r)) B' e := by
    have : subBlock M r = subBlock A r := (hact r hr).1
    rw [← this] at hB; exact hB
  obtain ⟨M', hMM', hsub, hoff, hbtk⟩ := hBM.exists_submatrix (hpart.blockIndex_injective hrm)
  obtain ⟨U', E', hU', hE', hM'⟩ := (show IsPerturbedUnitarySimilar H M ε from
    ⟨U, E, hUU, hE, hM⟩).trans hMM'
  -- a block of another range of the partition is unchanged
  have hother : ∀ r' ∈ active ++ done, r' ≠ r → subBlock M' r' = subBlock M r' := by
    intro r' hr' hne
    ext a b
    exact hoff _ _ (fun ⟨c, hc⟩ => hpart.blockIndex_ne hrm hr' hne a c hc.symm)
      (fun ⟨c, hc⟩ => hpart.blockIndex_ne hrm hr' hne b c hc.symm)
  have hset := hpart.subBlock_setSubBlock hrm A B'
  refine ⟨M', U', E', hU', hE', hM', hpart, hbtk _ r.1 (fun a => ?_) hbt, fun r' hr' => ?_,
    fun r' hr' => ?_⟩
  · have := hpart.val_blockIndex hrm a
    exact hpart.rangeLabel_eq hrm (by omega) (by omega)
  · by_cases hne : r' = r
    · subst hne
      exact ⟨hsub.trans hset.1.symm, by rw [hset.1]; exact hHess⟩
    · have hr'm := List.mem_append_left done hr'
      rw [hother r' hr'm hne, hset.2 r' hr'm hne]
      exact hact r' hr'
  · have hne : r' ≠ r := fun h => (List.nodup_append.mp hpart.1).2.2 r hr r' hr' h.symm
    rw [hother r' (List.mem_append_right _ hr') hne]
    exact hdone r' hr'

/-- The invariant reads the current matrix only through its active blocks: if two matrices have
the same active blocks, the invariant holds for one exactly when it holds for the other. -/
theorem DeflationInv.congr_active
    {H A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out)
    (hA : ∀ r ∈ active, subBlock A' r = subBlock A r) :
    DeflationInv H ε active done A' out := by
  obtain ⟨M, U, E, hUU, hE, hM, hpart, hbt, hact, hdone⟩ := h
  exact ⟨M, U, E, hUU, hE, hM, hpart, hbt, fun r hr => by rw [hA r hr]; exact hact r hr, hdone⟩

/-- **Finishing a block with the roots of a perturbed block**: if the invariant holds with error
$\varepsilon$ and the first active range $r$, $\|\mathbf{F}\|_2 \le \beta$, and the output
`out'` agrees with `out` off $r$ and lists on $r$ the roots (with multiplicity) of the block of
$\mathbf{A}$ on $r$ plus $\mathbf{F}$, then $r$ is finished with error $\varepsilon + \beta$. -/
theorem DeflationInv.finish_of_specNorm_le
    {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε β : ℝ} {r : ℕ × ℕ}
    {rest done : List (ℕ × ℕ)} {out out' : Fin (n + 1) → ℂ}
    (h : DeflationInv H ε (r :: rest) done A out) {F : Matrix (Fin r.2) (Fin r.2) ℂ}
    (hF : specNorm F ≤ β)
    (hout : ∀ j : Fin (n + 1), ¬(r.1 ≤ (j : ℕ) ∧ (j : ℕ) < r.1 + r.2) → out' j = out j)
    (hroots : (subBlock A r + F).charpoly.roots = (List.ofFn (subVec out' r) : Multiset ℂ)) :
    DeflationInv H (ε + β) rest (r :: done) A out' := by
  -- triangularize the perturbed block: a Hessenberg perturbed similarity with error `β`
  obtain ⟨V, hV, hT⟩ := exists_hasOrthonormalCols_isUpperTriangular (subBlock A r + F)
  have hB : IsPerturbedUnitarySimilar (subBlock A r) (Vᴴ * (subBlock A r + F) * V) β := by
    simpa using ((isPerturbedUnitarySimilar_add (subBlock A r) F).trans
      (hV.isPerturbedUnitarySimilar _)).mono (by simpa using hF)
  have hHess : IsUpperHessenberg (Vᴴ * (subBlock A r + F) * V) := fun i j hij =>
    hT (show j < i by rw [Fin.lt_def]; omega)
  have h' := h.setSubBlock_of_isPerturbedUnitarySimilar List.mem_cons_self hB hHess
  have hpart : IsRangePartition (n + 1) (r :: rest ++ done) := by
    obtain ⟨_, _, _, _, _, _, hpart, -⟩ := h; exact hpart
  have hset := hpart.subBlock_setSubBlock (by simp) A (Vᴴ * (subBlock A r + F) * V)
  have hcp : (Vᴴ * (subBlock A r + F) * V).charpoly = (subBlock A r + F).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hV.mul_conjTranspose_self, Matrix.one_mul]
  have h'' := h'.finish hout (by rw [hset.1, hcp, hroots])
  refine h''.congr_active fun r' hr' => ?_
  have hne : r' ≠ r := fun h =>
    (List.nodup_cons.mp (List.nodup_append.mp hpart.1).1).1 (h ▸ hr')
  exact (hset.2 r' (by simp [hr']) hne).symm

/-- **A subfamily of a simple spectrum**: if $\mathbf{a}$ lists the eigenvalues of $\mathbf{A}$,
$\mathbf{b}$ lists those of $\mathbf{B}$ and is injective, and the characteristic polynomial of
$\mathbf{A}$ divides that of $\mathbf{B}$, then $\mathbf{a} = \mathbf{b} \circ f$ for an
injective $f$: the eigenvalues of $\mathbf{A}$ are distinct and are among those of
$\mathbf{B}$. -/
theorem IsEigenvalueListing.exists_injective_eq_comp_of_charpoly_dvd {K ι κ m l : Type*}
    [Field K] [Fintype ι] [Fintype κ] [Fintype m] [DecidableEq m] [Fintype l] [DecidableEq l]
    {A : Matrix m m K} {B : Matrix l l K} {a : ι → K} {b : κ → K}
    (ha : IsEigenvalueListing A a) (hb : IsEigenvalueListing B b)
    (hdvd : A.charpoly ∣ B.charpoly) (hinj : Function.Injective b) :
    ∃ f : ι → κ, Function.Injective f ∧ ∀ i, a i = b (f i) := by
  classical
  have hra : A.charpoly.roots = Finset.univ.val.map a := by
    rw [isEigenvalueListing_iff.mp ha, Finset.prod_eq_multiset_prod]
    simpa only [Multiset.map_map, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map a)
  have hrb : B.charpoly.roots = Finset.univ.val.map b := by
    rw [isEigenvalueListing_iff.mp hb, Finset.prod_eq_multiset_prod]
    simpa only [Multiset.map_map, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map b)
  have hle : Finset.univ.val.map a ≤ Finset.univ.val.map b := by
    rw [← hra, ← hrb]
    exact Polynomial.roots.le_of_dvd B.charpoly_monic.ne_zero hdvd
  have hnd : (Finset.univ.val.map a).Nodup :=
    Multiset.nodup_of_le hle (Multiset.Nodup.map hinj Finset.univ.nodup)
  have hmem : ∀ i, ∃ j, b j = a i := fun i => by
    simpa using Multiset.mem_of_le hle (Multiset.mem_map_of_mem a (Finset.mem_univ i))
  choose f hf using hmem
  refine ⟨f, fun i j hij => ?_, fun i => (hf i).symm⟩
  have : a i = a j := by rw [← hf i, ← hf j, hij]
  exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_univ _) j (Finset.mem_univ _) this

/-- **The characteristic polynomial of a diagonal block divides the whole**: if $\mathbf{M}$ is
block upper triangular for a partition `rs` of the indices into ranges and $r$ is one of its
ranges, the characteristic polynomial of the block of $\mathbf{M}$ on $r$ divides that of
$\mathbf{M}$. -/
theorem _root_.Matrix.BlockTriangular.charpoly_subBlock_dvd
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {rs : List (ℕ × ℕ)}
    (hM : M.BlockTriangular (rangeLabel rs)) (hrs : IsRangePartition (n + 1) rs)
    {r : ℕ × ℕ} (hr : r ∈ rs) : (subBlock M r).charpoly ∣ M.charpoly := by
  have hrv := hrs.2.1 r hr
  have hidx := hrs.val_blockIndex hr
  let φ : Fin r.2 → {i // rangeLabel rs i = r.1} := fun a =>
    ⟨blockIndex n r a, hrs.rangeLabel_eq hr (by rw [hidx]; omega) (by rw [hidx]; omega)⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => hrs.blockIndex_injective hr (congrArg Subtype.val hab),
      fun ⟨i, hi⟩ => ?_⟩
    obtain ⟨r', ⟨hr', h₁, h₂⟩, -⟩ := hrs.2.2 i i.2
    have hr'v := hrs.2.1 r' hr'
    have hlab := hrs.rangeLabel_eq hr' h₁ h₂
    have : r' = r := (hrs.2.2 r.1 (by omega)).unique ⟨hr', by omega, by omega⟩
      ⟨hr, le_rfl, by omega⟩
    subst this
    exact ⟨⟨i - r'.1, by omega⟩, Subtype.ext (Fin.ext (by rw [hidx]; simp; omega))⟩
  let e := Equiv.ofBijective φ hφ
  have hblk : subBlock M r =
      Matrix.reindex e.symm e.symm (M.toSquareBlock (rangeLabel rs) r.1) := by
    ext a b; simp [subBlock, Matrix.toSquareBlock, Matrix.toSquareBlockProp, e, φ]
  rw [hblk, Matrix.charpoly_reindex, hM.charpoly]
  exact Finset.dvd_prod_of_mem _
    (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (φ ⟨0, by omega⟩).2⟩)

/-- **Condition and separation of every active block after a perturbation**: under the invariant
`NLAlib.DeflationInv` with perturbation bound $\varepsilon$, if
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, eigenvalues separated by $g > 0$ and
$\varepsilon \le g/(16(n + 1)B)$, then every active block of $\mathbf{A}$ is diagonalizable with
condition at most $2B$ and eigenvalues separated by $g/2$: its eigenvalues are some of those of
$\mathbf{H} + \mathbf{E}$, which keep the separation $g - 2B\|\mathbf{E}\|_2$
(`NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub`). The condition half is
`NLAlib.DeflationInv.exists_pseudoConditionNumber_subBlock_le`. -/
theorem DeflationInv.exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub
    {H A V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} {active done : List (ℕ × ℕ)}
    {out : Fin (n + 1) → ℂ} (h : DeflationInv H ε active done A out) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {B g : ℝ}
    (hB : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hε : ε ≤ g / (16 * (n + 1) * B)) {r : ℕ × ℕ} (hr : r ∈ active) :
    ∃ (Vr : Matrix (Fin r.2) (Fin r.2) ℂ) (dr : Fin r.2 → ℂ), IsUnit Vr ∧
      subBlock A r * Vr = Vr * Matrix.diagonal dr ∧ pseudoConditionNumber Vr ≤ 2 * B ∧
      ∀ i j, i ≠ j → g / 2 ≤ ‖dr i - dr j‖ := by
  obtain ⟨Vr, dr, hVr, hAr, hκr⟩ :=
    h.exists_pseudoConditionNumber_subBlock_le hV hHV hB hg hgap hε hr
  refine ⟨Vr, dr, hVr, hAr, hκr, ?_⟩
  obtain ⟨M, U, E, hUU, hE, rfl, hpart, hbt, hact, -⟩ := h
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  have hE' := hE.trans hε
  obtain ⟨V', d', hV', hV'd, -, hsep⟩ :=
    exists_pseudoConditionNumber_le_and_le_norm_sub hV hHV hB hg hgap hE'
  have hBE : B * specNorm E ≤ g / 16 := by
    calc B * specNorm E ≤ B * (g / (16 * (n + 1) * B)) :=
          mul_le_mul_of_nonneg_left hE' (by linarith)
      _ = g / (16 * (n + 1)) := by field_simp
      _ ≤ g / 16 := by gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hsmall : g / 2 ≤ g - 2 * B * specNorm E := by linarith
  have hLM : IsEigenvalueListing (Uᴴ * (H + E) * U) d' := by
    rw [isEigenvalueListing_iff, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      hUU.mul_conjTranspose_self, Matrix.one_mul, ← isEigenvalueListing_iff]
    exact isEigenvalueListing_of_mul_eq_mul_diagonal ((Matrix.isUnit_iff_isUnit_det _).mp hV')
      hV'd
  have hLr : IsEigenvalueListing (subBlock (Uᴴ * (H + E) * U) r) dr := by
    rw [(hact r hr).1]
    exact isEigenvalueListing_of_mul_eq_mul_diagonal ((Matrix.isUnit_iff_isUnit_det _).mp hVr) hAr
  have hd' : Function.Injective d' := fun i j hij => by
    by_contra hne
    have := hsep i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  obtain ⟨f, hf, hfe⟩ := hLr.exists_injective_eq_comp_of_charpoly_dvd hLM
    (hbt.charpoly_subBlock_dvd hpart (List.mem_append_left _ hr)) hd'
  intro i j hij
  rw [hfe i, hfe j]
  exact hsmall.trans (hsep _ _ (hf.ne hij))

end NLAlib
