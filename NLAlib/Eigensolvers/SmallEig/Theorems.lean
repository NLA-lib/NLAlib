/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Program
public import NLAlib.Matrix.Perturbation.EigenvalueMatching
public import NLAlib.Ops.Confined
public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.Static

/-!
# The small-eigenvalue solver: headline theorems

[BanksGarzaVargasSrivastava2025, Theorem 1.1] as a theorem about the fixed program
`NLAlib.SmallEig.smallEigProg`: on any complex matrix $\mathbf{M}$ of order at most $n_{\max}$ and
norm at most $\Sigma$, with probability at least $1 - \varphi$ the program stores all eigenvalues
of $\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$, at the unit roundoff
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, conditional on the two random-matrix
theorems (`NLAlib.PolyLogTail.BoundsGinibreGap`, `NLAlib.PolyLogTail.BoundsGinibreCondition`),
which are hypotheses here and proved at the records
`NLAlib.ginibreGapRecord` <!-- value ginibreGapRecord --> $(10000e, 5, 1/2, 2)$,
`NLAlib.ginibreConditionRecord` <!-- value ginibreConditionRecord --> $(128e, 3, 2, 2)$ (the
`_unconditional` corollaries). The error is absolute: $\Sigma$ is an input, the paper's relative
form is the corollary `NLAlib.SmallEig.smallEig_relative`. [BanksGarzaVargasSrivastava2025,
Corollary 1.3] is the forward contract on blocks of order at most $k_{\max}$ and norm at most
$\Sigma$ (`NLAlib.SmallEig.smallEigProg_randomSmallEigContract`), which the shifted QR algorithm
consumes.

What is not claimed: a rounded Gaussian or disk sampler (the draws are exact tape values; their
rounding after the draw is modelled), range safety, the paper's question of $O(n^3)$ work.

## Main results

* `NLAlib.SmallEig.smallEigProg_pwrites`: Theorem 1.1 as a probabilistic block specification.
* `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`: Theorem 1.1.
* `NLAlib.SmallEig.smallEig_relative`: the relative form.
* `NLAlib.SmallEig.smallEigProg_randomSmallEigContract`: Corollary 1.3 as a routine contract.
* `NLAlib.SmallEig.smallEig_measureReal_not_forward_le`: Corollary 1.3 for one input.
* `NLAlib.SmallEig.smallEig_work_le`: the operation count.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-! ### The pieces of the proofs -/

/-- **The class of the matrix the core receives** in `NLAlib.SmallEig.smallEigProg`, relative to
the input $\mathbf{M}$: $\mathbf{H}$ is upper Hessenberg, diagonalizable with condition at most
$B_c$ and eigenvalues separated by $g_c$ (`NLAlib.SmallEig.smallEigCondition`,
`NLAlib.SmallEig.smallEigSeparation`), $\|\mathbf{H}\|_2 \le \Sigma + 3\delta/4$, and a perturbed
unitary similarity of $\mathbf{M}$ with backward error $5\delta/8$. -/
def SmallEigCoreClass {n : ℕ} (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail)
    (M H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  IsUpperHessenberg H ∧
    (∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
      H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ smallEigCondition nmax S δ φ c₂ ∧
      ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ ≤ ‖d i - d j‖) ∧
    specNorm H ≤ S + 3 * δ / 4 ∧ IsPerturbedUnitarySimilar M H (5 * δ / 8)

/-- **The reduction keeps the class** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], the step
from the perturbation to the core): on a machine with the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ and $M.\mathrm{lit}(0) = 0$, if
$\|\mathbf{M}\|_2 \le \Sigma$ and $\mathbf{M} + \mathbf{E}$, $\|\mathbf{E}\|_2 \le \delta/2$, has a
diagonalization with condition at most $2/t_2$ and eigenvalues separated by $t_1/2$ (the class of
`NLAlib.SmallEig.ginibrePerturb_pwrites`), then the rounded bottom-up Hessenberg form of
$\mathbf{M} + \mathbf{E}$ is in the class of the core (`NLAlib.SmallEig.SmallEigCoreClass`). -/
theorem smallEigCoreClass_hessenbergReduceLastWord {Mch : Machine ℝ} {u : ℝ}
    (hM : StdModel u id Mch) (hzero : Mch.lit 0 = 0) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax n : ℕ} (hn : n + 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {M E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hMS : specNorm M ≤ S)
    (hE : specNorm E ≤ δ / 2) (hV : IsUnit V) (hAV : (M + E) * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖) :
    SmallEigCoreClass nmax S δ φ c₁ c₂ M (hessenbergReduceLastWord Mch (M + E)) := by
  have hS : 0 < S := hδ.trans_le hδS
  have hn1 : 1 ≤ nmax := by omega
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨-, hu1, hu2, -⟩ := uSmallEig_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have ht₁ := (smallEigGap_pos_le hb₁ hn1 hS.le hδ hφ hφ1).1
  have ht₂ := (smallEigCond_pos_le hb₂ hn1 hS.le hδ hφ hφ1).1
  set t₁ := smallEigGap nmax S δ φ c₁
  set t₂ := smallEigCond nmax S δ φ c₂
  have hnn : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr; linarith
  have hb : u * (100000 * ((nmax : ℝ) + 1) ^ 2) ≤ 1 := by
    have := (hu.trans hu1).trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  have hnu : 100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1 := by nlinarith
  have hr : u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) ≤
      min (δ / 8) (t₁ / (64 * ((nmax : ℝ) + 1) * (2 / t₂))) := by
    have := hu.trans hu2
    unfold uSmallEigReduce at this
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨hHess, Q, hQ, -, hF⟩ :=
    hessenbergReduceLast_isPerturbedUnitarySimilar hM hzero hnu (M + E)
  set H := hessenbergReduceLastWord Mch (M + E)
  have hA : specNorm (M + E) ≤ 2 * S := by
    have := specNorm_add_le M E; linarith
  have hFb : specNorm (H - Qᴴ * (M + E) * Q) ≤ u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) := by
    refine hF.trans ?_
    have h0 : 0 ≤ specNorm (M + E) := specNorm_nonneg _
    calc 50 * ((n : ℝ) + 1) ^ 2 * u * specNorm (M + E)
        ≤ 50 * ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) := by gcongr
      _ ≤ _ := by
        have := mul_nonneg (mul_nonneg hu0 (sq_nonneg ((nmax : ℝ) + 1))) hS.le
        nlinarith
  have hFδ : specNorm (H - Qᴴ * (M + E) * Q) ≤ δ / 8 := hFb.trans (hr.trans (min_le_left _ _))
  have hFg : specNorm (H - Qᴴ * (M + E) * Q) ≤ t₁ / (64 * ((n : ℝ) + 1) * (1 / t₂)) := by
    refine hFb.trans (hr.trans ((min_le_right _ _).trans ?_))
    refine div_le_div_of_nonneg_left ht₁.le (by positivity) ?_
    rw [show 64 * ((nmax : ℝ) + 1) * (2 / t₂) = 128 * ((nmax : ℝ) + 1) * (1 / t₂) by ring]
    have : 0 < 1 / t₂ := by positivity
    nlinarith
  obtain ⟨V', d', hV', hHV', hκ', hgap'⟩ := class_of_rhess (B := 1 / t₂) hV hAV
    (by rw [show 2 * (1 / t₂) = 2 / t₂ by ring]; exact hκ) ht₁ hgap hQ hFg
  have hPUS : IsPerturbedUnitarySimilar M H (specNorm E + (0 + specNorm (H - Qᴴ * (M + E) * Q))) :=
    by
    have h2 := (hQ.isPerturbedUnitarySimilar (M + E)).add_right (H - Qᴴ * (M + E) * Q)
    rw [add_sub_cancel] at h2
    exact (isPerturbedUnitarySimilar_add M E).trans h2
  have hPUS' : IsPerturbedUnitarySimilar M H (5 * δ / 8) := hPUS.mono (by linarith)
  refine ⟨hHess, ⟨V', d', hV', hHV', ?_, hgap'⟩, ?_, hPUS'⟩
  · unfold smallEigCondition; rw [show 4 / t₂ = 4 * (1 / t₂) by ring]; exact hκ'
  · have := hPUS'.specNorm_le; linarith

/-- The memory of `NLAlib.SmallEig.smallEigProg` on a block of order $n + 2$ after its three
scratch buffers are allocated on top of $L$ buffers: the work matrix of $2(n + 2)^2$ words at
`(L, 0)`, the failure word and the threshold word, the input $\mathbf{M}$ at `w`, the words `qs` at
`q` and room for the output at `o`, all three below $L$. -/
def SmallEigScratch (n L : ℕ) (qs : List ℝ) (w q o : ℕ × ℕ)
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.store.length = L + 3 ∧ μ.store.len L = 2 * ((n + 2) * (n + 2)) ∧ μ.store.len (L + 1) = 1 ∧
    μ.store.len (L + 2) = 1 ∧ w.1 < L ∧ q.1 < L ∧ o.1 < L ∧
    o.2 + 2 * (n + 2) ≤ μ.store.len o.1 ∧ μ.store.readBlock q.1 q.2 qs.length = some qs ∧
    HoldsMatrix w M μ.store

/-- The scratch memory survives a run that writes only the output and above $L$, when the output
is apart from the matrix and the words. -/
theorem SmallEigScratch.of_eqOff {n L : ℕ} {qs : List ℝ} {w q o : ℕ × ℕ}
    {M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {μ μ' : Mem ℝ} {F : Fp}
    (h : SmallEigScratch n L qs w q o M μ) (hfr : μ.store.EqOff F μ'.store)
    (hF : F ≤ Store.inBlock o.1 o.2 (2 * (n + 2)) ⊔ Fp.above L)
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 2) * (n + 2))))
      (Store.inBlock o.1 o.2 (2 * (n + 2))))
    (hqo : Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * (n + 2)))) :
    SmallEigScratch n L qs w q o M μ' := by
  obtain ⟨h1, h2, h3, h4, hw, hq, ho, hr, hqs, hM⟩ := h
  have hab : ∀ {b} (k l : ℕ), b < L → Fp.Disj (Fp.above L) (Store.inBlock b k l) :=
    fun _ _ hb _ _ ha hi => absurd (hi.1 ▸ ha : L ≤ _) (by omega)
  refine ⟨by rw [hfr.length_eq, h1], by rw [hfr.len_eq, h2], by rw [hfr.len_eq, h3],
    by rw [hfr.len_eq, h4], hw, hq, ho, by rw [hfr.len_eq]; exact hr,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      ((Fp.disj_sup_left.mpr ⟨hqo.symm, hab _ _ hq⟩).mono hF le_rfl) hqs,
    hM.of_eqOff hfr ((Fp.disj_sup_left.mpr ⟨hwo.symm, hab _ _ hw⟩).mono hF le_rfl)⟩

/-- The scratch memory has its three operands and the scratch buffers live. -/
theorem SmallEigScratch.live {n L : ℕ} {qs : List ℝ} {w q o : ℕ × ℕ}
    {M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {μ : Mem ℝ}
    (h : SmallEigScratch n L qs w q o M μ) (zs : List (ℕ × ℕ))
    (hz : ∀ z ∈ zs, z = w ∨ z = q ∨ z = o ∨ z.1 < L + 3) : μ.Live zs := by
  intro z hz'
  obtain ⟨h1, -, -, -, hw, hq, ho, -⟩ := h
  rw [h1]
  rcases hz z hz' with rfl | rfl | rfl | h <;> omega

/-- The scratch memory after the allocation of the three buffers: from a memory holding
$\mathbf{M}$ at `w` and the words at `q`, with the output room at `o`, the store with the three
fresh buffers on top is `NLAlib.SmallEig.SmallEigScratch` at the old buffer count. -/
theorem SmallEigScratch.of_alloc {n : ℕ} {qs : List ℝ} {w q o : ℕ × ℕ}
    {M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ} {μ : Mem ℝ} {s₁ : Store ℝ}
    (hW : HoldsMatrix w M μ.store) (hq : μ.store.readBlock q.1 q.2 qs.length = some qs)
    (hl : μ.Live [w, q, o]) (hroom : o.2 + 2 * (n + 2) ≤ μ.store.len o.1)
    (hlen : s₁.length = μ.store.length + [2 * ((n + 2) * (n + 2)), 1, 1].length)
    (hlens : ∀ i (hi : i < [2 * ((n + 2) * (n + 2)), 1, 1].length),
      s₁.len (μ.store.length + i) = [2 * ((n + 2) * (n + 2)), 1, 1][i])
    (hBelow : Store.Below μ.store.length μ.store s₁) :
    SmallEigScratch n μ.store.length qs w q o M ⟨s₁, μ.pos⟩ := by
  have hwl : w.1 < μ.store.length := hl w (by simp)
  have hql : q.1 < μ.store.length := hl q (by simp)
  have hol : o.1 < μ.store.length := hl o (by simp)
  exact ⟨by simpa using hlen, by simpa using hlens 0 (by simp),
    by simpa using hlens 1 (by simp), by simpa using hlens 2 (by simp), hwl, hql, hol,
    by rw [(hBelow o.1 hol).1]; exact hroom, hBelow.readBlock_of hql hq,
    hW.of_below hBelow hwl⟩

/-- `NLAlib.SmallEig.smallEigProg` on a block of order at most $1$ copies its diagonal: on a scalar
machine, from a matrix $\mathbf{B}$ of order $d \le 1$ at `w` with room for the $2d$ output words
at `o`, apart, on every tape the run writes only the output and stores the diagonal of
$\mathbf{B}$. -/
theorem smallEigProg_writes_of_le_one {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (sG : ℕ) {d nq T : ℕ} (hd : d ≤ 1) {w q o : ℕ × ℕ} {τ : Tape ℝ} {μ : Mem ℝ}
    {B : Matrix (Fin d) (Fin d) ℂ} (hB : HoldsMatrix w B μ.store) (hl : μ.Live [w, q, o])
    (hroom : o.2 + 2 * d ≤ μ.store.len o.1)
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d))) :
    Writes .total I τ (smallEigProg (O := O) (Q := Q) sG).body (Env.frame [d, nq, T] [w, q, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ' => HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => B i i) μ'.store) μ := by
  unfold smallEigProg
  refine (writes_ifPos (n := 2 - d)
    (P := fun μ' => HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => B i i) μ'.store) rfl
    ?_).seq_le le_rfl ?_
  · rw [if_pos (by omega)]
    exact ((copyLeaf_writes hS hB hl hroom hwo :
      Writes .total I τ _ (Env.frame [d, nq, T] [w, q, o]) _ _ μ).in_frame rfl rfl hl)
  · intro μ₁ _ h₁
    refine writes_ifPos (n := d - 1) rfl ?_
    rw [if_neg (by omega)]
    exact h₁

/-- A matrix of order at most $1$ is listed by its diagonal. -/
theorem isEigenvalueListing_diag_of_le_one {d : ℕ} (hd : d ≤ 1) (B : Matrix (Fin d) (Fin d) ℂ) :
    IsEigenvalueListing B fun i => B i i := by
  have hT : B.IsUpperTriangular := fun i j hji => absurd hji (by omega)
  simpa using hT.isEigenvalueListing_diag

omit [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The copy step of `NLAlib.SmallEig.smallEigProg`: on a scalar machine, with the output apart
from the matrix and the words, from the scratch memory (`NLAlib.SmallEig.SmallEigScratch`) with
the threshold word copied, on every tape the copy of $\mathbf{M}$ from `w` to the work matrix at
`(L, 0)` writes only above $L$, keeps the scratch memory and the threshold word and stores
$\mathbf{M}$ at `(L, 0)`. -/
theorem smallEigProg_copy_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    {law : ℕ → Measure ℝ} {n L : ℕ} {qs : List ℝ} {w q o : ℕ × ℕ}
    {M : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ}
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1 + 1) * (n + 1 + 1))))
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1))))
    (hqo : Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock o.1 o.2 (2 * (n + 1 + 1))))
    {ρ : Env} {ds : List IExp} {args : List Operand}
    (hd : IExp.evalList ρ.idx ds = some [2 * ((n + 1 + 1) * (n + 1 + 1))])
    (ha : Operand.evalList ρ args = some [w, (L, 0)]) :
    PWrites law I (.frame ds args (unaryMap (Tst := Q) (Has.inj ScalarOp.copy : O)).body) ρ
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L)
      (fun μ => SmallEigScratch n L qs w q o M μ ∧ μ.store.get (L + 2) 0 = some (qs.getD 6 0))
      (fun μ => (SmallEigScratch n L qs w q o M μ ∧
        μ.store.get (L + 2) 0 = some (qs.getD 6 0)) ∧ HoldsMatrix (L, 0) M μ.store) 0 := by
  have hab : ∀ b k l, L ≤ b →
      Store.inBlock b k l ≤ Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L :=
    fun b k l hb _ _ hi => Or.inr (hi.1 ▸ hb)
  refine PWrites.of_writes le_rfl fun μ τ ⟨h, hTh⟩ => ?_
  have hwL := h.2.2.2.2.1
  exact ((copyMatrix_writes hS (τ := τ) h.2.2.2.2.2.2.2.2.2 (b := (L, 0))
    (by rw [h.2.1]; simp) (Fp.disj_inBlock_of_ne (by omega))).in_frame hd ha
    (h.live _ (by simp))).mono (hab _ _ _ le_rfl) fun μ' hfr ⟨_, hW⟩ =>
      ⟨⟨h.of_eqOff hfr (hab _ _ _ le_rfl) hwo hqo, hfr.keep (Store.readsOnly_get _ _ _)
        (Fp.disj_inBlock_of_ne (by omega)) hTh⟩, hW⟩

omit [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The perturbation step of `NLAlib.SmallEig.smallEigProg`: on a scalar machine with the standard
model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, index literals, a measurable
interpretation reading the tape only in its windows whose draws store the tape entry, a stream
`sG` with the standard real Gaussian law and the tails $c_1$, $c_2$ of the gap and the condition
of a complex Ginibre perturbation with $b_1, b_2 > 0$: let $n + 2 \le n_{\max}$,
$0 < \delta \le \Sigma$, $0 < \varphi \le 1$, $\|\mathbf{M}\|_2 \le \Sigma$, and the output apart
from the matrix and the words. From the scratch memory (`NLAlib.SmallEig.SmallEigScratch`) with
the threshold word copied and $\mathbf{M}$ at `(L, 0)`, except with probability at most
$3\varphi/4$ the call writes only above $L$ and stores $\mathbf{M} + \mathbf{E}$,
$\|\mathbf{E}\|_2 \le \delta/2$, with a diagonalization of condition at most $2/t_2$ and
eigenvalues separated by $t_1/2$ (`NLAlib.SmallEig.smallEigCond`, `NLAlib.SmallEig.smallEigGap`).
-/
theorem smallEigProg_perturb_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) (hSmp : IsSample I)
    {law : ℕ → Measure ℝ} {sG : ℕ} (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition) (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax n : ℕ} (hn : n + 1 + 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {M : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hMS : specNorm M ≤ S) {L : ℕ}
    {w q o : ℕ × ℕ}
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1 + 1) * (n + 1 + 1))))
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1))))
    (hqo : Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)))) {ρ : Env} {ds : List IExp}
    {args : List Operand}
    (hd : IExp.evalList ρ.idx ds = some [n + 1 + 1, (smallEigParams nmax S δ φ c₁ c₂).length])
    (ha : Operand.evalList ρ args = some [(L, 0), q, (L, 0)]) :
    PWrites law I (.frame ds args (ginibrePerturb (O := O) (Q := Q) sG).body) ρ
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L)
      (fun μ => (SmallEigScratch n L (smallEigParams nmax S δ φ c₁ c₂) w q o M μ ∧
        μ.store.get (L + 2) 0 = some ((smallEigParams nmax S δ φ c₁ c₂).getD 6 0)) ∧
        HoldsMatrix (L, 0) M μ.store)
      (fun μ => (SmallEigScratch n L (smallEigParams nmax S δ φ c₁ c₂) w q o M μ ∧
        μ.store.get (L + 2) 0 = some ((smallEigParams nmax S δ φ c₁ c₂).getD 6 0)) ∧
        ∃ (E V : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (d : Fin (n + 1 + 1) → ℂ),
          HoldsMatrix (L, 0) (M + E) μ.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
          (M + E) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂ ∧
          ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖) (3 * φ / 4) := by
  have hab : ∀ b k l, L ≤ b →
      Store.inBlock b k l ≤ Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L :=
    fun b k l hb _ _ hi => Or.inr (hi.1 ▸ hb)
  obtain ⟨_, _, hured, _⟩ := uSmallEig_spec (nmax := nmax) hb₁ hb₂ (by omega) hδ hδS hφ hφ1
  refine (((ginibrePerturb_pwrites (O := O) (Q := Q) hS hM hL hSmp hG hA hB hb₁ hb₂
    hδ hδS hφ hφ1 (hu.trans hured) hn hMS (a := (L, 0)) (q := q)).in_frame hd ha
    fun μ h z hz => h.2.2.1 z (by simp at hz ⊢; tauto)).mono_eqOff
    (fun μ ⟨⟨h, _⟩, hW⟩ => ⟨hW, h.2.2.2.2.2.2.2.2.1, h.live _ (by simp),
      Fp.disj_inBlock_of_ne (by have := h.2.2.2.2.2.1; omega)⟩)
    (fun μ μ' ⟨⟨h, hTh⟩, _⟩ hfr hpost => ⟨⟨h.of_eqOff hfr (hab _ _ _ le_rfl) hwo hqo,
      hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_ne (by omega)) hTh⟩,
      hpost⟩)).mono (fun _ h => h) (hab _ _ _ le_rfl) (fun _ h => h) le_rfl

omit [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O] [Has IdxTst Q] in
/-- The reduction step of `NLAlib.SmallEig.smallEigProg`: on a scalar machine with the standard
model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, $M.\mathrm{lit}(0) = 0$ and exact
comparisons, tail records with $b_1, b_2 > 0$, $n + 2 \le n_{\max}$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $\|\mathbf{M}\|_2 \le \Sigma$: from the scratch memory
(`NLAlib.SmallEig.SmallEigScratch`) with the threshold word copied and the perturbed matrix
$\mathbf{M} + \mathbf{E}$ of the class of `NLAlib.SmallEig.ginibrePerturb_pwrites` at `(L, 0)`, the
Hessenberg reduction writes only above $L$ and, on every tape, leaves a memory set up for the core
with a matrix in its class (`NLAlib.SmallEig.SmallEigCoreClass`). -/
theorem smallEigProg_reduce_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hzero : Mch.lit 0 = 0) (hC : IsCmp id I)
    {law : ℕ → Measure ℝ} {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax n : ℕ}
    (hn : n + 1 + 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {M : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ}
    (hMS : specNorm M ≤ S) {L : ℕ} {w q o : ℕ × ℕ}
    (hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1 + 1) * (n + 1 + 1))))
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1))))
    (hqo : Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)))) {ρ : Env} {ds : List IExp}
    {args : List Operand} (hd : IExp.evalList ρ.idx ds = some [n + 1 + 1])
    (ha : Operand.evalList ρ args = some [(L, 0), (L, 0)]) :
    PWrites law I (.frame ds args (hessenbergReduceLast (O := O) (Q := Q)).body) ρ
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L)
      (fun μ => (SmallEigScratch n L (smallEigParams nmax S δ φ c₁ c₂) w q o M μ ∧
        μ.store.get (L + 2) 0 = some ((smallEigParams nmax S δ φ c₁ c₂).getD 6 0)) ∧
        ∃ (E V : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (d : Fin (n + 1 + 1) → ℂ),
          HoldsMatrix (L, 0) (M + E) μ.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
          (M + E) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂ ∧
          ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖)
      (fun μ => ∃ x : {H // SmallEigCoreClass nmax S δ φ c₁ c₂ M H},
        SmallEigCoreInput (smallEigParams nmax S δ φ c₁ c₂) (L, 0) (L + 2, 0) q o (L + 1, 0) x.1
          μ ∧ HoldsMatrix w M μ.store) 0 := by
  have hab : ∀ b k l, L ≤ b →
      Store.inBlock b k l ≤ Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L :=
    fun b k l hb _ _ hi => Or.inr (hi.1 ▸ hb)
  have hq12 : 12 ≤ (smallEigParams nmax S δ φ c₁ c₂).length := by simp [smallEigParams]
  refine PWrites.of_writes le_rfl
    fun μ τ ⟨⟨h, hTh⟩, E, V, d, hW, hE, hV, hAV, hκ, hgap⟩ => ?_
  refine ((hessenbergReduceLast_writes_word hS hC (τ := τ) (a := (L, 0))
    (h.live _ (by simp)) hW).in_frame hd ha (h.live _ (by simp))).mono (hab _ _ _ le_rfl)
    fun μ' hfr ⟨_, hH⟩ => ?_
  obtain ⟨hl', hW', hF', hT', _, hqL, hoL, hroom', hq', hM'⟩ :=
    h.of_eqOff hfr (hab _ _ _ le_rfl) hwo hqo
  exact ⟨⟨_, smallEigCoreClass_hessenbergReduceLastWord hM hzero hb₁ hb₂ hn hδ hδS hφ hφ1 hu
    hMS hE hV hAV hκ hgap⟩, smallEigCoreInput_of_scratch hqL hoL hl' hW' hF' hT' hroom' hq12
    hqo hH (hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_ne (by omega)) hTh) hq',
    hM'⟩

/-- The last step of `NLAlib.SmallEig.smallEigProg`: on a scalar machine with the standard
model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, index literals, exact natural
literals up to $n + 2 \le n_{\max}$, exact comparisons and conversion, a measurable interpretation
reading the tape only in its windows whose draws store the tape entry, a Gaussian stream `sG` and
an exact polar sampler on a uniform stream `sU`, tail records with $b_1, b_2 > 0$,
$0 < \delta \le \Sigma$ and $0 < \varphi \le 1$: from a memory whose work matrix at `(L, 0)` is
in the class of the core relative to $\mathbf{M}$ (`NLAlib.SmallEig.SmallEigCoreClass`), set up
for the core (`NLAlib.SmallEig.SmallEigCoreInput`) and still holding $\mathbf{M}$ at `w`, the call
of the core writes only the output and above $L$ and, except with probability at most
$\varphi/4$, lists the spectrum of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$: the backward errors $5\delta/8$ and $\delta/4$ add. -/
theorem smallEigProg_core_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) {n : ℕ}
    (hNat : IsExactNatLit id Mch (n + 1 + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : n + 1 + 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {M : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} {L : ℕ} {w q o : ℕ × ℕ} {ρ : Env}
    {ds : List IExp} {args : List Operand}
    (hd : IExp.evalList ρ.idx ds = some [n + 1 + 1, 1, (smallEigParams nmax S δ φ c₁ c₂).length,
      smallEigCap nmax S δ φ c₁ c₂, smallEigCap nmax S δ φ c₁ c₂])
    (ha : Operand.evalList ρ args = some [(L, 0), (L + 2, 0), q, o, (L + 1, 0)]) :
    PWrites law I (.frame ds args (smallEigCore (O := O) (Q := Q) sG).body) ρ
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L)
      (fun μ => ∃ x : {H // SmallEigCoreClass nmax S δ φ c₁ c₂ M H},
        SmallEigCoreInput (smallEigParams nmax S δ φ c₁ c₂) (L, 0) (L + 2, 0) q o (L + 1, 0) x.1
          μ ∧ HoldsMatrix w M μ.store)
      (SmallEigSpectrum o M δ) (φ / 4) := by
  have hab : ∀ b k l, L ≤ b →
      Store.inBlock b k l ≤ Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L :=
    fun b k l hb _ _ hi => Or.inr (hi.1 ▸ hb)
  refine PWrites.mono (F := Store.inBlock L 0 (2 * ((n + 1 + 1) * (n + 1 + 1))) ⊔
      Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Store.inBlock (L + 1) 0 1) ?_ (fun _ h => h)
    (sup_le (sup_le (hab _ _ _ le_rfl) le_sup_left) (hab _ _ _ (by omega))) (fun _ h => h) le_rfl
  refine PStep.mono (PWrites.pstep_of_forall hI hloc
    (F := Store.inBlock L 0 (2 * ((n + 1 + 1) * (n + 1 + 1))) ⊔
      Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Store.inBlock (L + 1) 0 1)
    (P := fun (x : {H // SmallEigCoreClass nmax S δ φ c₁ c₂ M H}) μ =>
      SmallEigCoreInput (smallEigParams nmax S δ φ c₁ c₂) (L, 0) (L + 2, 0) q o (L + 1, 0) x.1 μ ∧
        HoldsMatrix w M μ.store)
    (Q := fun x μ' => μ'.store.get (L + 1) 0 = some 0 ∧
      ∃ (roots : Fin (n + 1 + 1) → ℂ) (E : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
        specNorm E ≤ δ / 4 ∧ (x.1 + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))
    (fun x => ?_) (measurableSet_leafOutcome (n + 1 + 1) δ w o
      (Store.inBlock L 0 (2 * ((n + 1 + 1) * (n + 1 + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Store.inBlock (L + 1) 0 1)) ?_)
    (fun μ h => h) ?_ le_rfl
  · obtain ⟨hHess, ⟨V, d, hV, hHV, hκ, hgap⟩, hHS, -⟩ := x.2
    exact ((smallEigCore_pwrites (O := O) (Q := Q) hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG
      hb₁ hb₂ hδ hδS hφ hφ1 hu hn hHess hV hHV hκ hgap hHS (a := (L, 0)) (t := (L + 2, 0))
      (p := q) (out := o) (f := (L + 1, 0))).mono (fun μ h => h.1) le_rfl (fun _ h => h)
      le_rfl).in_frame hd ha fun μ h => h.1.1
  · rintro x μ μ' ⟨_, hWM⟩ hfr ⟨_, roots, E, hO, hE, hR⟩
    refine ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hO hj 0]; rfl, ?_⟩
    obtain ⟨-, -, -, hPUS⟩ := x.2
    obtain ⟨G, hG, hLG⟩ := (hPUS.add_right E).exists_isEigenvalueListing
      (isEigenvalueListing_of_charpoly_roots_eq_ofFn hR)
    refine ⟨G, hG.trans (by linarith), ?_⟩
    rw [← hWM.eq_storedMatrix, ← hO.eq_storedMatrix]
    exact hLG
  · rintro μ μ' ⟨x, _, hWM⟩ ⟨hfr, hsome, G, hG, hLG⟩
    refine ⟨hfr, fun i => storedMatrix o (n + 1 + 1) 1 μ'.store i 0, G, hG, ?_, ?_⟩
    · rwa [← hWM.eq_storedMatrix] at hLG
    · convert holdsMatrix_storedMatrix hsome using 2
      ext i j
      rw [Fin.fin_one_eq_zero j]
      rfl

/-- **The small-eigenvalue program as a probabilistic block** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1]): let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$), index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a
measurable interpretation reading the tape only in its windows, draws that store the tape entry,
a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it, and a stream $s_G$ with
the standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$; let $n + 1 \le n_{\max}$,
$\mathbf{M}$ of order $n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$. Then from a memory holding $\mathbf{M}$ and the words
(`NLAlib.SmallEig.SmallEigInput`), except with probability at most $\varphi$, the run of
`NLAlib.SmallEig.smallEigProg` writes only its output and lists the spectrum of
$\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$
(`NLAlib.SmallEig.SmallEigSpectrum`). The order $1$ is copied; otherwise the perturbation
(`NLAlib.SmallEig.ginibrePerturb_pwrites`, $3\varphi/4$), the reduction
(`NLAlib.SmallEig.smallEigProg_reduce_pwrites`) and the core
(`NLAlib.SmallEig.smallEigProg_core_pwrites`, $\varphi/4$) compose by `NLAlib.Ops.PWrites.seq`;
the backward errors $\delta/2 + \delta/8 + \delta/4$ add. -/
theorem smallEigProg_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (w q o : ℕ × ℕ) :
    PWrites law I (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1))) (SmallEigInput nmax S δ φ c₁ c₂ w q o M)
      (SmallEigSpectrum o M δ) φ := by
  obtain _ | n := n
  · refine PWrites.of_writes hφ.le fun μ τ ⟨hW, _, hl, hroom, hwo, _⟩ => ?_
    refine (smallEigProg_writes_of_le_one hS sG le_rfl hW hl hroom hwo).mono le_rfl
      fun μ' _ hO => ⟨fun i => M i i, 0, by rw [specNorm_zero]; exact hδ.le, by
        simpa using isEigenvalueListing_diag_of_le_one le_rfl M, hO⟩
  by_cases hwo : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1 + 1) * (n + 1 + 1))))
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)))
  swap
  · exact PWrites.of_writes hφ.le fun μ τ hin => absurd hin.2.2.2.2.1 hwo
  by_cases hqo : Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock o.1 o.2 (2 * (n + 1 + 1)))
  swap
  · exact PWrites.of_writes hφ.le fun μ τ hin => absurd hin.2.2.2.2.2 hqo
  have hzero : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hq12 : 12 ≤ (smallEigParams nmax S δ φ c₁ c₂).length := by simp [smallEigParams]
  set qs := smallEigParams nmax S δ φ c₁ c₂ with hqs
  unfold smallEigProg
  refine (PWrites.seq (F₁ := Store.inBlock o.1 o.2 (2 * (n + 1 + 1)))
    (Mid := SmallEigInput nmax S δ φ c₁ c₂ w q o M) (φ₁ := 0) hI hloc hφ.le
    (PWrites.ifPos (n := 2 - (n + 1 + 1)) rfl le_rfl (fun h => absurd h (by omega))
      fun _ _ h => h)
    (PWrites.ifPos (n := n + 1 + 1 - 1) rfl hφ.le (fun _ => ?_)
      fun h => absurd h (by omega))).mono (fun _ h => h) (sup_le le_rfl le_rfl) (fun _ h => h)
    (by simp)
  change PWrites law I (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 1, .const 1] _) _ _ _ _ _
  refine PWrites.allocs (ns := [2 * ((n + 1 + 1) * (n + 1 + 1)), 1, 1]) rfl
    (Pre₁ := fun L μ => SmallEigScratch n L qs w q o M μ) ?_ ?_ fun L => ?_
  · exact fun μ s₁ hin hlen hlens hBelow =>
      SmallEigScratch.of_alloc hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1 hlen hlens hBelow
  · rintro μ ⟨_, _, hl, _⟩ s s' p hBelow ⟨roots, E, hE, hLst, hO⟩
    exact ⟨roots, E, hE, hLst, hO.of_below hBelow (hl o (by simp))⟩
  have hab : ∀ b k l, L ≤ b →
      Store.inBlock b k l ≤ Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L :=
    fun b k l hb _ _ hi => Or.inr (hi.1 ▸ hb)
  set Fo := Store.inBlock o.1 o.2 (2 * (n + 1 + 1)) ⊔ Fp.above L with hFo
  set t₁ := smallEigGap nmax S δ φ c₁
  set t₂ := smallEigCond nmax S δ φ c₂
  refine (PWrites.seq (F₁ := Fo) (φ₁ := 0) (φ₂ := (0 + (0 + (3 * φ / 4 + (0 + φ / 4)))))
    (Mid := SmallEigScratch n L qs w q o M)
    hI hloc (by linarith) ?_
    (PWrites.seq (F₁ := Fo) (φ₁ := 0) (φ₂ := (0 + (3 * φ / 4 + (0 + φ / 4))))
      (Mid := fun μ => SmallEigScratch n L qs w q o M μ ∧
        μ.store.get (L + 2) 0 = some (qs.getD 6 0)) hI hloc (by linarith) ?_
    (PWrites.seq (F₁ := Fo) (φ₁ := 0) (φ₂ := (3 * φ / 4 + (0 + φ / 4)))
      (Mid := fun μ => (SmallEigScratch n L qs w q o M μ ∧
        μ.store.get (L + 2) 0 = some (qs.getD 6 0)) ∧ HoldsMatrix (L, 0) M μ.store)
      hI hloc (by linarith) ?_
    (PWrites.seq (F₁ := Fo) (φ₁ := 3 * φ / 4) (φ₂ := (0 + φ / 4))
      (Mid := fun μ => (SmallEigScratch n L qs w q o M μ ∧
        μ.store.get (L + 2) 0 = some (qs.getD 6 0)) ∧
        ∃ (E V : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (d : Fin (n + 1 + 1) → ℂ),
          HoldsMatrix (L, 0) (M + E) μ.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
          (M + E) * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ 2 / t₂ ∧
          ∀ i j, i ≠ j → t₁ / 2 ≤ ‖d i - d j‖) hI hloc (by linarith) ?_
    (PWrites.seq (F₁ := Fo) (F₂ := Fo) (φ₁ := 0) (φ₂ := φ / 4)
      (Mid := fun μ => ∃ x : {H // SmallEigCoreClass nmax S δ φ c₁ c₂ M H},
        SmallEigCoreInput qs (L, 0) (L + 2, 0) q o (L + 1, 0) x.1 μ ∧
          HoldsMatrix w M μ.store) hI hloc (by linarith) ?_ ?_))))).mono (fun _ h => h)
    (by simp [hFo]) (fun _ h => h) (le_of_eq (by ring))
  · -- zero the output
    refine PWrites.of_writes le_rfl fun μ τ h => ?_
    exact ((writes_fillMap_readBlock (hS (.lit 0)) (τ := τ) (m := μ) (y := o)
      h.2.2.2.2.2.2.2.1).in_frame rfl rfl (h.live _ (by simp))).mono le_sup_left
      fun μ' hfr _ => h.of_eqOff hfr le_sup_left hwo hqo
  · -- copy the threshold word
    refine PWrites.of_writes le_rfl fun μ τ h => ?_
    have hq6 := Store.get_of_readBlock h.2.2.2.2.2.2.2.2.1 (j := 6) (by omega) 0
    have hT := h.2.2.2.1
    exact (writes_call_un (hS .copy) (x := (q.1, q.2 + 6)) (z := (L + 2, 0)) rfl rfl trivial hq6
      rfl (by simp only at hT ⊢; omega)).mono (hab _ _ _ (by omega))
      fun μ' hfr ⟨_, hTh⟩ => ⟨h.of_eqOff hfr (hab _ _ _ (by omega)) hwo hqo, hTh⟩
  · exact smallEigProg_copy_pwrites hS hwo hqo rfl rfl
  · exact smallEigProg_perturb_pwrites hS hM hL hSmp hG hA hB hb₁ hb₂ hn hδ hδS hφ hφ1 hu
      hMS hwo hqo rfl rfl
  · exact smallEigProg_reduce_pwrites hS hM hzero hC hb₁ hb₂ hn hδ hδS hφ hφ1 hu hMS hwo hqo rfl
      rfl
  · exact smallEigProg_core_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hb₁ hb₂ hn hδ hδS
      hφ hφ1 hu rfl rfl

/-- **The backward listing at $\delta_b$ is a forward one at $\beta$**
([BanksGarzaVargasSrivastava2025, Corollary 1.3], the matching): for $\mathbf{M}$ of order
$n + 1 \le k_{\max}$ with $\|\mathbf{M}\|_2 \le \Sigma$ and $0 < \beta \le \Sigma$, an output
listing the spectrum of $\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta_b$
(`NLAlib.SmallEig.forwardBackwardError`) is within $\beta$ of a listing of the spectrum of
$\mathbf{M}$, by the Ostrowski–Elsner matching
(`NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`) and
`NLAlib.SmallEig.forwardBackwardError_spec`. -/
theorem smallEigSpectrum_forward {kmax n : ℕ} (hn : n + 1 ≤ kmax) {S β : ℝ} (hβ : 0 < β)
    (hβS : β ≤ S) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S)
    {o : ℕ × ℕ} {μ' : Mem ℝ} (h : SmallEigSpectrum o M (forwardBackwardError kmax S β) μ') :
    ∃ roots ev : Fin (n + 1) → ℂ, IsEigenvalueListing M ev ∧ (∀ i, ‖roots i - ev i‖ ≤ β) ∧
      HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store := by
  obtain ⟨roots, E, hE, hL, hO⟩ := h
  obtain ⟨-, hbS, h2⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  obtain ⟨ev, hev, hb⟩ := exists_isEigenvalueListing_norm_sub_le_rpow (A' := M) hL
  refine ⟨roots, ev, hev, fun i => ?_, hO⟩
  rw [norm_sub_rev]
  refine (hb i).trans (le_trans ?_ (h2 n hn))
  have hα : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hE' : specNorm (M - (M + E)) = specNorm E := by rw [sub_add_cancel_left, specNorm_neg]
  have hsum : specNorm (M + E) + specNorm M ≤ 3 * S := by
    linarith [specNorm_add_le M E]
  have h0 : 0 ≤ specNorm (M + E) + specNorm M := by positivity
  rw [hE']
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hsum hα) (by positivity))
    (Real.rpow_le_rpow (specNorm_nonneg _) hE (by positivity)) (by positivity)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))

/-- **The small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], corrected:
$\Sigma$ an input, the base case of order $1$, every loop capped, the error absolute). Let the
machine have the standard model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a measurable
interpretation reading the tape only in its windows, draws that store the tape entry, a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it, and a stream $s_G$ with the
standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$. Let $n + 1 \le n_{\max}$,
$\mathbf{M}$ of order $n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$. Then from a memory holding $\mathbf{M}$ and the words of
`NLAlib.SmallEig.smallEigParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \operatorname{spec}(\mathbf{M} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr]
  \le \varphi\,.$$
Here $\boldsymbol{u}_{\mathrm{SmallEig}}$ is `NLAlib.SmallEig.uSmallEig` at $n_{\max}$.
[BanksGarzaVargasSrivastava2025, Theorem 1.1]; there $\Sigma$ is not an input (its errata P9,
N4) and the error is relative.

Note: The run terminates on every tape (`NLAlib.SmallEig.smallEigProg_terminates`). The failure
is split in four: the gap, the condition, the norm of the perturbation, and the worklist. -/
theorem smallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1))) (SmallEigSpectrum o M δ) μ} ≤ φ :=
  (smallEigProg_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS hδ hδS hφ
    hφ1 hu w q o).measureReal_not_writes_le hin hξ

/-- **The small-eigenvalue solver, relative form** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], as printed: the error relative to $\|\mathbf{M}\|_2$). With the hypotheses on the
machine, the streams and the tails of `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`
written out below: let $n + 1 \le n_{\max}$, $\mathbf{M}$ of order $n + 1$, $c \ge 1$ and
$\Sigma > 0$ with $\|\mathbf{M}\|_2 \le \Sigma \le c\|\mathbf{M}\|_2$, $0 < \varepsilon \le 1$,
$0 < \varphi \le 1$, and $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ at the absolute
error $\varepsilon\Sigma/c$. Then from a memory holding $\mathbf{M}$ and the words at
$\delta = \varepsilon\Sigma/c$,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \operatorname{spec}(\mathbf{M} + \mathbf{E}),\
  \|\mathbf{E}\|_2 \le \varepsilon\|\mathbf{M}\|_2\bigr] \le \varphi\,.$$
[BanksGarzaVargasSrivastava2025, Theorem 1.1]; the bound $\Sigma$ of the norm is an input there
too (its errata P9, N4). -/
theorem smallEig_relative {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S c ε φ : ℝ} (hS0 : 0 < S) (hMS : specNorm M ≤ S)
    (hc : 1 ≤ c) (hSM : S ≤ c * specNorm M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S (ε * S / c) φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S (ε * S / c) φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S (ε * S / c) φ c₁ c₂) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1))) (SmallEigSpectrum o M (ε * specNorm M)) μ} ≤ φ := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < ε * S / c := by positivity
  have hδS : ε * S / c ≤ S := by
    rw [div_le_iff₀ hc0]; nlinarith
  have hδM : ε * S / c ≤ ε * specNorm M := by
    rw [div_le_iff₀ hc0]; nlinarith [mul_le_mul_of_nonneg_left hSM hε.le]
  exact ((smallEigProg_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS
    hδ hδS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
    (fun _ ⟨roots, E, hE, hLst, hO⟩ => ⟨roots, E, hE.trans hδM, hLst, hO⟩)
    le_rfl).measureReal_not_writes_le hin hξ

/-- **The small-eigenvalue solver as a forward routine** ([BanksGarzaVargasSrivastava2025,
Corollary 1.3]): on a machine with the standard model at
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$, index literals, exact
natural literals up to $k'_{\max} \le k_{\max}$, exact `toNat` and comparisons, a measurable
interpretation
reading the tape only in its windows, draws that store the tape entry, a stream $s_U$ uniform on
$[0, 1]$ with an exact polar disk sampler and a stream $s_G$ with the standard real Gaussian law,
with the tails $c_1$, $c_2$ ($b_1, b_2 > 0$), $0 < \beta \le \Sigma$ and $0 < \varphi \le 1$:
`NLAlib.SmallEig.smallEigProg` with the words `NLAlib.SmallEig.smallEigForwardParams` and the cap
`NLAlib.SmallEig.smallEigForwardCap` meets `NLAlib.ShiftedQR.RandomSmallEigContract` with the
forward error $\beta$ and the failure probability $\varphi$ on orders at most $k'_{\max}$ and norms
at most $\Sigma$: one list of words, chosen at $k_{\max}$, serves every order. Here
$\boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$ is `NLAlib.SmallEig.uSmallEigForward`.
[BanksGarzaVargasSrivastava2025, Corollary 1.3]; there the order is fixed and the words depend on
it. -/
theorem smallEigProg_randomSmallEigContract {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax kmax' : ℕ} (hk' : kmax' ≤ kmax) (hNat : IsExactNatLit id Mch kmax') (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) :
    RandomSmallEigContract law β φ kmax' (smallEigForwardCap kmax S β φ c₁ c₂) S
      (smallEigForwardParams kmax S β φ c₁ c₂) (smallEigProg (O := O) (Q := Q) sG) I := by
  intro d w q o B hd _ hBS
  obtain ⟨hb0, hbS, -⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  rcases d with _ | n
  · refine PWrites.of_writes hφ.le fun μ τ ⟨hW, _, hl, hroom, hwo, _⟩ => ?_
    exact (smallEigProg_writes_of_le_one hS sG (by omega) hW hl hroom hwo).mono le_rfl
      fun μ' _ hO => ⟨fun i => B i i, fun i => B i i, isEigenvalueListing_diag_of_le_one
        (by omega) B, fun i => by simp [hβ.le], hO⟩
  · exact (smallEigProg_pwrites hS hM hL (hNat.mono hd) hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁
      hb₂ (hd.trans hk') hBS hb0 hbS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
      (fun _ h => smallEigSpectrum_forward (hd.trans hk') hβ hβS hBS h) le_rfl

/-- **The forward error on one input** ([BanksGarzaVargasSrivastava2025, Corollary 1.3]): with the
hypotheses on the machine, the streams and the tails written out in
`NLAlib.SmallEig.smallEigProg_randomSmallEigContract` (standard model at
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$, exact literals up to
$k_{\max}$, a measurable tape-local interpretation, the uniform and Gaussian streams, the tails
with $b_1, b_2 > 0$): for $\mathbf{M}$ of order $n + 1 \le k_{\max}$ with
$\|\mathbf{M}\|_2 \le \Sigma$, $0 < \beta \le \Sigma$ and $0 < \varphi \le 1$, from a memory
holding $\mathbf{M}$ and the words `NLAlib.SmallEig.smallEigForwardParams`,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \boldsymbol{\mu} \text{ with } \lvert\mu_i - \lambda_i\rvert \le \beta\bigr]
  \le \varphi$$
for a listing $\boldsymbol{\lambda}$ of the eigenvalues of $\mathbf{M}$. -/
theorem smallEig_measureReal_not_forward_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax : ℕ} (hNat : IsExactNatLit id Mch kmax) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ kmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S) {w q o : ℕ × ℕ}
    {μ : Mem ℝ} (hin : SmallEigInput kmax S (forwardBackwardError kmax S β) φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n kmax S (forwardBackwardError kmax S β) φ c₁ c₂) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1)))
      (fun μ' => ∃ roots ev : Fin (n + 1) → ℂ, IsEigenvalueListing M ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) μ} ≤ φ := by
  obtain ⟨hb0, hbS, -⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  exact ((smallEigProg_pwrites hS hM hL (hNat.mono hn) hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁
    hb₂ hn hMS hb0 hbS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
    (fun _ h => smallEigSpectrum_forward hn hβ hβS hMS h) le_rfl).measureReal_not_writes_le hin hξ

/-- **The operation count of the small-eigenvalue program** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], running time, on every tape): there is an absolute constant $c$ such that the static
count (`NLAlib.Ops.stmtCost`) of `NLAlib.SmallEig.smallEigProg` at the order $n + 1$, $n_q$ words
and the cap $T$ has at most $c(n + 1)^4(T + 1)^2$ operations and tests. The count holds on every
tape: the loops are capped by $T$ ($m, t, m_2 \le T$, $q \le m$). The paper's count has the factor
$n$ in its last term (its erratum N5). The monomial bound of the tree
(`NLAlib.Ops.size_stmtCost_le_stmtWorkMono`) gives $c = 3473$; the certificate's
`NLAlib.SmallEig.smallEigWork` is larger because its instrumentation also counts the structural
instructions. -/
theorem smallEig_work_le (sG : ℕ) : ∃ c : ℕ, ∀ n nq T : ℕ,
    Count.size (stmtCost (smallEigProg (O := O) (Q := Q) sG).body [n + 1, nq, T]) ≤
      c * (n + 1) ^ 4 * (T + 1) ^ 2 := by
  refine ⟨3473, fun n nq T => ?_⟩
  have hw : stmtWorkMono (smallEigProg (O := O) (Q := Q) sG).body
      [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] = ⟨3473, [4, 0, 2]⟩ := by
    kernel_rfl
  have hσ : SlotsLe [n + 1, nq + 1, T + 1] [n + 1, nq, T]
      [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] := by
    simp [SlotsLe, WorkMono.eval]
  refine (size_stmtCost_le_stmtWorkMono (by simp) _ hσ).trans ?_
  rw [hw]
  simp [WorkMono.eval, mul_assoc]

/-! ### With the proved random-matrix tails -/

/-- The unconditional form of `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`
([BanksGarzaVargasSrivastava2025, Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapRecord` <!-- value ginibreGapRecord --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionRecord` <!-- value ginibreConditionRecord --> $(128e, 3, 2, 2)$. -/
theorem smallEig_measureReal_not_spectrum_le_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u
  : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ ginibreGapRecord ginibreConditionRecord)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ ginibreGapRecord
      ginibreConditionRecord w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ ginibreGapRecord
        ginibreConditionRecord) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1))) (SmallEigSpectrum o M δ) μ} ≤ φ := by
  apply smallEig_measureReal_not_spectrum_le
    (hA := boundsGinibreGap_ginibreGapRecord) (hB := boundsGinibreCondition_ginibreConditionRecord)
    (hb₁ := ginibreGapRecord_b_pos) (hb₂ := ginibreConditionRecord_b_pos) <;> assumption

/-- The unconditional form of `NLAlib.SmallEig.smallEig_relative` ([BanksGarzaVargasSrivastava2025,
Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails of a complex Ginibre perturbation
are proved, at the records `NLAlib.ginibreGapRecord` <!-- value ginibreGapRecord -->
$(10000e, 5, 1/2, 2)$ and `NLAlib.ginibreConditionRecord` <!-- value ginibreConditionRecord -->
$(128e, 3, 2, 2)$. -/
theorem smallEig_relative_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S c ε φ : ℝ} (hS0 : 0 < S) (hMS : specNorm M ≤ S)
    (hc : 1 ≤ c) (hSM : S ≤ c * specNorm M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S (ε * S / c) φ ginibreGapRecord
      ginibreConditionRecord)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S (ε * S / c) φ
      ginibreGapRecord ginibreConditionRecord w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S (ε * S / c) φ ginibreGapRecord
        ginibreConditionRecord) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1))) (SmallEigSpectrum o M (ε * specNorm M)) μ} ≤ φ := by
  apply smallEig_relative
    (hA := boundsGinibreGap_ginibreGapRecord) (hB := boundsGinibreCondition_ginibreConditionRecord)
    (hb₁ := ginibreGapRecord_b_pos) (hb₂ := ginibreConditionRecord_b_pos) <;> assumption

/-- The unconditional form of `NLAlib.SmallEig.smallEigProg_randomSmallEigContract`
([BanksGarzaVargasSrivastava2025, Corollary 1.3]): the eigenvalue-gap and eigenvector-condition
tails of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapRecord` <!-- value ginibreGapRecord --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionRecord` <!-- value ginibreConditionRecord --> $(128e, 3, 2, 2)$. -/
theorem smallEigProg_randomSmallEigContract_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u :
  ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax kmax' : ℕ} (hk' : kmax' ≤ kmax) (hNat : IsExactNatLit id Mch kmax') (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ ginibreGapRecord
      ginibreConditionRecord) :
    RandomSmallEigContract law β φ kmax' (smallEigForwardCap kmax S β φ
      ginibreGapRecord ginibreConditionRecord) S
      (smallEigForwardParams kmax S β φ ginibreGapRecord
        ginibreConditionRecord) (smallEigProg (O := O) (Q := Q) sG) I := by
  apply smallEigProg_randomSmallEigContract
    (hA := boundsGinibreGap_ginibreGapRecord) (hB := boundsGinibreCondition_ginibreConditionRecord)
    (hb₁ := ginibreGapRecord_b_pos) (hb₂ := ginibreConditionRecord_b_pos) <;> assumption

/-- The unconditional form of `NLAlib.SmallEig.smallEig_measureReal_not_forward_le`
([BanksGarzaVargasSrivastava2025, Corollary 1.3]): the eigenvalue-gap and eigenvector-condition
tails of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapRecord` <!-- value ginibreGapRecord --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionRecord` <!-- value ginibreConditionRecord --> $(128e, 3, 2, 2)$. -/
theorem smallEig_measureReal_not_forward_le_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u :
  ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax : ℕ} (hNat : IsExactNatLit id Mch kmax) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ ginibreGapRecord
      ginibreConditionRecord) {n : ℕ} (hn : n + 1 ≤ kmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S) {w q o : ℕ × ℕ}
    {μ : Mem ℝ} (hin : SmallEigInput kmax S (forwardBackwardError kmax S β) φ
      ginibreGapRecord ginibreConditionRecord w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n kmax S (forwardBackwardError kmax S β) φ
        ginibreGapRecord ginibreConditionRecord) [w, q, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1)))
      (fun μ' => ∃ roots ev : Fin (n + 1) → ℂ, IsEigenvalueListing M ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) μ} ≤ φ := by
  apply smallEig_measureReal_not_forward_le
    (hA := boundsGinibreGap_ginibreGapRecord) (hB := boundsGinibreCondition_ginibreConditionRecord)
    (hb₁ := ginibreGapRecord_b_pos) (hb₂ := ginibreConditionRecord_b_pos) <;> assumption

end NLAlib.SmallEig
