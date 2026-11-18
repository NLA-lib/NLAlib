/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRitz
public import NLAlib.Matrix.QRIteration.Ritz
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolve
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward
public import NLAlib.Eigensolvers.ShiftedQR.PairBlocks
public import NLAlib.Matrix.QRIteration.StableStepForward
public import NLAlib.Matrix.FinitePrecision.GivensLogSlots

/-!
# The trials of the rounded `Regularize`

When the perturbed approximate Ritz values of `Regularize` ([BanksGarzaVargasSrivastava2022,
§4.2]) are not optimal, the dichotomy (Theorem 4.1, with the constant $\tfrac12 k^{-1/(2k)}$
for the printed $(2k)^{-1/(2k)}$) gives one of them whose degree $k$ step decouples; the program
tries them in turn: a
rounded degree $k$ step with the shift repeated, on a copy, and the scan of its bottom $k$
subdiagonal entries. This file has the trials, the decision after `Optimal`, and the
mathematics that one trial succeeds.

## Main definitions

* `NLAlib.ShiftedQR.regularizeTrial`, `NLAlib.ShiftedQR.regularizeTrials`,
  `NLAlib.ShiftedQR.regularizeDecide`: the programs.

## Main results

* `NLAlib.exists_norm_subdiag_le_hessenbergPotential`: some bottom subdiagonal entry is at most
  the potential.
* `NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow`: a rounded step with a
  good shift decouples.
* `NLAlib.ShiftedQR.exists_forall_isStableQRChain_exists_norm_subdiag_le`: the dichotomy of
  `Regularize` with rounded steps.
* `NLAlib.ShiftedQR.regularizeTrials_writes`, `NLAlib.ShiftedQR.regularizeDecide_writes`: the
  trials and the decision on any scalar machine.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- Some bottom subdiagonal entry is at most the potential: for $1 \le k \le n$ one of the
last $k$ subdiagonal entries has $\lvert\mathbf{H}_{i+1,i}\rvert \le \psi_k(\mathbf{H})$, the
geometric mean of their moduli. -/
theorem exists_norm_subdiag_le_hessenbergPotential {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H i.succ i.castSucc‖ ≤ hessenbergPotential k H := by
  set S := Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)
  have hmem : (⟨n - k, by omega⟩ : Fin n) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hne : S.Nonempty := ⟨_, hmem⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ (fun i : Fin n => ‖H i.succ i.castSucc‖) hne
  have hcard : S.card = k := by
    rw [← Finset.card_map Fin.valEmbedding,
      show S.map Fin.valEmbedding = Finset.Ico (n - k) n by
        ext x
        simp only [S, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply, Finset.mem_Ico]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact ⟨by omega, i.isLt⟩
        · intro hx; exact ⟨⟨x, hx.2⟩, by simp only; omega, rfl⟩]
    simp only [Nat.card_Ico]; omega
  refine ⟨i0, (Finset.mem_filter.mp hi0).2, ?_⟩
  have hprod : ‖H i0.succ i0.castSucc‖ ^ k ≤ hessenbergPotential k H ^ k := by
    rw [hessenbergPotential_pow hk]
    calc ‖H i0.succ i0.castSucc‖ ^ k = ∏ _i ∈ S, ‖H i0.succ i0.castSucc‖ := by
          rw [Finset.prod_const, hcard]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hmin
  exact le_of_pow_le_pow_left₀ hk.ne' (hessenbergPotential_nonneg k H) hprod

/-- Optimality does not depend on the order of the shifts: the shift polynomial of a
permuted list is the same. -/
theorem isOptimalRitzValues_iff_of_perm {θ : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss ts : List ℂ} (h : ss.Perm ts) :
    IsOptimalRitzValues θ H ss ↔ IsOptimalRitzValues θ H ts := by
  have hp : shiftPoly ss = shiftPoly ts := (h.map _).prod_eq
  simp only [IsOptimalRitzValues, hp, h.length_eq]

/-- **A rounded step with a good shift decouples** ([BanksGarzaVargasSrivastava2022, proof of
Lemma 4.6]): let $\mathbf{H} \ne 0$ be upper Hessenberg, $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{e})$ with $\kappa(\mathbf{V}) \le B$,
$\|\mathbf{H}\|_2 \le \Sigma$, $1 \le k \le n$, $\omega > 0$, and $r$ a shift with
$\lvert r\rvert \le C\|\mathbf{H}\|_2$ ($C \ge 0$), at distance at least $d > 0$ from every
$e_i$, and $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - r)^{-k}\| \ge (2/\omega)^k$. If
$\widehat{\mathbf{H}}$ is the result of a backward-stable chain of $k$ steps with the shift $r$
and relative error $x \ge 0$,
$$x \le (16B)^{-1}\Bigl(\frac{d}{(2 + 2C)\Sigma}\Bigr)^k, \qquad
(66 + 2C)B\Sigma\Bigl(\frac{(2 + 2C)\Sigma}{d}\Bigr)^k\sqrt{n + 1}\,x \le \frac{\omega}{2},$$
then one of the last $k$ subdiagonal entries of $\widehat{\mathbf{H}}$ has modulus at most
$\omega$: the exact step has its potential at most $\omega/2$, and the computed step is within
$\omega/2$ of it up to a diagonal unitary similarity. -/
theorem IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow {x C B S d ω : ℝ} {k : ℕ}
    {H H' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {r : ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H (List.replicate k r) H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hd : 0 < d) (hω : 0 < ω) (hk : 0 < k) (hkn : k ≤ n) (hH0 : H ≠ 0)
    (hH : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hS : specNorm H ≤ S) (hr : ‖r‖ ≤ C * specNorm H)
    (hdist : ∀ i, d ≤ ‖e i - r‖)
    (hτ : (2 / ω) ^ k ≤ ‖WithLp.toLp 2
      ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖)
    (hxu : x ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) * x ≤ ω / 2) :
    ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω := by
  have hHp : 0 < specNorm H :=
    (specNorm_nonneg H).lt_of_ne fun h0 => hH0 (specNorm_eq_zero_iff.mp h0.symm)
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num)
    ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hS0 : 0 < S := hHp.trans_le hS
  have hne : ∀ i, e i ≠ r := fun i he => by
    have := hdist i; rw [he, sub_self, norm_zero] at this; linarith
  set X := multiShiftedQRStep H (List.replicate k r)
  -- the exact step has its potential at most `ω / 2`
  have hpot := hH.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le hk hkn
    (det_sub_smul_one_ne_zero_of_forall_ne hV hHV (fun i => hne i))
  rw [aeval_shiftPoly_replicate, ← Matrix.inv_pow'] at hτ
  have hψ : hessenbergPotential k X ≤ ω / 2 := by
    have h2 : 0 < (2 / ω) ^ k := by positivity
    have hle : hessenbergPotential k X ^ k * (2 / ω) ^ k ≤ 1 :=
      (mul_le_mul_of_nonneg_left hτ (pow_nonneg (hessenbergPotential_nonneg k X) k)).trans hpot
    have : hessenbergPotential k X ^ k ≤ (ω / 2) ^ k := by
      have h3 := (le_div_iff₀ h2).mpr hle
      rwa [one_div, ← inv_pow, inv_div] at h3
    exact le_of_pow_le_pow_left₀ hk.ne' (by positivity) this
  obtain ⟨i, hik, hi⟩ := exists_norm_subdiag_le_hessenbergPotential hk hkn X
  refine ⟨i, hik, ?_⟩
  -- the computed step is within `ω / 2` of the exact one, up to a diagonal unitary
  have hs : ∀ s ∈ List.replicate k r, ‖s‖ ≤ C * specNorm H := fun s hs => by
    rw [List.eq_of_mem_replicate hs]; exact hr
  have hdist' : ∀ s ∈ List.replicate k r, ∀ i, d ≤ ‖e i - s‖ := fun s hs i => by
    rw [List.eq_of_mem_replicate hs]; exact hdist i
  have hmono : (d / ((2 + 2 * C) * S)) ^ k ≤ (d / ((2 + 2 * C) * specNorm H)) ^ k := by
    gcongr
  obtain ⟨D, hD, hF⟩ := h.exists_frobNorm_conj_sub_le hx hC hd hH0 hH hV hHV hκ hs hdist'
    (by rw [List.length_replicate]; exact hxu.trans (by gcongr))
  rw [List.length_replicate] at hF
  have hF' : frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - X) ≤ ω / 2 := by
    refine hF.trans (le_trans ?_ hbound)
    gcongr
  have he := (norm_apply_le_frobNorm _ i.succ i.castSucc).trans hF'
  have hconj : ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D) i.succ i.castSucc =
      star (D i.succ) * H' i.succ i.castSucc * D i.castSucc := by
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hn : ‖((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D) i.succ i.castSucc‖ =
      ‖H' i.succ i.castSucc‖ := by
    rw [hconj, norm_mul, norm_mul, norm_star, hD, hD, one_mul, mul_one]
  rw [Matrix.sub_apply] at he
  have := norm_sub_norm_le (((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D) i.succ i.castSucc)
    (X i.succ i.castSucc)
  rw [hn] at this
  linarith

end NLAlib

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The pair `S` copied $k$ times into `SR`: the shifts of a degree $k$ step with one repeated
shift. The interface is `[k] (S) → (SR)`. -/
def replicatePair : Impl O Q := opsImpl% [k] (S) → (SR) {
  for l < k {
    run (unaryMap (Has.inj ScalarOp.copy)).body [2] (S, SR[2 * l])
  }
}

/-- The computation of one trial of `Regularize`: the degree $k$ rounded step with the shift `S`
repeated $k$ times on a copy `T` of `A` (`SR` the repeated shifts, `Ds` the diagonal outputs),
recording its rotations directly in slot $j$ of the slotted log `Lg` of slot width $w$, and the
scan of its bottom $k$ subdiagonal entries against the threshold word `Thr` into the registers
`Rg`. The interface is `[N, k, w, j] (A, S, Thr) → (T, SR, Ds, Rg, Lg)`. -/
def trialStep : Impl O Q := opsImpl% [N, k, w, j] (A, S, Thr) → (T, SR, Ds, Rg, Lg) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (A, T);
  run replicatePair.body [k] (S, SR);
  run multiStepStable.body [N, k, w, j] (T, SR, T, Ds, Lg);
  run bottomScan.body [N, k] (T, Thr, Rg)
}

/-- The acceptance of a trial: copy the step `T` back to `A`, set the search word `G` to $0$ and
the flag `Fl` to $1$, and validate the trial's slot $j$ of the log `Lg` (slot width $w$), so that
its recorded rotations become part of the log. The interface is `[N, w, j] (T) → (A, G, Fl, Lg)`.
-/
def trialAccept : Impl O Q := opsImpl% [N, w, j] (T) → (A, G, Fl, Lg) {
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (T, A);
  call (Has.inj (ScalarOp.lit 0)) [] () → (G);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Fl);
  run (slottedLogValidate (O := O) (Q := Q)).body [w, j] (Lg)
}

/-- **One trial of `Regularize`**, at the slot $j$ of the log: if the search word `G` is
positive, run `NLAlib.ShiftedQR.trialStep`; if its scan found a small entry (`Rg[3]` positive),
accept it (`NLAlib.ShiftedQR.trialAccept`, which validates the slot). A trial that is not run, or
not accepted, leaves its slot invalid. The interface is
`[N, k, w, j] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl, Lg)`. -/
def regularizeTrial : Impl O Q :=
  opsImpl% [N, k, w, j] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl, Lg) {
    if (Has.inj CmpTst.isPos) [] (G) {
      run trialStep.body [N, k, w, j] (A, S, Thr, T, SR, Ds, Rg, Lg);
      if (Has.inj CmpTst.isPos) [] (Rg[3]) {
        run trialAccept.body [N, w, j] (T, A, G, Fl, Lg)
      } else {
        skip
      }
    } else {
      skip
    }
  }

/-- The $k$ trials of `Regularize`, with the shifts `S[2t]` in turn, trial $t$ at the slot
$j_0 + t$ of the log. The interface is `[N, k, w, j0] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl, Lg)`.
-/
def regularizeTrials : Impl O Q :=
  opsImpl% [N, k, w, j0] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl, Lg) {
    for t < k {
      run regularizeTrial.body [N, k, w, j0 + t] (A, S[2 * t], Thr, T, SR, Ds, Rg, A, G, Fl, Lg)
    }
  }

/-- The decision of `Regularize`: `Optimal` of the $k$ shifts `S` with the word `C` into `G`; if
optimal, the flag `Fl` is $0$; otherwise `Fl` is $2$, `G` is $1$, and the trials run at the slots
$j_0, \dots, j_0 + k - 1$ of the log. The interface is
`[N, k, w, j0] (A, S, C, Thr, T, SR, Ds, Rg) → (A, G, Fl, Lg)`. -/
def regularizeDecide : Impl O Q :=
  opsImpl% [N, k, w, j0] (A, S, C, Thr, T, SR, Ds, Rg) → (A, G, Fl, Lg) {
    run optimalTest.body [N, k] (A, S, C, G);
    if (Has.inj CmpTst.isPos) [] (G) {
      call (Has.inj (ScalarOp.lit 0)) [] () → (Fl)
    } else {
      call (Has.inj (ScalarOp.lit 2)) [] () → (Fl);
      call (Has.inj (ScalarOp.lit 1)) [] () → (G);
      run regularizeTrials.body [N, k, w, j0] (A, S, Thr, T, SR, Ds, Rg, A, G, Fl, Lg)
    }
  }

end Program

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- `NLAlib.ShiftedQR.replicatePair` on any scalar machine stores the pair $r$ of `S` $k$ times
at `SR`, writing only `SR`. -/
theorem replicatePair_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} {sp sr : ℕ × ℕ} {r : ℂ}
    (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hsr : sr.2 + 2 * k ≤ m.store.len sr.1)
    (hd : Fp.Disj (Store.inBlock sp.1 sp.2 2) (Store.inBlock sr.1 sr.2 (2 * k))) :
    Writes .total I τ (replicatePair (O := O) (Q := Q)).body (Env.frame [k] [sp, sr])
      (Store.inBlock sr.1 sr.2 (2 * k))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock sr.1 sr.2 (2 * (List.replicate k r).length) =
          some ((List.replicate k r).flatMap fun z => [z.re, z.im])) m := by
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by norm_num) 0)
  unfold replicatePair
  refine (writes_loop (N := k) rfl (fun _ => Store.inBlock sr.1 sr.2 (2 * k))
    (fun _ _ => le_rfl) (fun l μ => μ.pos = m.pos ∧ μ.store.readBlock sr.1 sr.2 (2 * l) =
      some ((List.replicate l r).flatMap fun z => [z.re, z.im])) ⟨rfl, by simp⟩ ?_).mono
    le_rfl ?_
  · intro l hl μ hfr ⟨hp, hpre⟩
    have hsμ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hd.symm hs
    have hsub : Store.inBlock sr.1 (sr.2 + 2 * l) 2 ≤ Store.inBlock sr.1 sr.2 (2 * k) :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hc := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τ) (f := id) (x := sp)
      (y := (sr.1, sr.2 + 2 * l)) (hS .copy) (Or.inl (hd.mono le_rfl hsub)) hsμ
      (by rw [hfr.len_eq]; dsimp only; omega)
    refine (hc.in_frame rfl rfl ?_).mono hsub ?_
    · have h0 : sr.2 < m.store.len sr.1 := by omega
      simp [Mem.Live, hfr.length_eq, hsl, Store.lt_length_of_lt_len h0]
    rintro μ' hfr' ⟨hp', hnew⟩
    refine ⟨hp'.trans hp, ?_⟩
    have hold := hfr'.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_inBlock_of_le le_rfl).symm hpre
    rw [show 2 * (l + 1) = 2 * l + 2 by ring, List.replicate_succ', List.flatMap_append]
    exact Store.readBlock_add hold (by simpa using hnew)
  · rintro μ - ⟨hp, h⟩
    exact ⟨hp, by simpa using h⟩

omit [Has IdxTst Q] in
/-- The computation of one trial on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$, exact comparisons, index literals and exact natural literals
up to $n + 1$: from an upper Hessenberg $\mathbf{H}$ of order $n + 1$ at `A`, the shift $r$ at `S`
and the threshold word $t$ at `Thr`, `NLAlib.ShiftedQR.trialStep` writes only its four outputs
and its rotations in the pending slot of the log, and stores at `T` a backward-stable degree
$k$ step by the exact unitary of the entries, $\widehat{\mathbf{H}}$ with the shift $r$
repeated (relative error $300(n+1)^2\boldsymbol{u}$), upper Hessenberg, and in `Rg` the scan
of its bottom $k$ subdiagonal entries (`NLAlib.ShiftedQR.bottomScan_writes`). -/
theorem trialStep_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a sp thr t sr ds rg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {r : ℂ} {tv : ℝ} (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    {ns w : ℕ} {lg : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length < ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, sp, thr, t, sr, ds, rg], b.1 ≠ lg.1) :
    Writes .total I τ (trialStep (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, L.length] [a, sp, thr, t, sr, ds, rg, lg])
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => ∃ es : List GivensEntry, es.length = k * n ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w L es m'.store ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs
          (givensLog (n + 1) es) ∧
          IsUpperHessenberg H' ∧ HoldsMatrix t H' m'.store ∧
          ((m'.store.get rg.1 (rg.2 + 3) = some 1 ∧ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧
              (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
            (m'.store.get rg.1 (rg.2 + 3) = some 0 ∧ ∀ i : Fin n, n ≤ (i : ℕ) + k →
              tv < (1 + u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2))) m := by
  have hu0 := hM.roundoff_nonneg
  have hD : ∀ b ∈ [a, sp, thr, t, sr, ds, rg], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by norm_num) 0)
  have htl := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith)
  have hsrl := Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega)
  have hdsl := Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega)
  have hrgl := Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega)
  have hthl := Store.lt_length_of_get hthr
  unfold trialStep
  refine (copyMatrix_writes (τ := τ) hS hA hrt (hW.symm.mono (by fp_sub) (by fp_sub))).frame_seq_le
    rfl rfl (by simp [Mem.Live, hal, htl]) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hT₁⟩
  have hlog₁ := hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD t (by simp) _ _ _ _)
    hlog
  have hs₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hs
  have hthr₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr
  have hrep := replicatePair_writes (τ := τ) (sr := sr) hS hs₁ (by rw [hfr₁.len_eq]; exact hrsr)
    (hW.symm.mono (by fp_sub) (by fp_sub))
  refine hrep.frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁.length_eq, hsl, hsrl]) (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hSR₂⟩
  have hT₂ := hT₁.of_eqOff hfr₂ hts.symm
  have hlog₂ := hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (hD sr (by simp) _ _ _ _) hlog₁
  have hthr₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hW.mono (by fp_sub) (by fp_sub)) hthr₁
  have hl₂ : ∀ b, m₂.store.len b = m.store.len b := fun b => by rw [hfr₂.len_eq, hfr₁.len_eq]
  have hL₂ : m₂.store.length = m.store.length := by rw [hfr₂.length_eq, hfr₁.length_eq]
  have hms := multiStepStable_isStableQRChainBy (τ := τ) (m := m₂) (a := t) (s := sr) (ds := ds)
    (lg := lg) (ss := List.replicate k r) hS hM hu0 hC hL hNat hH hnu (Nat.le_succ n) hlog₂ hj
    (by rw [List.length_replicate]; exact hw)
    (by simp [Mem.Live, hL₂, htl, hsrl, hdsl, hlgL]) hT₂ hSR₂
    (by rw [hl₂, List.length_replicate]; exact hrds)
    (by simpa using hts) (by simpa using htd) (by simpa using hsd)
    (by
      rw [List.length_replicate]
      exact Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨(hD t (by simp) _ _ _ _).symm,
        (hD sr (by simp) _ _ _ _).symm⟩, (hD ds (by simp) _ _ _ _).symm⟩)
  rw [List.length_replicate] at hms
  refine hms.frame_seq_le rfl rfl (by simp [Mem.Live, hL₂, htl, hsrl, hdsl, hlgL]) (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, es, hes, hpl, hlog₃, H', Rs, hch, hH', hT₃, -⟩
  have hthr₃ := hfr₃.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hW.mono (by fp_sub) (by fp_sub),
      hW.mono (by fp_sub) (by fp_sub)⟩, (hD thr (by simp) _ _ _ _).symm⟩) hthr₂
  have hL₃ : m₃.store.length = m.store.length := by rw [hfr₃.length_eq, hL₂]
  have hb := bottomScan_writes (τ := τ) (m := m₃) (a := t) (t := thr) (r := rg) hS hM hu0 hu1
    hL hNat hC hk hT₃ hthr₃ (by simp [Mem.Live, hL₃, htl, hthl, hrgl])
    (by rw [hfr₃.len_eq, hl₂]; exact hrrg) hrg (hW.mono (by fp_sub) (by fp_sub))
  refine (hb.in_frame rfl rfl (by simp [Mem.Live, hL₃, htl, hthl, hrgl])).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hscan⟩
  refine ⟨es, hes, hpl, hfr₄.keep (readsOnly_holdsSlottedLog _ _ _ _ _)
    (hD rg (by simp) _ _ _ _) hlog₃, H', Rs, hch, hH', hT₃.of_eqOff hfr₄ hrg, ?_⟩
  rcases hscan with ⟨h1, i, hi, -, hle⟩ | h0
  · exact Or.inl ⟨h1, i, hi, hle⟩
  · exact Or.inr h0

omit [Has CmpTst Q] [Has IdxTst Q] in
/-- The acceptance of a trial on a scalar machine with the standard model and exact natural
literals up to $1$: `NLAlib.ShiftedQR.trialAccept` copies the matrix at `T` to `A`, stores $0$
in `G` and $1$ in `Fl`, closes the pending slot of the log as accepted, and writes only these. -/
theorem trialAccept_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hNat : IsExactNatLit id M 1) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ}
    {t a g f : ℕ × ℕ} {H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hT : HoldsMatrix t H' m.store) (hra : a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1)
    (hrg : g.2 < m.store.len g.1) (hrf : f.2 < m.store.len f.1)
    (hta : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hga : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hL : IsIndexLit M I) {ns w : ℕ} {lg : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    {P : List GivensEntry} (hlog : HoldsSlottedLog lg ns w L P m.store) (hj : L.length < ns)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [t, a, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (trialAccept (O := O) (Q := Q)).body
      (Env.frame [n + 1, w, L.length] [t, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => HoldsMatrix a H' m'.store ∧ m'.store.get g.1 g.2 = some 0 ∧
        m'.store.get f.1 f.2 = some 1 ∧ HoldsSlottedLog lg ns w (L ++ [some P]) [] m'.store) m := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 le_rfl
  have hD : ∀ b ∈ [t, a, g, f], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  have htl := Store.lt_length_of_get (Store.get_of_readBlock hT (j := 0) (by positivity) 0)
  have hal := Store.lt_length_of_lt_len (show a.2 < m.store.len a.1 by nlinarith)
  unfold trialAccept
  refine (copyMatrix_writes (τ := τ) hS hT hra hta).frame_seq_le rfl rfl
    (by simp [Mem.Live, htl, hal]) (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, hA₁⟩
  refine (writes_call_const (hS (.lit 0)) (z := g) rfl trivial
    (by rw [hfr₁.len_eq]; exact hrg)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨-, hG₂⟩
  refine (writes_call_const (hS (.lit 1)) (z := f) rfl trivial
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrf)).seq_le (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨-, hF₃⟩
  have hlog₃ : HoldsSlottedLog lg ns w L P m₃.store :=
    hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD f (by simp) _ _ _ _)
      (hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD g (by simp) _ _ _ _)
        (hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD a (by simp) _ _ _ _) hlog))
  have hL₃ : m₃.store.length = m.store.length := by
    rw [hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq]
  refine ((slottedLogValidate_writes_of_exactNat (τ := τ) hL (hNat.mono le_rfl) hlog₃ hj).in_frame
    rfl rfl (by simp [Mem.Live, hL₃, hlgL])).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨-, hlog₄⟩
  refine ⟨((hA₁.of_eqOff hfr₂ (hga.mono (by fp_sub) le_rfl)).of_eqOff hfr₃
    (hga.mono (by fp_sub) le_rfl)).of_eqOff hfr₄ (hD a (by simp) _ _ _ _).symm, ?_,
    ?_, hlog₄⟩
  · rw [hfr₄.keep (Store.readsOnly_get _ _ _) (hD g (by simp) _ _ _ _).symm
      (hfr₃.keep (Store.readsOnly_get _ _ _) hgf.symm hG₂), h0]
  · rw [hfr₄.keep (Store.readsOnly_get _ _ _) (hD f (by simp) _ _ _ _).symm hF₃, h1]

/-- The outcome of one trial of `Regularize` from the search word $g$, the flag word $f$ and
the matrix $\mathbf{H}$ at `a`, with the shift $r$ and the threshold $t$: either nothing visible
changed (and, if $g > 0$, the computed step had no small bottom entry), or $g > 0$ and a
decoupled step was accepted: `G` is $0$, `Fl` is $1$ and `a` holds a backward-stable degree $k$
step with a bottom entry passing the scan, by the exact unitary of the trial's entries. The
trial's slot of the log is closed: rejected in the first case, accepted in the second. -/
def TrialPost (u : ℝ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (r : ℂ)
    (tv gv fv : ℝ) (a g f lg : ℕ × ℕ) (ns w : ℕ) (L : List (Option (List GivensEntry)))
    (m' : Mem ℝ) : Prop :=
  (HoldsSlottedLog lg ns w (L ++ [none]) [] m'.store ∧ m'.store.get g.1 g.2 = some gv ∧
    m'.store.get f.1 f.2 = some fv ∧ HoldsMatrix a H m'.store ∧
    (0 < gv → ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs ∧
        ∀ i : Fin n, n ≤ (i : ℕ) + k → tv < (1 + u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2)) ∨
  (0 < gv ∧ m'.store.get g.1 g.2 = some 0 ∧ m'.store.get f.1 f.2 = some 1 ∧
    ∃ es : List GivensEntry, es.length = k * n ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
      HoldsSlottedLog lg ns w (L ++ [some es]) [] m'.store ∧
    ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k r) H' Rs
        (givensLog (n + 1) es) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv)

omit [Has IdxTst Q] in
/-- One trial of `Regularize` on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$, exact comparisons, index literals and exact natural literals
up to $n + 1$: `NLAlib.ShiftedQR.regularizeTrial` writes only the matrix `A`, the words `G`,
`Fl`, its scratch and the log, and ends in `NLAlib.ShiftedQR.TrialPost`. -/
theorem regularizeTrial_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a sp thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {r : ℂ} {tv gv fv : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store) (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hg : m.store.get g.1 g.2 = some gv)
    (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    {ns w : ℕ} {lg : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length < ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, sp, thr, t, sr, ds, rg, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeTrial (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, L.length] [a, sp, thr, t, sr, ds, rg, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (TrialPost u k H r tv gv fv a g f lg ns w L) m := by
  have hD : ∀ b ∈ [a, sp, thr, t, sr, ds, rg, g, f], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  unfold regularizeTrial
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := g) hg) ?_
  by_cases hgp : 0 < gv
  · rw [show decide (0 < id gv) = true by simpa using hgp, if_pos rfl]
    have hstep := trialStep_writes (τ := τ) hS hM hu1 hL hNat hC hk0 hk hH hnu hA hs hthr hrt hrsr
      hrds hrrg hW hts htd hsd hrg hlog hj hw hlgl
      (fun b hb => hlgb b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h | h | h | h | h <;> simp [h]))
    have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
    refine hstep.frame_seq_le rfl rfl (by
        simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq]
        refine ⟨hal, Store.lt_length_of_get (Store.get_of_readBlock hs (j := 0) (by norm_num) 0),
          Store.lt_length_of_get hthr,
          Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith),
          Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega),
          Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega),
          Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega), hlgL⟩) (by fp_sub) ?_
    rintro m₁ hfr₁ ⟨es, hes, hpl, hlog₁, H', Rs, hch, hH', hT₁, hscan⟩
    have hA₁ := hA.of_eqOff hfr₁ (Fp.disj_sup_left.mpr
      ⟨hW.mono le_rfl (by fp_sub), (hD a (by simp) _ _ _ _).symm⟩)
    have hGFl : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
        Store.inBlock rg.1 rg.2 5 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
        (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1) :=
      Fp.disj_sup_left.mpr ⟨hGF.symm.mono (by fp_sub) le_rfl, Fp.disj_sup_right.mpr
        ⟨(hD g (by simp) _ _ _ _).symm, (hD f (by simp) _ _ _ _).symm⟩⟩
    have hg₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGFl.mono le_rfl le_sup_left) hg
    have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hGFl.mono le_rfl le_sup_right) hf
    have hlgl₁ : m₁.Live [lg] := by simpa [Mem.Live, hfr₁.length_eq] using hlgL
    rcases hscan with ⟨hR1, hdec⟩ | ⟨hR0, hall⟩
    · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (rg.1, rg.2 + 3)) hR1) ?_
      rw [show decide (0 < id (1 : ℝ)) = true by simp, if_pos rfl]
      have hacc := trialAccept_writes (τ := τ) (a := a) (g := g) (f := f) hS hM
        (hNat.mono (by omega)) hT₁
        (by rw [hfr₁.len_eq]; exact Store.le_len_of_readBlock hA (by positivity))
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hg)
        (by rw [hfr₁.len_eq]; exact Store.lt_len_of_get hf)
        (hW.mono (by fp_sub) (by fp_sub)) (hGF.mono le_rfl (by fp_sub)) hgf hL hlog₁ hj hlgl₁
        (fun b hb => hlgb b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h | h <;> simp [h]))
      refine (hacc.in_frame rfl rfl (by
        simp [Mem.Live, hfr₁.length_eq, Store.lt_length_of_get hg, Store.lt_length_of_get hf, hal,
          Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith), hlgL])).mono
        (by fp_sub) ?_
      rintro m₂ - ⟨hA₂, hG₂, hF₂, hlog₂⟩
      exact Or.inr ⟨hgp, hG₂, hF₂, es, hes, hpl, hlog₂, H', Rs, hch, hH', hA₂, hdec⟩
    · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (rg.1, rg.2 + 3)) hR0) ?_
      rw [show decide (0 < id (0 : ℝ)) = false by simp, if_neg (by simp)]
      exact (Writes.skip (Or.inl ⟨hlog₁.reject hj, hg₁, hf₁, hA₁,
        fun _ => ⟨H', Rs, hch.isStableQRChain, hall⟩⟩)).mono bot_le fun _ _ h => h
  · rw [show decide (0 < id gv) = false by simpa using hgp, if_neg (by simp)]
    exact (Writes.skip (Or.inl ⟨hlog.reject hj, hg, hf, hA, fun h => absurd h hgp⟩)).mono bot_le
      fun _ _ h => h

/-- The trials of `Regularize` after an accepted one, $l$ trials in: `G` is $0$, `Fl` is $1$, the
$l$ closed trial slots `Ls` after `L` hold one accepted slot `es` (planes below $n$), and `a` holds
the accepted step, by the exact unitary of `es`, with a bottom entry passing the scan. -/
abbrev TrialsDone (u : ℝ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (zs : Fin k → ℂ) (tv : ℝ) (a g f lg : ℕ × ℕ) (ns w : ℕ)
    (L : List (Option (List GivensEntry))) (l : ℕ) (μ : Mem ℝ) : Prop :=
  μ.store.get g.1 g.2 = some 0 ∧
    μ.store.get f.1 f.2 = some 1 ∧ ∃ (j : Fin k) (Ls : List (Option (List GivensEntry)))
      (es : List GivensEntry), Ls.length = l ∧ (∀ e ∈ es, e.1 + 1 < n + 1) ∧
      HoldsSlottedLog lg ns w (L ++ Ls) [] μ.store ∧ slotEntries w Ls = padEntries w es ∧
      ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
      IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs
        (givensLog (n + 1) es) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix a H' μ.store ∧
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv

omit [Has IdxTst Q] in
/-- The trials of `Regularize` on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$, exact comparisons, index literals and exact natural literals
up to $n + 1$: from an upper Hessenberg $\mathbf{H}$ at `A`, $k \ge 1$ shifts $z_j$ stored as
pairs at `S`, the threshold word $t$ at `Thr`, the search word $1$ at `G`, and a shift $z_{j_0}$
every backward-stable degree $k$ step of which has a bottom subdiagonal entry of modulus at most
$\omega$, $(1 + \boldsymbol{u})^2\omega^2 \le t$, `NLAlib.ShiftedQR.regularizeTrials` sets the
flag to $1$ and stores at `A` an accepted step: a backward-stable degree $k$ step with some
shift $z_j$ repeated, upper Hessenberg, with a bottom entry passing the scan; the trials close the
slots $j_0, \dots, j_0 + k - 1$ of the log, the accepted one valid, and the step is by the exact
unitary of its entries. -/
theorem regularizeTrials_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a s thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {zs : Fin k → ℂ} {tv fv ω : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hA : HoldsMatrix a H m.store)
    (hs : ∀ j : Fin k, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(zs j).re, (zs j).im])
    (hthr : m.store.get thr.1 thr.2 = some tv) (hg : m.store.get g.1 g.2 = some 1)
    (hf : m.store.get f.1 f.2 = some fv)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (jstar : Fin k) (hgood : ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
      IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs jstar)) H' Rs →
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, s, thr, t, sr, ds, rg, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, L.length] [a, s, thr, t, sr, ds, rg, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => m'.store.get f.1 f.2 = some 1 ∧
        ∃ (j : Fin k) (Ls : List (Option (List GivensEntry)))
        (es : List GivensEntry), Ls.length = k ∧ (∀ e ∈ slotEntries w Ls, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns w (L ++ Ls) [] m'.store ∧ slotEntries w Ls = padEntries w es ∧
        ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs
          (givensLog (n + 1) es) ∧
          IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
          ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) m := by
  set F := Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
    Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))
  have hFS : Fp.Disj F (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hAS, hW.mono le_rfl (by fp_sub)⟩,
      Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne (hlgb s (by simp)).symm,
        Fp.disj_inBlock_of_ne (hlgb thr (by simp)).symm⟩⟩
  have hpair : ∀ j : Fin k, Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    fun j => Fp.inBlock_le_inBlock (by omega) (by omega)
  let Done := TrialsDone u k H zs tv a g f lg ns w L
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  have hLive : ∀ (j : ℕ) (μ : Mem ℝ), μ.store.length = m.store.length →
      μ.Live [a, (s.1, s.2 + 2 * j), thr, t, sr, ds, rg, a, g, f, lg] := by
    intro j μ hμ
    have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
    have hsl := Store.lt_length_of_get (Store.get_of_readBlock (hs ⟨0, hk0⟩) (j := 0)
      (by norm_num) 0)
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hμ]
    exact ⟨hal, hsl, Store.lt_length_of_get hthr,
      Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith),
      Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega),
      Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega),
      Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega), hal,
      Store.lt_length_of_get hg, Store.lt_length_of_get hf, hlgL⟩
  have hlgb' : ∀ j : ℕ, ∀ b ∈ [a, (s.1, s.2 + 2 * j), thr, t, sr, ds, rg, g, f], b.1 ≠ lg.1 :=
    fun j b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact hlgb s (by simp) | exact hlgb _ (by simp)
  unfold regularizeTrials
  refine (writes_loop (N := k) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun j μ => (μ.store.get g.1 g.2 = some 1 ∧ μ.store.get f.1 f.2 = some fv ∧
      HoldsMatrix a H μ.store ∧ j ≤ jstar ∧
      HoldsSlottedLog lg ns w (L ++ List.replicate j none) [] μ.store) ∨ Done j μ)
    (Or.inl ⟨hg, hf, hA, Nat.zero_le _, by simpa using hlog⟩) ?_).mono le_rfl ?_
  · intro j hj μ hfr hinv
    have hl : ∀ b, μ.store.len b = m.store.len b := fun b => hfr.len_eq b
    have hsj := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hFS.mono le_rfl
      ((hpair ⟨j, hj⟩).trans le_sup_left)) (hs ⟨j, hj⟩)
    have hthrμ := hfr.keep (Store.readsOnly_get _ _ _) (hFS.mono le_rfl le_sup_right) hthr
    have hlgμ : μ.Live [lg] := by simpa [Mem.Live, hfr.length_eq] using hlgL
    rcases hinv with ⟨hgμ, hfμ, hAμ, hjs, hlogμ⟩ | hdone
    · have htr := regularizeTrial_writes (τ := τ) (sp := (s.1, s.2 + 2 * j)) hS hM hu1 hL hNat hC
        hk0 hk hH hnu hAμ hsj hthrμ hgμ hfμ (by rw [hl]; exact hrt) (by rw [hl]; exact hrsr)
        (by rw [hl]; exact hrds) (by rw [hl]; exact hrrg)
        (hW.mono le_rfl (sup_le_sup_right (sup_le_sup_left (hpair ⟨j, hj⟩) _) _)) hts htd hsd hrg
        hGF hgf hlogμ (by simp; omega) hw hlgμ (hlgb' j)
      rw [List.length_append, List.length_replicate] at htr
      refine (htr.in_frame rfl rfl (hLive j μ hfr.length_eq)).mono le_rfl ?_
      rintro μ' - (⟨hlog', hg', hf', hA', hch⟩ |
        ⟨-, hg', hf', es, hes, hpl, hlog', H', Rs, hc, hH', hA', hdec⟩)
      · refine Or.inl ⟨hg', hf', hA', ?_, by
          rwa [List.replicate_succ', ← List.append_assoc]⟩
        by_contra hlt
        have hjeq : (⟨j, hj⟩ : Fin k) = jstar := Fin.ext (by simp at hlt ⊢; omega)
        obtain ⟨H', Rs, hc, hall⟩ := hch one_pos
        obtain ⟨i, hik, hi⟩ := hgood H' Rs (by rw [← hjeq]; exact hc)
        nlinarith [hall i hik, pow_le_pow_left₀ (norm_nonneg _) hi 2, sq_nonneg (1 + u)]
      · refine Or.inr ⟨hg', hf', ⟨j, hj⟩, List.replicate j none ++ [some es], es, by simp, hpl,
          by rwa [← List.append_assoc], ?_, H', Rs, hc, hH', hA', hdec⟩
        simp [slotEntries_append, slotEntries_replicate_none, slotEntries_some]
    · obtain ⟨hg0, hf1, j', Ls, es, hLs, hpl, hlogμ, hse, H', Rs, hc, hH', hA', hdec⟩ := hdone
      have htr := regularizeTrial_writes (τ := τ) (sp := (s.1, s.2 + 2 * j)) hS hM hu1 hL hNat hC
        hk0 hk hH' hnu hA' hsj hthrμ hg0 hf1 (by rw [hl]; exact hrt) (by rw [hl]; exact hrsr)
        (by rw [hl]; exact hrds) (by rw [hl]; exact hrrg)
        (hW.mono le_rfl (sup_le_sup_right (sup_le_sup_left (hpair ⟨j, hj⟩) _) _)) hts htd hsd hrg
        hGF hgf hlogμ (by simp; omega) hw hlgμ (hlgb' j)
      rw [List.length_append, hLs] at htr
      refine (htr.in_frame rfl rfl (hLive j μ hfr.length_eq)).mono le_rfl ?_
      rintro μ' - (⟨hlog', hg', hf', hA'', -⟩ | ⟨h0, -⟩)
      · refine Or.inr ⟨hg', hf', j', Ls ++ [none], es, by simp [hLs], hpl,
          by rwa [← List.append_assoc], ?_, H', Rs, hc, hH', hA'', hdec⟩
        rw [slotEntries_append, hse]
        simp [slotEntries]
      · exact absurd h0 (lt_irrefl 0)
  · rintro μ - (⟨-, -, -, hjs, -⟩ | ⟨-, hF, j, Ls, es, hLs, hpl, hlog', hse, hrest⟩)
    · exact absurd jstar.isLt (by omega)
    · exact ⟨hF, j, Ls, es, hLs, hse ▸ padEntries_planes (by omega) hpl, hlog', hse, hrest⟩

omit [Has IdxTst Q] in
/-- The decision of `Regularize` on a scalar machine with the standard model at
$\boldsymbol{u} \le 1$, exact comparisons, index literals and exact natural literals up to
$n + 1$: from an upper Hessenberg $\mathbf{H}$ at `A`, $1 \le k \le n$, the $k$ shifts $z_j$ at
`S` with $\lvert z_j\rvert \le C\|\mathbf{H}\|_2$, $\theta > 0$, $\psi_k(\mathbf{H}) > 0$, the
word $0.999\theta^k$ at `C`, the threshold word $t$ at `Thr`, the scratch and output views apart,
and the precision conditions $(n + 1)\boldsymbol{u} \le 1/2500$,
$10^5(n + 1 + k)^2\boldsymbol{u} \le 1$ and
$30000k(n + 1)^{3/2}\boldsymbol{u}((2 + 2C)\|\mathbf{H}\|_2)^k \le
(\theta\psi_k(\mathbf{H}))^k$, `NLAlib.ShiftedQR.regularizeDecide` either sets the flag to $0$,
leaves $\mathbf{H}$ at `A` and the shifts are $\theta$-optimal, or sets the flag to $1$ and stores
at `A` an accepted step (`NLAlib.ShiftedQR.regularizeTrials_writes`), given that, when the shifts
are not $0.998^{1/k}\theta$-optimal, some shift decouples every backward-stable step with it. The
trials use the slots $j_0, \dots, j_0 + k - 1$ of the log: on acceptance they are closed, the
accepted one valid, and the step is by the exact unitary of its entries; when optimal the log is
untouched. -/
theorem regularizeDecide_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a s c thr t sr ds rg g f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {zs : Fin k → ℂ} {tv ω θ C : ℝ}
    (hH : IsUpperHessenberg H) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hθ : 0 < θ)
    (hψ : 0 < hessenbergPotential k H) (hzs : ∀ j, ‖zs j‖ ≤ C * specNorm H)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * C) * specNorm H) ^ k ≤ (θ * hessenbergPotential k H) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hA : HoldsMatrix a H m.store)
    (hs : ∀ j : Fin k, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(zs j).re, (zs j).im])
    (hc : m.store.get c.1 c.2 = some (0.999 * θ ^ k))
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrg' : g.2 < m.store.len g.1)
    (hrf : f.2 < m.store.len f.1)
    (hrt : t.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len t.1)
    (hrsr : sr.2 + 2 * k ≤ m.store.len sr.1) (hrds : ds.2 + 2 * k ≤ m.store.len ds.1)
    (hrrg : rg.2 + 5 ≤ m.store.len rg.1)
    (hW : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
      Store.inBlock rg.1 rg.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1))
    (hts : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock sr.1 sr.2 (2 * k)))
    (htd : Fp.Disj (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * k)))
    (hsd : Fp.Disj (Store.inBlock sr.1 sr.2 (2 * k)) (Store.inBlock ds.1 ds.2 (2 * k)))
    (hrg : Fp.Disj (Store.inBlock rg.1 rg.2 5)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1)))))
    (hGF : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock sr.1 sr.2 (2 * k) ⊔
        Store.inBlock ds.1 ds.2 (2 * k) ⊔ Store.inBlock rg.1 rg.2 5 ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hgf : Fp.Disj (Store.inBlock g.1 g.2 1) (Store.inBlock f.1 f.2 1))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock c.1 c.2 1))
    (hdich : ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ) H (List.ofFn zs) →
      ∃ jstar : Fin k, ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs jstar)) H' Rs →
          ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    (hlog : HoldsSlottedLog lg ns w L [] m.store) (hj : L.length + k ≤ ns) (hw : k * n ≤ w)
    (hlgl : m.Live [lg]) (hlgb : ∀ b ∈ [a, s, c, thr, t, sr, ds, rg, g, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, L.length] [a, s, c, thr, t, sr, ds, rg, a, g, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock g.1 g.2 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock t.1 t.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock sr.1 sr.2 (2 * k) ⊔ Store.inBlock ds.1 ds.2 (2 * k) ⊔
          Store.inBlock rg.1 rg.2 5) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (m'.store.get f.1 f.2 = some 0 ∧ HoldsMatrix a H m'.store ∧
          HoldsSlottedLog lg ns w L [] m'.store ∧
          IsOptimalRitzValues θ H (List.ofFn zs)) ∨
        (m'.store.get f.1 f.2 = some 1 ∧ ∃ (j : Fin k) (Ls : List (Option (List GivensEntry)))
          (es : List GivensEntry), Ls.length = k ∧ (∀ e ∈ slotEntries w Ls, e.1 + 1 < n + 1) ∧
          HoldsSlottedLog lg ns w (L ++ Ls) [] m'.store ∧ slotEntries w Ls = padEntries w es ∧
          ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
          IsStableQRChainBy (300 * (n + 1) ^ 2 * u) H (List.replicate k (zs j)) H' Rs
            (givensLog (n + 1) es) ∧
            IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
            ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv)) m := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have hlen : (List.ofFn zs).length = k := List.length_ofFn
  have hsS : m.store.readBlock s.1 s.2 (2 * (List.ofFn zs).length) =
      some ((List.ofFn zs).flatMap fun z => [z.re, z.im]) :=
    readBlock_flatMap_pair_of_forall fun j hj => by
      have := hs ⟨j, by simpa using hj⟩
      simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlen ▸ hj] using this
  have hD : ∀ b ∈ [a, s, c, thr, t, sr, ds, rg, g, f], ∀ o k o' k',
      Fp.Disj (Store.inBlock b.1 o k) (Store.inBlock lg.1 o' k') :=
    fun b hb _ _ _ _ => Fp.disj_inBlock_of_ne (hlgb b hb)
  have hlgL : lg.1 < m.store.length := by simpa [Mem.Live] using hlgl
  have hal := Store.lt_length_of_get (Store.get_of_readBlock hA (j := 0) (by positivity) 0)
  have hsl := Store.lt_length_of_get (Store.get_of_readBlock (hs ⟨0, hk0⟩) (j := 0)
    (by norm_num) 0)
  have hgl := Store.lt_length_of_lt_len hrg'
  have hopt := optimalTest_writes (τ := τ) (ss := List.ofFn zs) (a := a) (s := s) (c := c)
    (f := g) hS hM (hNat.mono (by omega)) hC (by simp; omega) (by simp; omega) hθ
    (by simpa using hψ) (by simpa using fun j => hzs j) (by simpa using huo)
    (by simpa using huo1) hA hsS (by simpa using hc) hrg'
    (by simp [Mem.Live, hal, hsl, Store.lt_length_of_get hc, hgl])
    (by
      rw [hlen]
      exact Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hGF.mono le_sup_left le_sup_right,
        hAS.mono (by fp_sub) (by fp_sub)⟩, hAS.mono (by fp_sub) (by fp_sub)⟩)
  rw [hlen] at hopt
  unfold regularizeDecide
  refine hopt.frame_seq_le rfl rfl (by simp [Mem.Live, hal, hsl, Store.lt_length_of_get hc, hgl])
    (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨-, b, hb, hb01, hb1, hb0⟩
  have hA₁ := hA.of_eqOff hfr₁ (hGF.mono le_sup_left le_sup_right)
  have hlog₁ := hfr₁.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD g (by simp) _ _ _ _)
    hlog
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := g) hb) ?_
  rcases hb01 with rfl | rfl
  · rw [show decide (0 < id (0 : ℝ)) = false by simp, if_neg (by simp)]
    obtain ⟨jstar, hgood⟩ := hdich (hb0 rfl)
    refine (writes_call_const (hS (.lit 2)) (z := f) rfl trivial
      (by rw [hfr₁.len_eq]; exact hrf)).seq_le (by fp_sub) ?_
    rintro m₂ hfr₂ ⟨-, hF₂⟩
    refine (writes_call_const (hS (.lit 1)) (z := g) rfl trivial
      (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hrg')).seq_le (by fp_sub) ?_
    rintro m₃ hfr₃ ⟨-, hG₃⟩
    have hfr := (hfr₁.trans' hfr₂).trans' hfr₃
    have hl : ∀ b, m₃.store.len b = m.store.len b := fun b => by
      rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
    have hkeep : Fp.Disj (Store.inBlock g.1 g.2 1 ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock g.1 g.2 1) (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock thr.1 thr.2 1) :=
      hAS.mono (by fp_sub) (by fp_sub)
    have hs₃ : ∀ j : Fin k, m₃.store.readBlock s.1 (s.2 + 2 * j) 2 =
        some [(zs j).re, (zs j).im] := fun j => hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (hkeep.mono le_rfl ((Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_left))
      (hs j)
    have hthr₃ := hfr.keep (Store.readsOnly_get _ _ _) (hkeep.mono le_rfl le_sup_right) hthr
    have hA₃ := hA.of_eqOff hfr (hGF.mono (by fp_sub) le_sup_right)
    have hF₃ := hfr₃.keep (Store.readsOnly_get _ _ _) hgf hF₂
    have hlog₃ := hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD g (by simp) _ _ _ _)
      (hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD f (by simp) _ _ _ _) hlog₁)
    have htr := regularizeTrials_writes (τ := τ) hS hM hu1 hL hNat hC hk0 hk hH hnu hA₃ hs₃
      hthr₃ (by rw [hG₃, h1]) hF₃ (by rw [hl]; exact hrt) (by rw [hl]; exact hrsr)
      (by rw [hl]; exact hrds) (by rw [hl]; exact hrrg) hW hts htd hsd hrg hGF hgf
      (hAS.mono le_rfl (by fp_sub)) jstar hgood hthrω hlog₃ hj hw
      (by simpa [Mem.Live, hfr.length_eq] using hlgL)
      (fun b hb => hlgb b ((List.Sublist.refl _ |>.cons c |>.cons_cons s |>.cons_cons a).subset hb))
    refine (htr.in_frame rfl rfl ?_).mono (by fp_sub) fun _ _ h => Or.inr h
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hfr.length_eq]
    exact ⟨hal, hsl, Store.lt_length_of_get hthr,
      Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by nlinarith),
      Store.lt_length_of_lt_len (show sr.2 < m.store.len sr.1 by omega),
      Store.lt_length_of_lt_len (show ds.2 < m.store.len ds.1 by omega),
      Store.lt_length_of_lt_len (show rg.2 < m.store.len rg.1 by omega), hal, hgl,
      Store.lt_length_of_lt_len hrf, hlgL⟩
  · rw [show decide (0 < id (1 : ℝ)) = true by simp, if_pos rfl]
    refine (writes_call_const (hS (.lit 0)) (z := f) rfl trivial
      (by rw [hfr₁.len_eq]; exact hrf)).mono (by fp_sub) ?_
    rintro m₂ hfr₂ ⟨-, hF₂⟩
    exact Or.inl ⟨by rw [hF₂, h0], hA₁.of_eqOff hfr₂ (hGF.mono le_sup_right le_sup_right),
      hfr₂.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (hD f (by simp) _ _ _ _) hlog₁,
      hb1 rfl⟩

end Trials

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

/-- **The dichotomy of `Regularize`, with rounded steps** ([BanksGarzaVargasSrivastava2022,
proof of Lemma 4.6], corrected: the dichotomy constant is $\tfrac12 k^{-1/(2k)}$, the printed
$(2k)^{-1/(2k)}$ drops a factor $2$, and the proof's test is $\psi_k(\mathbf{H}) \ge
\varepsilon$ where the paper prints $\le$): let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$, $B^{2/k} \le 2$, $1 \le k \le n$, eigenvalues separated by
$2\omega^2/\Sigma$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, and
shifts $z_1, \dots, z_k$ within $\omega^2/(2020\Sigma)$ of a listing of the eigenvalues of the
trailing $k \times k$ block, with $\lvert z_j\rvert \le 1.1\|\mathbf{H}\|_2$ and at distance at
least $d > 0$ from every $e_i$. If the shifts are not $0.998^{1/k}\theta$-optimal,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, then some $z_{j_0}$ has the property that
every backward-stable chain of $k$ steps with the shift $z_{j_0}$ and relative error $x \ge 0$,
$$x \le (16B)^{-1}\Bigl(\frac{d}{4.2\Sigma}\Bigr)^k, \qquad
68.2B\Sigma\Bigl(\frac{4.2\Sigma}{d}\Bigr)^k\sqrt{n + 1}\,x \le \frac{\omega}{2},$$
ends in a matrix with a bottom subdiagonal entry of modulus at most $\omega$. -/
theorem exists_forall_isStableQRChain_exists_norm_subdiag_le {n k : ℕ} {B S ω d x : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {zs lam : Fin k → ℂ}
    (hH : IsUpperHessenberg H) (hk : 0 < k) (hkn : k ≤ n) (hBk : B ^ ((2 : ℝ) / k) ≤ 2)
    (hω : 0 < ω) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hκ : pseudoConditionNumber V ≤ B) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hS : specNorm H ≤ S) (hψ : ω ≤ hessenbergPotential k H)
    (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hzl : ∀ j, ‖zs j - lam j‖ ≤ ω ^ 2 / (20 * 101 * S))
    (hz : ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) (hd : 0 < d) (hdist : ∀ j i, d ≤ ‖e i - zs j‖)
    (hopt : ¬IsOptimalRitzValues ((0.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹))) H (List.ofFn zs))
    (hx : 0 ≤ x) (hxu : x ≤ (16 * B)⁻¹ * (d / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / d) ^ k * √(n + 1) * x ≤ ω / 2) :
    ∃ jstar : Fin k, ∀ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) Rs,
      IsStableQRChain x H (List.replicate k (zs jstar)) H' Rs →
        ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω := by
  have hB : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hψH := hessenbergPotential_le_specNorm hk hkn H
  have hH0 : H ≠ 0 := fun h0 => by
    rw [h0, specNorm_zero] at hψH
    rw [h0] at hψ
    linarith
  obtain ⟨ss, hperm, hss⟩ := exists_perm_forall₂_ritzValues hlam hzl
  have hne : ∀ r ∈ ss, ∀ i, e i ≠ r := by
    intro r hr i he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (hperm.subset hr)
    have := hdist j i
    rw [he, sub_self, norm_zero] at this
    linarith
  obtain ⟨r, hr, hτ⟩ := exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues hH hk hkn hB hBk hω
    hV hHV hκ hgap hS hψ hss hne (by rwa [isOptimalRitzValues_iff_of_perm hperm])
  obtain ⟨jstar, rfl⟩ := List.mem_ofFn.mp (hperm.subset hr)
  refine ⟨jstar, fun H' Rs hch => ?_⟩
  exact hch.exists_norm_subdiag_le_of_le_norm_inv_pow hx (by norm_num) hd hω hk hkn hH0 hH hV hHV
    hκ hS (hz jstar) (fun i => hdist jstar i) hτ hxu hbound

end NLAlib.ShiftedQR
