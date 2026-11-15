/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedExc
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRitz

/-!
# The rounded `Regularize`

`Regularize` ([BanksGarzaVargasSrivastava2022, §4.2], called $\mathsf{RitzOrDecouple}$ there)
computes forward-approximate Ritz values with `SmallEig`, perturbs each by an independent uniform
sample of a small disk, and tests the perturbed values with `Optimal`. If they are optimal it
returns them; otherwise the dichotomy
(`NLAlib.exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues`) gives one among them whose
degree $k$ step decouples, and the program tries them in turn. The random perturbation keeps
every shift away from the spectrum, which the forward error of the rounded steps needs.

## Main results

* `NLAlib.ShiftedQR.regularize_bad_window_le`: one perturbation comes within
  $\eta = R\sqrt{\varphi/(2k)}$ of an eigenvalue with probability at most $\varphi/(2k)$.
* `NLAlib.exists_norm_subdiag_le_hessenbergPotential`: some bottom subdiagonal entry is at most
  the potential.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Some bottom subdiagonal entry is at most the potential**: for $1 \le k \le n$ one of the
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

/-- **Optimality does not depend on the order of the shifts**: the shift polynomial of a
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
  have hne : ∀ i, e i ≠ r := fun i he => by have := hdist i; rw [he, sub_self, norm_zero] at this; linarith
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

/-- **The bad draws of one random shift regularization** ([BanksGarzaVargasSrivastava2022,
Lemma 3.10], one sample, as `Regularize` uses it): for a centre $c$, complex numbers
$\lambda_1, \dots, \lambda_N$ whose distinct values are at distance at least $4R$, $R > 0$,
$k \ge 1$ and $0 \le \varphi \le 1$, the window $x \in \mathbb{R}^2$ of two uniform draws on
$[0, 1]$ lies off the unit square or makes the polar sample $w$ of radius $R$ bring $c + w$
within $\eta = R\sqrt{\varphi/(2k)}$ of some $\lambda_i$ with probability at most
$\varphi/(2k)$. Over the $k$ draws of `Regularize` this is the paper's $\varphi/2$. -/
theorem regularize_bad_window_le (c : ℂ) {N : ℕ} (e : Fin N → ℂ) {k : ℕ} {R φ : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) :
    (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)).real
      {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
        ∃ i, ‖c + polarDisk 0 R x - e i‖ < R * √(φ / (2 * k))} ≤ φ / (2 * k) := by
  classical
  set η := R * √(φ / (2 * k)) with hη_def
  set Λ : Finset ℂ := Finset.univ.image e
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 ≤ φ / (2 * k) := by positivity
  have hq1 : φ / (2 * k) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hη0 : 0 ≤ η := by positivity
  have hηR : η ≤ R := mul_le_of_le_one_right hR.le (Real.sqrt_le_one.mpr hq1)
  have hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → 2 * (η + R) ≤ ‖a - b‖ := by
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    linarith [hsep i j hab]
  have hD3 := measureReal_exists_norm_add_sub_lt_le (fun _ : Fin 1 => c) Λ hR hη0 hΛ
  set U : Set ℂ := {w | ∃ a ∈ Λ, ‖c + w - a‖ < η}
  have hU : MeasurableSet U := by
    have : U = ⋃ a ∈ Λ, {w | ‖c + w - a‖ < η} := by ext; simp [U]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_lt (by fun_prop)
      measurable_const
  have h1 : (diskUniform 0 R).real U ≤ (η / R) ^ 2 := by
    have hmp := measurePreserving_funUnique (diskUniform 0 R) (Fin 1)
    rw [← hmp.measureReal_preimage hU.nullMeasurableSet]
    refine le_trans (le_of_eq ?_) (by simpa using hD3)
    congr 1
  set μ := Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Icc 0 1)
  set A : Set (Fin 2 → ℝ) := ⋃ j, (fun x : Fin 2 → ℝ => x j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ
  have hmeas : Measurable (polarDisk 0 R) := by unfold polarDisk; fun_prop
  have hset : {x : Fin 2 → ℝ | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ i, ‖c + polarDisk 0 R x - e i‖ < η} = A ∪ polarDisk 0 R ⁻¹' U := by
    ext x; simp [A, U, Λ]
  have hA0 : μ A = 0 := by
    refine measure_iUnion_null fun j => Measure.pi_eval_preimage_null _ ?_
    rw [Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self, measure_empty]
  rw [hset]
  calc μ.real (A ∪ polarDisk 0 R ⁻¹' U) ≤ μ.real A + μ.real (polarDisk 0 R ⁻¹' U) :=
        measureReal_union_le _ _
    _ = (diskUniform 0 R).real U := by
        rw [measureReal_def, hA0, ENNReal.toReal_zero, zero_add,
          ← map_measureReal_apply hmeas hU, map_polarDisk_eq_diskUniform 0 hR]
    _ ≤ (η / R) ^ 2 := h1
    _ = φ / (2 * k) := by rw [hη_def, mul_div_cancel_left₀ _ hR.ne', Real.sq_sqrt hq0]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

/-- A list of complex numbers stored as interleaved pairs, read pair by pair. -/
theorem readBlock_flatMap_pair_of_forall {s : Store ℝ} {b o : ℕ} {zs : List ℂ}
    (h : ∀ j < zs.length,
      s.readBlock b (o + 2 * j) 2 = some [(zs.getD j 0).re, (zs.getD j 0).im]) :
    s.readBlock b o (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]) := by
  induction zs generalizing o with
  | nil => simp
  | cons z zs ih =>
    have h0 := h 0 (by simp)
    have ht := ih (o := o + 2) fun j hj => by
      have := h (j + 1) (by simpa using hj)
      rwa [show o + 2 * (j + 1) = o + 2 + 2 * j by ring, List.getD_cons_succ] at this
    rw [List.length_cons, show 2 * (zs.length + 1) = 2 + 2 * zs.length by ring, List.flatMap_cons]
    exact Store.readBlock_add (by simpa using h0) ht

/-- A pair read from its two cells. -/
theorem readBlock_pair_of_get {s : Store ℝ} {b o : ℕ} {x y : ℝ} (hx : s.get b o = some x)
    (hy : s.get b (o + 1) = some y) : s.readBlock b o 2 = some [x, y] := by
  rw [Store.readBlock_eq_some_iff]
  refine ⟨rfl, fun j hj => ?_⟩
  have hj' : j < 2 := hj
  interval_cases j
  · simpa using hx
  · simpa using hy

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **One random perturbation of a shift**: a polar sample $w$ of the radius word `Rd` into the
pair `Z`, then the pair `S` becomes $\mathrm{fl}(S + w)$ componentwise. The interface is
`[] (Rd, S) → (Z, S)`. -/
def regularizeDraw : Impl O Q := opsImpl% [] (Rd, S) → (Z, S) {
  call (Has.inj DiskSampleOp.polar) [] (Rd) → (Z);
  call (Has.inj ScalarOp.add) [] (S, Z) → (S);
  call (Has.inj ScalarOp.add) [] (S[1], Z[1]) → (S[1])
}

/-- **The $k$ random perturbations**: `NLAlib.ShiftedQR.regularizeDraw` on each of the $k$ pairs
of `S`, with the radius word `Rd` and the scratch pair `Z`. The interface is
`[k] (Rd) → (Z, S)`. -/
def regularizeDraws : Impl O Q := opsImpl% [k] (Rd) → (Z, S) {
  for i < k {
    run regularizeDraw.body [] (Rd, S[2 * i], Z, S[2 * i])
  }
}

/-- The pair `S` copied $k$ times into `SR`: the shifts of a degree $k$ step with one repeated
shift. The interface is `[k] (S) → (SR)`. -/
def replicatePair : Impl O Q := opsImpl% [k] (S) → (SR) {
  for l < k {
    run (unaryMap (Has.inj ScalarOp.copy)).body [2] (S, SR[2 * l])
  }
}

/-- **One trial of `Regularize`**: if the search word `G` is positive, the degree $k$ rounded
step with the shift `S` repeated $k$ times is computed on a copy `T` of `A`, and its bottom $k$
subdiagonal entries are scanned against the threshold word `Thr`; if one passes, the step is
copied back to `A`, `G` is set to $0$ and the flag `Fl` to $1$. The interface is
`[N, k] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl)`. -/
def regularizeTrial : Impl O Q :=
  opsImpl% [N, k] (A, S, Thr, T, SR, Ds, Rg) → (A, G, Fl) {
    if (Has.inj CmpTst.isPos) [] (G) {
      run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (A, T);
      run replicatePair.body [k] (S, SR);
      run multiStepStable.body [N, k] (T, SR, T, Ds);
      run bottomScan.body [N, k] (T, Thr, Rg);
      if (Has.inj CmpTst.isPos) [] (Rg[3]) {
        run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (N * N)] (T, A);
        call (Has.inj (ScalarOp.lit 0)) [] () → (G);
        call (Has.inj (ScalarOp.lit 1)) [] () → (Fl)
      } else {
        skip
      }
    } else {
      skip
    }
  }

/-- `Regularize` with caller-owned scratch: the trailing $k \times k$ block of the order-$N$
matrix `A` into `B`, `SmallEig` of it into the $k$ pairs `S`, one random perturbation of each
pair (radius word `Rd`), `Optimal` with the word `C` into `G`; if optimal, the flag `Fl` is $0$;
otherwise `Fl` is $2$ and the $k$ trials run until one decouples (then `Fl` is $1$). The
interface is `[N, k] (A, Rd, C, Thr, B, Z, G, T, SR, Ds, Rg) → (A, S, Fl)`. -/
def regularizeWithScratch : Impl O Q :=
  opsImpl% [N, k] (A, Rd, C, Thr, B, Z, G, T, SR, Ds, Rg) → (A, S, Fl) {
    run copyToWork.body [N, N - k, k] (A, B);
    run smallEigLeaf.body [k] (B, S);
    run regularizeDraws.body [k] (Rd, Z, S);
    run optimalTest.body [N, k] (A, S, C, G);
    if (Has.inj CmpTst.isPos) [] (G) {
      call (Has.inj (ScalarOp.lit 0)) [] () → (Fl)
    } else {
      call (Has.inj (ScalarOp.lit 2)) [] () → (Fl);
      call (Has.inj (ScalarOp.lit 1)) [] () → (G);
      for j < k {
        run regularizeTrial.body [N, k] (A, S[2 * j], Thr, T, SR, Ds, Rg, A, G, Fl)
      }
    }
  }

/-- **`Regularize`** ([BanksGarzaVargasSrivastava2022, §4.2], $\mathsf{RitzOrDecouple}$): from
the order-$N$ matrix `A`, the radius word `Rd` of the perturbations, the word `C` of `Optimal`
($0.999\theta^k$) and the threshold word `Thr` of the decoupling scan, store $k$ perturbed
approximate Ritz values at `S` and set the flag `Fl` to $0$ (they are optimal, `A` unchanged) or
$1$ (`A` holds a decoupled degree $k$ step); `Fl` is $2$ only if no trial decoupled. All scratch is
scoped. The interface is `[N, k] (A, Rd, C, Thr) → (A, S, Fl)`. -/
def regularize : Impl O Q := opsImpl% [N, k] (A, Rd, C, Thr) → (A, S, Fl) {
  let B ← alloc (2 * (k * k));
  let Z ← alloc 2;
  let G ← alloc 1;
  let T ← alloc (2 * (N * N));
  let SR ← alloc (2 * k);
  let Ds ← alloc (2 * k);
  let Rg ← alloc 5;
  run regularizeWithScratch.body [N, k] (A, Rd, C, Thr, B, Z, G, T, SR, Ds, Rg, A, S, Fl)
}

end Program

section Proofs

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- **One random perturbation on any scalar machine** with an exact polar sampler on the stream
`s`: from the radius word $R$ at `Rd` and the pair $r$ at `S`, `NLAlib.ShiftedQR.regularizeDraw`
stores at `S` the rounded $\mathrm{fl}(r + w)$ (`NLAlib.ShiftedQR.excCentreWord`) of the polar
sample $w$ of radius $R$ read at the start position, writes only `S` and the scratch pair `Z`,
and advances the position by two. -/
theorem regularizeDraw_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {s : ℕ}
    (hD : IsPolarDiskSampler s I) {τ : Tape ℝ} {m : Mem ℝ} {rd sp z : ℕ × ℕ} {r : ℂ} {R : ℝ}
    (hrd : m.store.get rd.1 rd.2 = some R)
    (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hz : z.2 + 2 ≤ m.store.len z.1)
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock sp.1 sp.2 2)) :
    Writes .total I τ (regularizeDraw (O := O) (Q := Q)).body (Env.frame [] [rd, sp, z, sp])
      (Store.inBlock sp.1 sp.2 2 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos + 2 ∧ m'.store.readBlock sp.1 sp.2 2 =
        some [(excCentreWord M r (excSample τ s m.pos R)).1,
          (excCentreWord M r (excSample τ s m.pos R)).2]) m := by
  have hrl := Store.lt_length_of_get hrd
  have hre := Store.get_of_readBlock hs (j := 0) (by norm_num) 0
  have him := Store.get_of_readBlock hs (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hre him
  have hsl := Store.lt_length_of_get hre
  have hzl := Store.lt_length_of_lt_len (show z.2 < m.store.len z.1 by omega)
  set W := excSample τ s m.pos R with hW_def
  unfold regularizeDraw
  have hread : m.readBlocks [rd] [1] = some [[R]] := by
    simp [Mem.readBlocks, Store.readBlock, hrd]
  refine (writes_call (R := polarDiskRel s) hD (d := []) (a := [rd]) (b := [z])
    (k := 2) (ls := [2]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simp [Mem.Live]; omega, ⟨_, hread, trivial⟩, by
      simp [Mem.Room]; omega⟩)).seq_le (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨hp₁, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [[R]] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin 2 => (τ.window s m.pos 2).getD j 0) = Tape.windowFn τ s m.pos 2 := by
    funext j
    fin_cases j <;> simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  have hys' := hrel R hxs
  simp only [polarDiskRel] at hys'
  rw [hwin] at hys'
  have hWb : m₁.store.readBlock z.1 z.2 2 = some [W.re, W.im] := by
    subst hys'
    obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp (by simpa [Mem.readBlocks] using hys)
    simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
    rw [hy, hyy]; rfl
  have hW1 := Store.get_of_readBlock hWb (j := 0) (by norm_num) 0
  have hW2 := Store.get_of_readBlock hWb (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hW1 hW2
  have hz2 : Fp.Disj (Fp.blocks [z] [2]) (Store.inBlock sp.1 sp.2 2) := by
    simpa [Fp.blocks] using hzs
  have hre₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hz2.mono le_rfl (by fp_sub)) hre
  have him₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hz2.mono le_rfl (by fp_sub)) him
  refine (writes_call_bin (hS .add) rfl rfl trivial hre₁ hW1 rfl
    (fun _ => ⟨by simp [Mem.Live, hfr₁.length_eq]; omega, by
      rw [hfr₁.len_eq]; exact Store.lt_len_of_get hre⟩)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hX₂⟩
  have him₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) him₁
  have hW2₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (hzs.symm.mono (by fp_sub) (by fp_sub)) hW2
  refine (writes_call_bin (hS .add) rfl rfl trivial him₂ hW2₂ rfl
    (fun _ => ⟨by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega, by
      rw [hfr₂.len_eq, hfr₁.len_eq]; exact Store.lt_len_of_get him⟩)).mono (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hY₃⟩
  have hX₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hX₂
  exact ⟨by rw [hp₃, hp₂, hp₁], readBlock_pair_of_get hX₃ hY₃⟩

/-- **The rounding of a perturbed shift**: under the standard model,
$\lvert\mathrm{fl}(r + w) - (r + w)\rvert \le 2\boldsymbol{u}\lvert r + w\rvert$ for the
componentwise rounded sum `NLAlib.ShiftedQR.excCentreWord`. -/
theorem norm_excCentreWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (r w : ℂ) :
    ‖(⟨(excCentreWord M r w).1, (excCentreWord M r w).2⟩ : ℂ) - (r + w)‖ ≤
      2 * u * ‖r + w‖ := by
  have hu0 := hM.roundoff_nonneg
  have h1 := hM.add r.re w.re
  have h2 := hM.add r.im w.im
  simp only [id] at h1 h2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e : ((⟨(excCentreWord M r w).1, (excCentreWord M r w).2⟩ : ℂ) - (r + w)).re =
      M.add r.re w.re - (r.re + w.re) := by simp [excCentreWord]
  have e' : ((⟨(excCentreWord M r w).1, (excCentreWord M r w).2⟩ : ℂ) - (r + w)).im =
      M.add r.im w.im - (r.im + w.im) := by simp [excCentreWord]
  rw [e, e']
  have h3 : |r.re + w.re| ≤ ‖r + w‖ := by simpa using Complex.abs_re_le_norm (r + w)
  have h4 : |r.im + w.im| ≤ ‖r + w‖ := by simpa using Complex.abs_im_le_norm (r + w)
  nlinarith

end Proofs

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section Draws

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- The pair at `b` read as a complex number, an uninitialised word read as $0$. -/
def storedPair (b : ℕ × ℕ) (m : Mem ℝ) : ℂ := storedMatrix b 1 1 m.store 0 0

/-- A stored pair is the pair read from its block. -/
theorem storedPair_eq {b : ℕ × ℕ} {m : Mem ℝ} {z : ℂ}
    (h : m.store.readBlock b.1 b.2 2 = some [z.re, z.im]) : storedPair b m = z := by
  have hre := Store.get_of_readBlock h (j := 0) (by norm_num) 0
  have him := Store.get_of_readBlock h (j := 1) (by norm_num) 0
  simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ] at hre him
  apply Complex.ext <;> simp [storedPair, storedMatrix, hre, him]

/-- The bad windows of the perturbation of the pair at `b`: off the unit square, or bringing the
stored centre within $\eta$ of some $\lambda_l$. Jointly measurable in the memory and the
window. -/
theorem measurableSet_drawBad (b : ℕ × ℕ) {N : ℕ} (e : Fin N → ℂ) (R η : ℝ) :
    MeasurableSet {x : Mem ℝ × (Fin 2 → ℝ) | (∃ j, x.2 j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ l, ‖storedPair b x.1 + polarDisk 0 R x.2 - e l‖ < η} := by
  have hc : Measurable fun m : Mem ℝ => storedPair b m :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp (measurable_storedMatrix b 1 1))
  have hp : Measurable (polarDisk 0 R) := by unfold polarDisk; fun_prop
  have e1 : {x : Mem ℝ × (Fin 2 → ℝ) | (∃ j, x.2 j ∉ Set.Icc (0 : ℝ) 1) ∨
      ∃ l, ‖storedPair b x.1 + polarDisk 0 R x.2 - e l‖ < η} =
      (⋃ j, (fun x : Mem ℝ × (Fin 2 → ℝ) => x.2 j) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) ∪
        ⋃ l, {x | ‖storedPair b x.1 + polarDisk 0 R x.2 - e l‖ < η} := by
    ext x; simp
  rw [e1]
  refine (MeasurableSet.iUnion fun j => measurableSet_Icc.compl.preimage
    ((measurable_pi_apply j).comp measurable_snd)).union (MeasurableSet.iUnion fun l => ?_)
  exact measurableSet_lt (((hc.comp measurable_fst).add (hp.comp measurable_snd)).sub_const _
    |>.norm) measurable_const

/-- The state after `i` of the `k` perturbations of `NLAlib.ShiftedQR.regularizeDraws`: the
radius word $R$ at `rd`, room for the scratch pair `z`, targets $\lambda$ with the property
`Lam`, and $k$ pairs $c_j$ at `s` with
$\lvert c_j - \lambda_j\rvert \le \beta$ for $j \ge i$ (not yet perturbed) and, for
$j < i$, $\lvert c_j - \lambda_j\rvert \le \beta + R + \delta_j$ and every
$\lvert c_j - e_l\rvert + \delta_j \ge \eta$, where
$\delta_j = 2\boldsymbol{u}(\lvert\lambda_j\rvert + \beta + R)$. -/
def DrawsInv (u β R η : ℝ) {k N : ℕ} (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ)
    (rd z s : ℕ × ℕ) (i : ℕ) (m : Mem ℝ) : Prop :=
  m.store.get rd.1 rd.2 = some R ∧ z.2 + 2 ≤ m.store.len z.1 ∧ ∃ lam, Lam lam ∧ ∃ c : Fin k → ℂ,
    (∀ j : Fin k, m.store.readBlock s.1 (s.2 + 2 * j) 2 = some [(c j).re, (c j).im]) ∧
    ∀ j : Fin k, ((i ≤ j → ‖c j - lam j‖ ≤ β) ∧ ((j : ℕ) < i →
      ‖c j - lam j‖ ≤ β + R + 2 * u * (‖lam j‖ + β + R) ∧
        ∀ l, η ≤ ‖c j - e l‖ + 2 * u * (‖lam j‖ + β + R)))

/-- **One perturbation as a probabilistic block**: under an exact polar sampler on a stream `s₀`
uniform on $[0, 1]$, the perturbation of pair $i$ keeps `NLAlib.ShiftedQR.DrawsInv` from $i$ to
$i + 1$, except with probability at most $\varphi/(2k)$ (`regularize_bad_window_le`), for
$\eta = R\sqrt{\varphi/(2k)}$ and $\lambda$'s whose distinct values are $4R$ apart. -/
theorem regularizeDraw_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k N : ℕ} (hk : 0 < k)
    (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ) {β R φ : ℝ} (hR : 0 < R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) {rd z s : ℕ × ℕ}
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) (i : Fin k) :
    PWrites law I (regularizeDraw (O := O) (Q := Q)).body
      (Env.frame [] [rd, (s.1, s.2 + 2 * i), z, (s.1, s.2 + 2 * i)])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock z.1 z.2 2)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s i)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s (i + 1)) (φ / (2 * k)) := by
  set η := R * √(φ / (2 * k))
  have hu0 := hM.roundoff_nonneg
  have hpair : ∀ j : Fin k, Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * k) :=
    fun j => Fp.inBlock_le_inBlock (by omega) (by omega)
  refine PWrites.of_window (s := s₀) (W := 2) (Bad := fun m => {x | (∃ j, x j ∉ Set.Icc (0 : ℝ) 1)
    ∨ ∃ l, ‖storedPair (s.1, s.2 + 2 * i) m + polarDisk 0 R x - e l‖ < η})
    (measurableSet_drawBad _ e R η) ?_ ?_
  · rintro m ⟨-, -, -, -, c, hc, -⟩
    rw [storedPair_eq (b := (s.1, s.2 + 2 * i)) (hc i), hU]
    exact regularize_bad_window_le (c i) e hk hR hφ hφ1 hsep
  rintro m τ ⟨hrd, hz, lam, hlam, c, hc, hgood⟩ hwin
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_lt, storedPair_eq (b := (s.1, s.2 + 2 * i)) (hc i)] at hwin
  obtain ⟨hsq, hfar⟩ := hwin
  have hw := regularizeDraw_writes (τ := τ) (sp := (s.1, s.2 + 2 * i)) hS hD hrd (hc i) hz (hzs.mono le_rfl (hpair i))
  refine hw.mono (sup_le ((hpair i).trans le_sup_left) le_sup_right) ?_
  rintro m' hfr ⟨-, hnew⟩
  set W := excSample τ s₀ m.pos R
  have hW : ‖W‖ ≤ R := norm_polarDisk_le hR.le fun j => not_not.mp (hsq j)
  have hfar' : ∀ l, η ≤ ‖c i + W - e l‖ := hfar
  set c' := Function.update c i ⟨(excCentreWord M (c i) W).1, (excCentreWord M (c i) W).2⟩
  have hround := norm_excCentreWord_sub_le hM (c i) W
  have hci := (hgood i).1 le_rfl
  have hcw : ‖c i + W‖ ≤ ‖lam i‖ + β + R := by
    have := norm_add_le (c i - lam i + lam i) W
    have := norm_add_le (c i - lam i) (lam i)
    simp only [sub_add_cancel] at *
    linarith
  have hδ : 2 * u * ‖c i + W‖ ≤ 2 * u * (‖lam i‖ + β + R) := by gcongr
  refine ⟨hfr.keep (Store.readsOnly_get _ _ _) (Fp.disj_sup_left.mpr ⟨hsr.mono (hpair i) le_rfl, hzr⟩) hrd,
    by rw [hfr.len_eq]; exact hz, lam, hlam, c', fun j => ?_, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · by_cases hji : j = i
    · subst hji; simpa [c'] using hnew
    · have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
      have hd : Fp.Disj (Store.inBlock s.1 (s.2 + 2 * i) 2 ⊔ Store.inBlock z.1 z.2 2)
          (Store.inBlock s.1 (s.2 + 2 * j) 2) := by
        refine Fp.disj_sup_left.mpr ⟨?_, hzs.mono le_rfl (hpair j)⟩
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · exact (Fp.disj_inBlock_of_le (by omega)).symm
        · exact Fp.disj_inBlock_of_le (by omega)
      simpa [c', Function.update_of_ne hji] using
        hfr.keep (Store.readsOnly_readBlock _ _ _ _) hd (hc j)
  · have hji : j ≠ i := fun h => by subst h; simp at hj
    simpa [c', Function.update_of_ne hji] using (hgood j).1 (by simp at hj ⊢; omega)
  · by_cases hji : j = i
    · subst hji
      simp only [c', Function.update_self]
      refine ⟨?_, fun l => ?_⟩
      · have := norm_sub_le_norm_sub_add_norm_sub (⟨(excCentreWord M (c j) W).1,
          (excCentreWord M (c j) W).2⟩ : ℂ) (c j + W) (lam j)
        have h2 : ‖c j + W - lam j‖ ≤ ‖c j - lam j‖ + ‖W‖ := by
          rw [show c j + W - lam j = (c j - lam j) + W by ring]; exact norm_add_le _ _
        linarith
      · have := norm_sub_le_norm_sub_add_norm_sub (c j + W) (⟨(excCentreWord M (c j) W).1,
          (excCentreWord M (c j) W).2⟩ : ℂ) (e l)
        rw [norm_sub_rev (c j + W) (⟨(excCentreWord M (c j) W).1,
          (excCentreWord M (c j) W).2⟩ : ℂ)] at this
        linarith [hfar' l]
    · have hj' : (j : ℕ) < i := by
        have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
        simp at hj; omega
      simpa [c', Function.update_of_ne hji] using (hgood j).2 hj'

/-- **The $k$ perturbations as a probabilistic block**: under a measurable, tape-local
interpretation with an exact polar sampler on a stream `s₀` uniform on $[0, 1]$, from $k \ge 1$
pairs $c_j$ at `s` within $\beta$ of targets $\lambda_j$ and the radius word $R > 0$ at `rd`,
`NLAlib.ShiftedQR.regularizeDraws` writes only the pairs and the scratch pair `z` and, except
with probability at most $\varphi/2$, $0 \le \varphi \le 1$, stores pairs within
$\beta + R + \delta_j$ of the $\lambda_j$ and at distance at least
$R\sqrt{\varphi/(2k)} - \delta_j$ from every $e_l$, $\delta_j =
2\boldsymbol{u}(\lvert\lambda_j\rvert + \beta + R)$, provided the distinct $e_l$ are $4R$
apart ([BanksGarzaVargasSrivastava2022, Lemma 3.10], one draw at a time). -/
theorem regularizeDraws_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k N : ℕ}
    (hk : 0 < k) (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ) {β R φ : ℝ} (hR : 0 < R) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) {rd z s : ℕ × ℕ}
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) :
    PWrites law I (regularizeDraws (O := O) (Q := Q)).body (Env.frame [k] [rd, z, s])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock z.1 z.2 2)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s 0)
      (DrawsInv u β R (R * √(φ / (2 * k))) Lam e rd z s k) (φ / 2) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold regularizeDraws
  refine (PWrites.loop hI hloc (N := k) rfl _ (fun _ => φ / (2 * k))
    (fun _ _ => by positivity) (fun _ h => h) (fun i hi => ?_) (fun _ h => h)).mono
    (fun _ h => h) le_rfl (fun _ h => h) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      rfl)
  refine (regularizeDraw_pwrites hS hM hD hU hk Lam e hR hφ hφ1 hsep hzs hzr hsr ⟨i, hi⟩).in_frame
    rfl rfl ?_
  rintro m ⟨hrd, hz, -, -, c, hc, -⟩
  have h0 := Store.get_of_readBlock (hc ⟨i, hi⟩) (j := 0) (by norm_num) 0
  simp [Mem.Live, Store.lt_length_of_get hrd, Store.lt_length_of_get h0,
    Store.lt_length_of_lt_len (show z.2 < m.store.len z.1 by omega)]

end Draws

end NLAlib.ShiftedQR
