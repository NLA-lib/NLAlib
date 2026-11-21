/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedExc
public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularizeTrial

/-!
# The random perturbations of `Regularize`

`Regularize` ([BanksGarzaVargasSrivastava2022, §4.2]) perturbs each of its $k$ approximate Ritz
values by an independent polar sample of a disk of radius $R$, which keeps every shift away from
the spectrum ([BanksGarzaVargasSrivastava2022, Lemma 3.10]). This file has the two programs of
the perturbation, their stored words, and their failure probability.

## Main definitions

* `NLAlib.ShiftedQR.regularizeDraw`, `NLAlib.ShiftedQR.regularizeDraws`: one and $k$
  perturbations.
* `NLAlib.ShiftedQR.DrawsInv`: the invariant of the perturbations.

## Main results

* `NLAlib.ShiftedQR.regularize_bad_window_le`: one perturbation comes within
  $\eta = R\sqrt{\varphi/(2k)}$ of an eigenvalue with probability at most $\varphi/(2k)$.
* `NLAlib.ShiftedQR.regularizeDraws_pwrites`: the $k$ perturbations fail with probability at most
  $\varphi/2$.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

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
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 ≤ φ / (2 * k) := by positivity
  have hq1 : φ / (2 * k) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hηR : R * √(φ / (2 * k)) ≤ R := mul_le_of_le_one_right hR.le (Real.sqrt_le_one.mpr hq1)
  have h := measureReal_polarDisk_bad_le (η := R * √(φ / (2 * k))) (fun _ : Fin 1 => c) e hR
    (by positivity)
    fun i j hij => by linarith [hsep i j hij]
  refine (measureReal_mono fun x hx => ?_).trans (h.trans_eq ?_)
  · simpa using hx
  · rw [Nat.cast_one, one_mul, mul_div_cancel_left₀ _ hR.ne', Real.sq_sqrt hq0]

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **One random perturbation of a shift**: a polar sample $w$ of the radius word `Rd` into the
pair `Z`, then the pair `S` becomes $\mathrm{fl}(S + w)$ componentwise. The interface is
`[] (Rd, S) → (Z, S)`. -/
def regularizeDraw : Stmt O Q := ops% [] (Rd, S) → (Z, S) {
  call (Has.inj DiskSampleOp.polar) [] (Rd) → (Z);
  call (Has.inj ScalarOp.add) [] (S, Z) → (S);
  call (Has.inj ScalarOp.add) [] (S[1], Z[1]) → (S[1])
}

/-- **The $k$ random perturbations**: `NLAlib.ShiftedQR.regularizeDraw` on each of the $k$ pairs
of `S`, with the radius word `Rd` and the scratch pair `Z`. The interface is
`[k] (Rd) → (Z, S)`. -/
def regularizeDraws : Stmt O Q := ops% [k] (Rd) → (Z, S) {
  for i < k {
    run regularizeDraw [] (Rd, S[2 * i], Z, S[2 * i])
  }
}

end Program

section Proofs

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- One random perturbation on any scalar machine with an exact polar sampler on the stream
`s`: from the radius word $R$ at `Rd` and the pair $r$ at `S`, `NLAlib.ShiftedQR.regularizeDraw`
stores at `S` the rounded $\mathrm{fl}(r + w)$ (`NLAlib.ShiftedQR.excCentreWord`) of the polar
sample $w$ of radius $R$ read at the start position, writes only `S` and the scratch pair `Z`,
and advances the position by two.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem regularizeDraw_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {s : ℕ}
    (hD : IsPolarDiskSampler s I) {τ : Tape ℝ} {m : Mem ℝ} {rd sp z : ℕ × ℕ} {r : ℂ} {R : ℝ}
    (hrd : m.store.get rd.1 rd.2 = some R)
    (hs : m.store.readBlock sp.1 sp.2 2 = some [r.re, r.im])
    (hz : z.2 + 2 ≤ m.store.len z.1)
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock sp.1 sp.2 2)) :
    Writes .total I τ (regularizeDraw (O := O) (Q := Q)) (Env.frame [] [rd, sp, z, sp])
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

/-- The rounding of a perturbed shift: under the standard model,
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

/-- One perturbation as a probabilistic block: under an exact polar sampler on a stream `s₀`
uniform on $[0, 1]$, the perturbation of pair $i$ keeps `NLAlib.ShiftedQR.DrawsInv` from $i$ to
$i + 1$, except with probability at most $\varphi/(2k)$ (`regularize_bad_window_le`), for
$\eta = R\sqrt{\varphi/(2k)}$ and $\lambda$'s whose distinct values are $4R$ apart.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem regularizeDraw_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k N : ℕ} (hk : 0 < k)
    (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ) {β R φ : ℝ} (hR : 0 < R) (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) {rd z s : ℕ × ℕ}
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) (i : Fin k) :
    PWrites law I (regularizeDraw (O := O) (Q := Q))
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
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_lt,
    storedPair_eq (b := (s.1, s.2 + 2 * i)) (hc i)] at hwin
  obtain ⟨hsq, hfar⟩ := hwin
  have hw := regularizeDraw_writes (τ := τ) (sp := (s.1, s.2 + 2 * i)) hS hD hrd (hc i) hz
    (hzs.mono le_rfl (hpair i))
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
  refine ⟨hfr.keep (Store.readsOnly_get _ _ _)
    (Fp.disj_sup_left.mpr ⟨hsr.mono (hpair i) le_rfl, hzr⟩) hrd,
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
apart ([BanksGarzaVargasSrivastava2022, Lemma 3.10], one draw at a time).
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem regularizeDraws_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k N : ℕ}
    (hk : 0 < k) (Lam : (Fin k → ℂ) → Prop) (e : Fin N → ℂ) {β R φ : ℝ} (hR : 0 < R) (hφ : 0 ≤ φ)
    (hφ1 : φ ≤ 1) (hsep : ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖) {rd z s : ℕ × ℕ}
    (hzs : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock s.1 s.2 (2 * k)))
    (hzr : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock rd.1 rd.2 1))
    (hsr : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock rd.1 rd.2 1)) :
    PWrites law I (regularizeDraws (O := O) (Q := Q)) (Env.frame [k] [rd, z, s])
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
