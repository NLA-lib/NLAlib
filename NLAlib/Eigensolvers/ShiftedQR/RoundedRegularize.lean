/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedExc
public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularizeTrial

/-!
# The rounded `Regularize`

`Regularize` ([BanksGarzaVargasSrivastava2022, §4.2], called RitzOrDecouple there)
computes forward-approximate Ritz values with `SmallEig`, perturbs each by an independent uniform
sample of a small disk, and tests the perturbed values with `Optimal`. If they are optimal it
returns them; otherwise the dichotomy
(`NLAlib.exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues`) gives one among them whose
degree $k$ step decouples, and the program tries them in turn. The random perturbation keeps
every shift away from the spectrum, which the forward error of the rounded steps needs.

## Main definitions

* `NLAlib.ShiftedQR.regularize`: the program; `NLAlib.ShiftedQR.RegularizeOutcome`: its
  outcome.

## Main results

* `NLAlib.ShiftedQR.regularize_bad_window_le`: one perturbation comes within
  $\eta = R\sqrt{\varphi/(2k)}$ of an eigenvalue with probability at most $\varphi/(2k)$.
* `NLAlib.ShiftedQR.regularizeDraws_pwrites`: the $k$ perturbations fail with probability at most
  $\varphi/2$.
* `NLAlib.ShiftedQR.IsRandomSmallEig.smallEigLeaf_pwrites`: `SmallEig` with its forward error.
* `NLAlib.ShiftedQR.regularize_pwrites`: `Regularize` as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

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

/-- `Regularize` with a small-eigenvalue routine and caller-owned scratch: the trailing
$k \times k$ block of the order-$N$ matrix `A` into `B`, the routine `SE` with the words `Qw` and
the cap $T$ (interface `[d, nq, T] (Bk, Q) → (Ev)`) into the $k$ pairs `S`, one random
perturbation of each pair (radius word `Rd`), `Optimal` with the word `C` into `G`; if optimal,
the flag `Fl` is $0$; otherwise `Fl` is $2$ and the $k$ trials run until one decouples (then `Fl`
is $1$). The interface is
`[N, k, nq, T] (A, Rd, C, Thr, Qw, B, Z, G, Tm, SR, Ds, Rg) → (A, S, Fl)`. -/
def regularizeWithScratchWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, nq, T] (A, Rd, C, Thr, Qw, B, Z, G, Tm, SR, Ds, Rg) → (A, S, Fl) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, N - k, k] (A, B);
    run SE.body [k, nq, T] (B, Qw, S);
    run (regularizeDraws (O := O) (Q := Q)).body [k] (Rd, Z, S);
    run (regularizeDecide (O := O) (Q := Q)).body [N, k] (A, S, C, Thr, Tm, SR, Ds, Rg, A, G, Fl)
  }

/-- **`Regularize` with a small-eigenvalue routine** ([BanksGarzaVargasSrivastava2022, §4.2],
RitzOrDecouple there): from the order-$N$ matrix `A`, the radius word `Rd` of the perturbations,
the word `C` of `Optimal` ($0.999\theta^k$), the threshold word `Thr` of the decoupling scan and
the words `Qw` of the routine `SE`, store $k$ perturbed approximate Ritz values at `S` and set the
flag `Fl` to $0$ (they are optimal, `A` unchanged) or $1$ (`A` holds a decoupled degree $k$ step);
`Fl` is $2$ only if no trial decoupled. All scratch is scoped. The interface is
`[N, k, nq, T] (A, Rd, C, Thr, Qw) → (A, S, Fl)`. -/
def regularizeWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, nq, T] (A, Rd, C, Thr, Qw) → (A, S, Fl) {
    let B ← alloc (2 * (k * k));
    let Z ← alloc 2;
    let G ← alloc 1;
    let Tm ← alloc (2 * (N * N));
    let SR ← alloc (2 * k);
    let Ds ← alloc (2 * k);
    let Rg ← alloc 5;
    run (regularizeWithScratchWith SE).body [N, k, nq, T]
      (A, Rd, C, Thr, Qw, B, Z, G, Tm, SR, Ds, Rg, A, S, Fl)
  }

/-- **`Regularize`** ([BanksGarzaVargasSrivastava2022, §4.2], RitzOrDecouple there):
`NLAlib.ShiftedQR.regularizeWith` with the `SmallEig` kernel as the routine
(`NLAlib.ShiftedQR.smallEigKernel`), no words and the cap $0$. From the order-$N$ matrix `A`, the
radius word `Rd` of the perturbations, the word `C` of `Optimal` ($0.999\theta^k$) and the
threshold word `Thr` of the decoupling scan, store $k$ perturbed approximate Ritz values at `S`
and set the flag `Fl` to $0$ (they are optimal, `A` unchanged) or $1$ (`A` holds a decoupled
degree $k$ step); `Fl` is $2$ only if no trial decoupled. The interface is
`[N, k] (A, Rd, C, Thr) → (A, S, Fl)`. -/
def regularize : Impl O Q := opsImpl% [N, k] (A, Rd, C, Thr) → (A, S, Fl) {
  run (regularizeWith (smallEigKernel (O := O) (Q := Q))).body [N, k, 0, 0]
    (A, Rd, C, Thr, Rd, A, S, Fl)
}

end Program

section Proofs

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- One random perturbation on any scalar machine with an exact polar sampler on the stream
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

/-- One perturbation as a probabilistic block: under an exact polar sampler on a stream `s₀`
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



namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section SmallEig

variable {O Q : Type} [Has EigenvalueKernelOp O]

/-- **A randomized small-eigenvalue kernel with its forward error**
([BanksGarzaVargasSrivastava2022, Definition 1.2]): if the interpretation's `smallEig` is a
randomized kernel with forward error $\beta$ and failure probability $\varphi$ on the stream `s`
(`NLAlib.ShiftedQR.IsRandomSmallEig`), the leaf routine that calls it on an upper Hessenberg
$\mathbf{B}$ of order $d$ writes only its output and, except with probability at most $\varphi$,
stores values within $\beta$ of a listing of the eigenvalues of $\mathbf{B}$ with multiplicity. -/
theorem IsRandomSmallEig.smallEigLeaf_pwrites {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) {d : ℕ} {w o : ℕ × ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : IsUpperHessenberg B) :
    PWrites law I (smallEigLeaf (O := O) (Q := Q)).body (Env.frame [d] [w, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.Live [w, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ := by
  obtain ⟨W, Bad, hBad, hφ, hI⟩ := h
  refine PWrites.of_window (s := s) (W := W d) (Bad := fun _ => Bad d B)
    (measurable_snd (hBad d B)) (fun _ _ => hφ d B hB) ?_
  rintro μ τ ⟨hH, hl, hroom, hdisj⟩ hgood
  unfold smallEigLeaf
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  refine (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa [Mem.Live] using hl, ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) ?_
  rintro μ' - ⟨-, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [matrixWords B] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) =
      Tape.windowFn τ s μ.pos (W d) := by
    funext j
    simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  obtain ⟨roots, ev, hev, hfw, rfl⟩ := hrel d (matrixWords B) rfl hxs
    (by simpa using hB) (by
      change (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) ∉ _
      rw [hwin]
      simpa using hgood)
  rw [matrixOfWords_matrixWords] at hev
  refine ⟨roots, ev, hev, hfw, ?_⟩
  obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp
    (by simpa [Mem.readBlocks, randomSmallEigRel] using hys)
  simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
  simpa [HoldsMatrix] using hyy ▸ hy

end SmallEig

end NLAlib.ShiftedQR

namespace NLAlib

variable {n : ℕ}

/-- An eigenvalue of the trailing $k \times k$ block, $k \le n + 1$, is at most
$\|\mathbf{H}\|_2$. -/
theorem IsEigenvalueListing.norm_le_specNorm_of_trailingBlock {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lam : Fin k → ℂ}
    (hlam : IsEigenvalueListing (trailingBlock k H) lam) (hkn : k ≤ n + 1) (j : Fin k) :
    ‖lam j‖ ≤ specNorm H := by
  have hroots : (trailingBlock k H).charpoly.roots = (List.ofFn lam : Multiset ℂ) := by
    rw [isEigenvalueListing_iff.mp hlam]
    simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      List.prod_ofFn, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (List.ofFn lam : Multiset ℂ)
  refine norm_le_specNorm_of_mem_ritzValues hkn ?_
  rw [ritzValues, Multiset.mem_toList, hroots, Multiset.mem_coe]
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- The trailing $k \times k$ block, $k \le n + 1$, has spectral norm at most
$\|\mathbf{H}\|_2$. -/
theorem specNorm_trailingBlock_le {k : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hkn : k ≤ n + 1) : specNorm (trailingBlock k H) ≤ specNorm H := by
  have hinj : Function.Injective fun i : Fin k =>
      (⟨min (n + 1 - k + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (n + 1)) := by
    intro i j h
    simp only [Fin.mk.injEq] at h
    ext
    omega
  exact specNorm_submatrix_le H hinj hinj

end NLAlib

namespace NLAlib.ShiftedQR

open Ops

/-- The words `Regularize` with scratch at `L, …, L + 6` reads, and the room it writes into: the
matrix $\mathbf{H}$ at `a`, the radius word $R$ at `rd`, the word $c_w$ at `c`, the threshold
word $t$ at `thr`, room for the $k$ output pairs at `s` and the flag at `f`, and seven scratch
buffers of the lengths of `NLAlib.ShiftedQR.regularize` above the $L$ buffers of the caller. -/
def RegularizeCtx (L : ℕ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (R cw tv : ℝ) (a rd c thr s f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  HoldsMatrix a H m.store ∧ m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some cw ∧
    m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
    f.2 < m.store.len f.1 ∧ m.store.length = L + 7 ∧ m.store.len L = 2 * (k * k) ∧
    m.store.len (L + 1) = 2 ∧ m.store.len (L + 2) = 1 ∧
    m.store.len (L + 3) = 2 * ((n + 1) * (n + 1)) ∧ m.store.len (L + 4) = 2 * k ∧
    m.store.len (L + 5) = 2 * k ∧ m.store.len (L + 6) = 5

/-- The context survives a write apart from the matrix and the three input words. -/
theorem RegularizeCtx.of_eqOff {L n k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} {a rd c thr s f : ℕ × ℕ} {m m' : Mem ℝ} {F : Fp}
    (h : RegularizeCtx L k H R cw tv a rd c thr s f m) (hfr : m.store.EqOff F m'.store)
    (hF : Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1)) :
    RegularizeCtx L k H R cw tv a rd c thr s f m' := by
  obtain ⟨hA, hrd, hc, ht, hs, hf, hlen, h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hA.of_eqOff hfr (hF.mono le_rfl (by fp_sub)),
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hrd,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hc,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) ht, ?_⟩
  simp only [hfr.len_eq, hfr.length_eq]
  exact ⟨hs, hf, hlen, h0, h1, h2, h3, h4, h5, h6⟩

/-- **The outcome of `Regularize`**, with the optimality parameter $\theta$, the distance $d$ to
the spectrum, the threshold word $t$ and the backward error $\varepsilon$: either the flag is $0$,
`a` still holds $\mathbf{H}$, and `s` holds $k$ shifts that are $\theta$-optimal, at distance at
least $d$ from every $e_i$ and in $\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$; or the flag is $1$ and
`a` holds an upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$\varepsilon$ one of whose bottom $k$ subdiagonal entries passes the scan. -/
def RegularizeOutcome {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e : Fin (n + 1) → ℂ) (u θ d tv ε : ℝ) (a s f : ℕ × ℕ) (m' : Mem ℝ) : Prop :=
  (m'.store.get f.1 f.2 = some 0 ∧ HoldsMatrix a H m'.store ∧ ∃ zs : Fin k → ℂ,
      m'.store.readBlock s.1 s.2 (2 * k) = some ((List.ofFn zs).flatMap fun z => [z.re, z.im]) ∧
      IsOptimalRitzValues θ H (List.ofFn zs) ∧ (∀ j i, d ≤ ‖e i - zs j‖) ∧
      ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∨
    (m'.store.get f.1 f.2 = some 1 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsPerturbedUnitarySimilar H H' ε ∧ IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
      ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv)

/-- The bounds on the perturbed shifts that `Regularize` needs: from shifts $z_j$ within
$\beta + R + \delta_j$ of a listing $\lambda$ of the eigenvalues of the trailing block, with
$\lvert z_j - e_l\rvert + \delta_j \ge \eta$, $\delta_j = 2\boldsymbol{u}(\lvert\lambda_j\rvert
+ \beta + R)$, under $\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$ and $0 < \omega \le \psi_k(\mathbf{H})$,
$\|\mathbf{H}\|_2 \le \Sigma$: the shifts are within $\omega^2/(2020\Sigma)$ of $\lambda$, in
$\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$ and at distance at least $\eta/2$ from every $e_l$. -/
theorem regularize_shift_bounds {n k N : ℕ} {u β R η ω S : ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lam zs : Fin k → ℂ} {e : Fin N → ℂ}
    (hu0 : 0 ≤ u) (hk : 0 < k) (hkn : k ≤ n) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hS : specNorm H ≤ S) (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ η)
    (hz : ∀ j : Fin k, ‖zs j - lam j‖ ≤ β + R + 2 * u * (‖lam j‖ + β + R) ∧
      ∀ l, η ≤ ‖zs j - e l‖ + 2 * u * (‖lam j‖ + β + R)) :
    (∀ j, ‖zs j - lam j‖ ≤ ω ^ 2 / (20 * 101 * S)) ∧ (∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∧
      ∀ j l, η / 2 ≤ ‖e l - zs j‖ := by
  have hψH := hessenbergPotential_le_specNorm hk hkn H
  have hS0 : 0 < S := by linarith
  have hlH : ∀ j, ‖lam j‖ ≤ specNorm H := fun j =>
    hlam.norm_le_specNorm_of_trailingBlock (by omega) j
  have hδ : ∀ j, 2 * u * (‖lam j‖ + β + R) ≤ 2 * u * (S + β + R) := fun j => by
    have := hlH j; gcongr; linarith
  have hsmall : ω ^ 2 / (20 * 101 * S) ≤ 0.1 * specNorm H := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun j => ?_, fun j => ?_, fun j l => ?_⟩
  · linarith [(hz j).1, hδ j]
  · have h1 := norm_le_norm_add_norm_sub' (zs j) (lam j)
    linarith [(hz j).1, hδ j, hlH j]
  · have := (hz j).2 l
    rw [norm_sub_rev] at this
    nlinarith [hδ j]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Tail

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The views of `Regularize` are apart: the matrix, the output pairs and the flag from each other
and from the three input words, all below the scratch handle $L$. -/
structure RegularizeViews (L : ℕ) (n k : ℕ) (a rd c thr s f : ℕ × ℕ) : Prop where
  /-- Every view is below the scratch handle. -/
  lt : a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧ thr.1 < L ∧ s.1 < L ∧ f.1 < L
  /-- The matrix is apart from the shifts. -/
  as : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock s.1 s.2 (2 * k))
  /-- The matrix is apart from the flag. -/
  af : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1)
  /-- The shifts are apart from the flag. -/
  sf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1)
  /-- The outputs are apart from the three input words. -/
  io : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
    Store.inBlock f.1 f.2 1) (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔
      Store.inBlock thr.1 thr.2 1)

/-- The deterministic tail of `Regularize`: from the context
`NLAlib.ShiftedQR.RegularizeCtx` and $k \ge 1$ perturbed shifts at `s` as
`NLAlib.ShiftedQR.DrawsInv` leaves them (within $\beta + R + \delta_j$ of a listing of the
eigenvalues of the trailing block, $\eta - \delta_j$ from every eigenvalue), under the precision
conditions of `Optimal`, of the rounded steps and of the scan, the decision of `Regularize` ends
in `NLAlib.ShiftedQR.RegularizeOutcome` with $d = \eta/2$, the optimality parameter
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$ and the backward error
$2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularizeDecide_outcome {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k L : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω β R η tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖) (hη : 0 < η)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ η) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (η / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (η / 2)) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (hctx : RegularizeCtx L k H R
      (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
      a rd c thr s f m)
    (hinv : DrawsInv u β R η (fun lam : Fin k → ℂ => IsEigenvalueListing (trailingBlock k H) lam)
      e rd (L + 1, 0) s k m) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a,
        (L + 2, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5))
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (η / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f) m := by
  set θ := 1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) with hθdef
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv
  obtain ⟨hA, -, hc, hthr, -, hrf, hlen, -, -, h2, h3, h4, h5, h6⟩ := hctx
  obtain ⟨-, -, lam, hlam, zs, hpairs, hzk⟩ := hinv
  have hu0 := hM.roundoff_nonneg
  have hψH := hessenbergPotential_le_specNorm hk0 hk H
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hS0 : 0 < S := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le one_pos ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hθ : 0 < θ := by positivity
  obtain ⟨hzl, hz, hdist⟩ := regularize_shift_bounds hu0 hk0 hk hω hψ hSH hlam hβ hdη
    (fun j => (hzk j).2 j.isLt)
  have hx : (0 : ℝ) ≤ 300 * (n + 1) ^ 2 * u := by positivity
  have huo' : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * 1.1) * specNorm H) ^ k ≤ (θ * hessenbergPotential k H) ^ k := by
    refine le_trans ?_ (huo.trans (by gcongr))
    gcongr
  have hdich := fun hopt => exists_forall_isStableQRChain_exists_norm_subdiag_le (d := η / 2)
    hH hk0 hk hBk hω hV hHV hκ hgap hSH hψ hlam hzl hz (by positivity)
    (fun j i => hdist j i) hopt hx hxu hbound
  have hdec := regularizeDecide_writes (τ := τ) (m := m) (a := a) (s := s) (c := c) (thr := thr)
    (t := (L + 3, 0)) (sr := (L + 4, 0)) (ds := (L + 5, 0)) (rg := (L + 6, 0)) (g := (L + 2, 0))
    (f := f) (C := 1.1) hS hM hu1 hL hNat hC hk0 hk hH hnu hθ hψ0 hz huo' huo1 hA hpairs hc hthr
    (by simp [h2]) hrf (by simp [h3]) (by simp [h4]) (by simp [h5]) (by simp [h6])
    (by disjoint) (by disjoint) (by disjoint) (by disjoint) (by disjoint)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨by disjoint, haf.symm⟩⟩)
    (by disjoint) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨has, hio.mono (by fp_sub) (by fp_sub)⟩,
        hio.mono (by fp_sub) (by fp_sub)⟩, by disjoint⟩, Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨hsf.symm, hio.mono (by fp_sub) (by fp_sub)⟩,
        hio.mono (by fp_sub) (by fp_sub)⟩⟩) hdich hthrω
  refine hdec.mono le_rfl ?_
  rintro m' hfr (⟨hF, hA', hopt⟩ | ⟨hF, j, H', Rs, hch, hH', hA', hdec'⟩)
  · refine Or.inl ⟨hF, hA', zs, ?_, hopt, fun j i => hdist j i, hz⟩
    have := readBlock_flatMap_pair_of_forall (s := m'.store) (b := s.1) (o := s.2)
      (zs := List.ofFn zs) fun j hj => by
        have hj' : j < k := by simpa using hj
        have hkeep := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr
          ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has.symm.mono
            (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl |>.symm, by disjoint⟩,
            hsf.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl |>.symm⟩,
            by disjoint⟩) (hpairs ⟨j, hj'⟩)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj'] using hkeep
    simpa using this
  · refine Or.inr ⟨hF, H', ?_, hH', hA', hdec'⟩
    have hsim := hch.isPerturbedUnitarySimilar hx (C := 1.1) (fun s hs => by
      rw [List.eq_of_mem_replicate hs]; exact hz j)
    simpa using hsim

end Tail

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

/-- The separation the perturbations need: if $\beta, R \ge 0$ and
$\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$, then eigenvalues
separated by $2\omega^2/\Sigma$ are $4R$ apart ($0 < \omega \le \psi_k(\mathbf{H})$,
$\|\mathbf{H}\|_2 \le \Sigma$). -/
theorem regularize_sep_of_gap {n k : ℕ} {u β R ω S : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} (hu0 : 0 ≤ u) (hk0 : 0 < k) (hk : k ≤ n) (hω : 0 < ω)
    (hψ : ω ≤ hessenbergPotential k H) (hSH : specNorm H ≤ S)
    (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖) (hβ0 : 0 ≤ β) (hR : 0 ≤ R)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S)) :
    ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖ := by
  intro i j hij
  have hS0 : 0 < S := lt_of_lt_of_le (lt_of_lt_of_le hω
    (hψ.trans (hessenbergPotential_le_specNorm hk0 hk H))) hSH
  have h1 := hgap i j (fun h => hij (h ▸ rfl))
  have h2 : 0 ≤ 2 * u * (S + β + R) := by positivity
  have h3 : ω ^ 2 / (20 * 101 * S) = 2 * ω ^ 2 / S / 4040 := by field_simp; ring
  have h4 : 0 ≤ 2 * ω ^ 2 / S := by positivity
  linarith

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section Assembly

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] [Has EigenvalueKernelOp O] in
/-- `Regularize` with a small-eigenvalue routine and scratch as a probabilistic block:
`NLAlib.ShiftedQR.regularizeWithScratchWith` from the context `NLAlib.ShiftedQR.RegularizeCtx`
with the routine's words stored below the scratch, apart from the shifts, ends in
`NLAlib.ShiftedQR.RegularizeOutcome` except with probability at most
$\varphi_{\mathrm{se}} + \varphi/2$: the routine (`NLAlib.ShiftedQR.RandomSmallEigContractAt` on
orders at most $k$ and norms at most $\Sigma$) fails with probability at most
$\varphi_{\mathrm{se}}$, the $k$ perturbations with probability at most $\varphi/2$, the rest is
deterministic. -/
theorem regularizeWithScratchWith_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k L : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ} (hqL : qw.1 < L)
    (hqw : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock qw.1 qw.2 qs.length)) :
    PWrites law I (regularizeWithScratchWith SE).body
      (Env.frame [n + 1, k, nq, T] [a, rd, c, thr, qw, (L, 0), (L + 1, 0), (L + 2, 0),
        (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a, s, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Fp.above L)
      (fun m => RegularizeCtx L k H R
        (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
        a rd c thr s f m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs)
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f)
      (φse + φ / 2) := by
  set cw := 0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k
  set η := R * √(φ / (2 * k))
  set Ctx := RegularizeCtx L k H R cw tv a rd c thr s f
  set Lam := fun lam : Fin k → ℂ => IsEigenvalueListing (trailingBlock k H) lam
  have hv' := hv
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv'
  have hIn : ∀ {F : Fp}, Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) →
      ∀ {m m'}, Ctx m → m.store.EqOff F m'.store → Ctx m' := fun hF _ _ h hfr => h.of_eqOff hfr hF
  have hsep := regularize_sep_of_gap hM.roundoff_nonneg hk0 hk hω hψ hSH hgap hβ0 hR.le hβ
  have hsIn : Fp.Disj (Store.inBlock s.1 s.2 (2 * k))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock rd.1 rd.2 1 ⊔
        Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) :=
    Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨has.symm,
      hio.mono (by fp_sub) (by fp_sub)⟩, hio.mono (by fp_sub) (by fp_sub)⟩,
      hio.mono (by fp_sub) (by fp_sub)⟩
  have hHt : IsUpperHessenberg (trailingBlock k H) := hH.subBlock (r := (n + 1 - k, k)) (by omega)
  have hHtS : specNorm (trailingBlock k H) ≤ S := (specNorm_trailingBlock_le H (by omega)).trans hSH
  have hqLw : ∀ {o m : ℕ}, Fp.Disj (Store.inBlock L o m) (Store.inBlock qw.1 qw.2 qs.length) :=
    Fp.disj_inBlock_of_ne (by omega)
  unfold regularizeWithScratchWith
  -- the trailing block
  have h1 : PWrites law I (copyToWork (Op := O) (Tst := Q)).body
      (Env.frame [n + 1, n + 1 - k, k] [a, (L, 0)]) (Store.inBlock L 0 (2 * (k * k)))
      (fun m => Ctx m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs)
      (fun m => (Ctx m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs) ∧
        HoldsMatrix (L, 0) (trailingBlock k H) m.store) 0 := by
    refine PWrites.of_writes le_rfl fun m τ ⟨hm, hq⟩ => ?_
    obtain ⟨hA, -, -, -, -, -, hlen, h0, -⟩ := id hm
    refine (copyToWork_writes (τ := τ) (w := (L, 0)) (lo := n + 1 - k) (d := k) hS
      (by simp [Mem.Live, hlen]; omega) hA (by omega) (by simp [h0]) (by disjoint)).mono le_rfl ?_
    rintro m' hfr ⟨-, hB⟩
    exact ⟨⟨hIn (by disjoint) hm hfr, hfr.keep (Store.readsOnly_readBlock _ _ _ _) hqLw hq⟩, hB⟩
  -- the routine on the trailing block
  have h2 : PWrites law I SE.body (Env.frame [k, nq, T] [(L, 0), qw, s])
      (Store.inBlock s.1 s.2 (2 * k))
      (fun m => (Ctx m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs) ∧
        HoldsMatrix (L, 0) (trailingBlock k H) m.store)
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s 0 m) φse := by
    refine (hSE (w := (L, 0)) (q := qw) (o := s) (trailingBlock k H) le_rfl hHt hHtS).mono_eqOff
      ?_ ?_
    · rintro m ⟨⟨hm, hq⟩, hB⟩
      obtain ⟨-, -, -, -, hrs, -, hlen, -⟩ := hm
      exact ⟨hB, hq, by simp [Mem.Live, hlen]; omega, hrs, by disjoint, hqw.symm⟩
    · rintro m m' ⟨⟨hm, -⟩, -⟩ hfr ⟨roots, ev, hev, hfw, hO⟩
      have hm' := hIn hsIn hm hfr
      obtain ⟨-, hrd', -, -, -, -, -, -, hz', -⟩ := id hm'
      refine ⟨hm', hrd', by simp [hz'], ev, hev, roots, fun j => ?_, fun j =>
        ⟨fun _ => hfw j, fun h => absurd h (Nat.not_lt_zero _)⟩⟩
      simpa using hO.read_entry j 0
  -- the `k` perturbations
  have h3 : PWrites law I (regularizeDraws (O := O) (Q := Q)).body
      (Env.frame [k] [rd, (L + 1, 0), s])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock (L + 1) 0 2)
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s 0 m)
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s k m) (φ / 2) :=
    (regularizeDraws_pwrites (β := β) hI hloc hS hM hD hU hk0 Lam e hR hφ.le hφ1 hsep
      (by disjoint) (by disjoint) (hio.mono (by fp_sub) (by fp_sub))).mono_eqOff
      (fun _ h => h.2) fun m m' hm hfr hinv =>
        ⟨hIn (Fp.disj_sup_left.mpr ⟨hsIn, by disjoint⟩) hm.1 hfr, hinv⟩
  -- the decision
  have h4 : PWrites law I (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a,
        (L + 2, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5))
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s k m)
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (η / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f) 0 :=
    PWrites.of_writes le_rfl fun m τ ⟨hm, hinv⟩ => regularizeDecide_outcome hS hM hu1 hL hNat hC
      hk0 hk hv hH hV hHV hκ hBk hω hψ hSH hgap (by positivity) hβ hdη hnu huo huo1 hxu hbound
      hthrω hm hinv
  have hlive : ∀ (l : List (ℕ × ℕ)), (∀ x ∈ l, x.1 < L + 7) → ∀ m, Ctx m → m.Live l :=
    fun l hl m hm x hx => by obtain ⟨-, -, -, -, -, -, hlen, -⟩ := hm; rw [hlen]; exact hl x hx
  refine (PWrites.seq hI hloc (by positivity) (h1.in_frame rfl rfl fun m hm =>
      hlive _ (by simp; omega) m hm.1)
    (PWrites.seq hI hloc (by positivity) (h2.in_frame rfl rfl fun m hm =>
      hlive _ (by simp; omega) m hm.1.1)
      (PWrites.seq hI hloc le_rfl (h3.in_frame rfl rfl fun m hm => hlive _ (by simp; omega) m hm.1)
        (h4.in_frame rfl rfl fun m hm => hlive _ (by simp; omega) m hm.1)))).mono
    (fun _ h => h) (by fp_sub) (fun _ h => h) (by simp)

omit [Has IdxTst Q] in
/-- **`Regularize` with a small-eigenvalue routine as a probabilistic block**, with the word count
`nq` apart from the words `qs` (`NLAlib.ShiftedQR.RandomSmallEigContractAt`):
`NLAlib.ShiftedQR.regularize_pwrites` for `NLAlib.ShiftedQR.regularizeWith`; the merged statement
is the case of the kernel, `NLAlib.ShiftedQR.regularizeWith_pwrites` the case `nq = qs.length`.
`Regularize` as a probabilistic block ([BanksGarzaVargasSrivastava2022, Lemma 4.6],
corrected: the constant of the dichotomy, Theorem 4.1, is $\tfrac12 k^{-1/(2k)}$, which the
printed last display drops to $(2k)^{-1/(2k)}$ without the factor $2$; the proof's test is
$\psi_k(\mathbf{H}) \ge \varepsilon$ where the paper prints $\le$; and the precision of
`Optimal`, Lemma 4.5, carries $n + kn^{3/2}$ where the paper has $2n^2$, which needs
$k \lesssim 2\sqrt{n}$): on a scalar machine with the standard model,
exact comparisons, index literals and exact natural literals up to $n + 1$, a measurable
tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$ and $B^{2/k} \le 2$, $1 \le k \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$, the
radius word $R > 0$, $0 < \varphi \le 1$, $\eta = R\sqrt{\varphi/(2k)}$,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the word $0.999\theta^k$ and a threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, and the precision conditions
$\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$, those of `Optimal` (with $C = 1.1$), and those
of the forward error of the rounded steps at the distance $\eta/2$
(`NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow`). Then
`NLAlib.ShiftedQR.regularize` writes only the matrix, the $k$ output pairs and the flag, and
except with probability at most $\varphi_{\mathrm{se}} + \varphi/2$ ends in
`NLAlib.ShiftedQR.RegularizeOutcome`: $\theta$-optimal shifts at distance at least $\eta/2$
from the spectrum with $\mathbf{H}$ unchanged, or a decoupled perturbed unitary similarity with
backward error $2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularizeWith_pwrites_at {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length)) :
    PWrites law I (regularizeWith SE).body
      (Env.frame [n + 1, k, nq, T] [a, rd, c, thr, qw, a, s, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1)
      (fun m => m.Live [a, rd, c, thr, qw, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
        f.2 < m.store.len f.1)
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f)
      (φse + φ / 2) := by
  have hφ0 : 0 ≤ φse + φ / 2 := by positivity
  have e : (regularizeWith SE).body = Stmt.allocs [.const 2 * (.var 1 * .var 1),
      .const 2, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 1, .const 2 * .var 1,
      .const 5] (.frame [.var 0, .var 1, .var 2, .var 3] [⟨0, .var 4⟩, ⟨1, .var 5⟩, ⟨2, .var 6⟩,
        ⟨3, .var 7⟩, ⟨4, .var 8⟩, ⟨8, .const 0⟩, ⟨9, .const 0⟩, ⟨10, .const 0⟩, ⟨11, .const 0⟩,
        ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨0, .var 4⟩, ⟨6, .var 10⟩, ⟨7, .var 11⟩]
        (regularizeWithScratchWith SE).body) := rfl
  rw [e]
  refine PWrites.allocs rfl (Pre₁ := fun L μ => (RegularizeViews L n k a rd c thr s f ∧
    qw.1 < L) ∧ (RegularizeCtx L k H R
      (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
      a rd c thr s f μ ∧ μ.store.readBlock qw.1 qw.2 qs.length = some qs)) ?_ ?_ fun L => ?_
  · rintro m s₁ ⟨hl, hA, hq, hrd, hc, hthr, hrs, hrf⟩ hlen hlens hBelow
    have hlv : a.1 < m.store.length ∧ rd.1 < m.store.length ∧ c.1 < m.store.length ∧
        thr.1 < m.store.length ∧ qw.1 < m.store.length ∧ s.1 < m.store.length ∧
        f.1 < m.store.length := by
      simpa [Mem.Live] using hl
    obtain ⟨h1, h2, h3, h4, hq7, h5, h6⟩ := hlv
    have hl7 := fun i (hi : i < 7) => hlens i (by simpa using hi)
    refine ⟨⟨⟨⟨h1, h2, h3, h4, h5, h6⟩, has, haf, hsf, hio⟩, hq7⟩, ⟨hA.of_below hBelow h1,
      hBelow.get_of h2 hrd, hBelow.get_of h3 hc, hBelow.get_of h4 hthr,
      by rw [(hBelow s.1 h5).1]; exact hrs, by rw [(hBelow f.1 h6).1]; exact hrf,
      by simpa using hlen, ?_⟩, (hBelow.readBlock hq7 qw.2 qs.length).trans hq⟩
    simpa using ⟨hl7 0 (by norm_num), hl7 1 (by norm_num), hl7 2 (by norm_num),
      hl7 3 (by norm_num), hl7 4 (by norm_num), hl7 5 (by norm_num), hl7 6 (by norm_num)⟩
  · rintro m ⟨hl, -⟩ st st' p hBelow hout
    have hlv : a.1 < m.store.length ∧ s.1 < m.store.length ∧ f.1 < m.store.length := by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hl
      exact ⟨hl.1, hl.2.2.2.2.2.1, hl.2.2.2.2.2.2⟩
    obtain ⟨h1, h5, h6⟩ := hlv
    rcases hout with ⟨hF, hA, zs, hzs, hrest⟩ | ⟨hF, H', hsim, hH', hA, hdec⟩
    · exact Or.inl ⟨hBelow.get_of h6 hF, hA.of_below hBelow h1, zs,
        hBelow.readBlock_of h5 hzs, hrest⟩
    · exact Or.inr ⟨hBelow.get_of h6 hF, H', hsim, hH', hA.of_below hBelow h1, hdec⟩
  · by_cases hvL : RegularizeViews L n k a rd c thr s f ∧ qw.1 < L
    · refine ((regularizeWithScratchWith_pwrites hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU hk0
        hk hvL.1 hH hV hHV hκ hBk hω hψ hSH hgap hR hφ hφ1 hβ hdη hnu huo huo1 hxu hbound
        hthrω hSE hvL.2 (hqw.mono (by fp_sub) le_rfl)).in_frame rfl rfl ?_).mono
        (fun _ h => h.2) (by fp_sub) (fun _ h => h) le_rfl
      rintro μ ⟨⟨-, -, -, -, -, -, hlen, -⟩, -⟩
      obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6⟩, -⟩, hq⟩ := hvL
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, hlen]
      omega
    · exact PWrites.of_writes hφ0 fun _ _ h => absurd h.1 hvL


omit [Has IdxTst Q] in
/-- **`Regularize` as a probabilistic block** ([BanksGarzaVargasSrivastava2022, Lemma 4.6],
corrected: the constant of the dichotomy, Theorem 4.1, is $\tfrac12 k^{-1/(2k)}$, which the
printed last display drops to $(2k)^{-1/(2k)}$ without the factor $2$; the proof's test is
$\psi_k(\mathbf{H}) \ge \varepsilon$ where the paper prints $\le$; and the precision of
`Optimal`, Lemma 4.5, carries $n + kn^{3/2}$ where the paper has $2n^2$, which needs
$k \lesssim 2\sqrt{n}$): on a scalar machine with the standard model,
exact comparisons, index literals and exact natural literals up to $n + 1$, a measurable
tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$ and $B^{2/k} \le 2$, $1 \le k \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$, the
radius word $R > 0$, $0 < \varphi \le 1$, $\eta = R\sqrt{\varphi/(2k)}$,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the word $0.999\theta^k$ and a threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, and the precision conditions
$\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$, those of `Optimal` (with $C = 1.1$), and those
of the forward error of the rounded steps at the distance $\eta/2$
(`NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow`). Then
`NLAlib.ShiftedQR.regularize` writes only the matrix, the $k$ output pairs and the flag, and
except with probability at most $\varphi_{\mathrm{se}} + \varphi/2$ ends in
`NLAlib.ShiftedQR.RegularizeOutcome`: $\theta$-optimal shifts at distance at least $\eta/2$
from the spectrum with $\mathbf{H}$ unchanged, or a decoupled perturbed unitary similarity with
backward error $2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularize_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I) (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (regularize (O := O) (Q := Q)).body
      (Env.frame [n + 1, k] [a, rd, c, thr, a, s, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1)
      (fun m => m.Live [a, rd, c, thr, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
        f.2 < m.store.len f.1)
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f)
      (φse + φ / 2) := by
  unfold regularize
  refine ((regularizeWith_pwrites_at hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU hk0 hk has haf hsf
    hio hH hV hHV hκ hBk hω hψ hSH hgap hR hφ hφ1 hβ hdη hnu huo huo1 hxu hbound hthrω
    (hSE.randomSmallEigContractAt k 0 0 S []) (qw := rd)
    (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega)).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) ?_).mono ?_ le_rfl (fun _ h => h) le_rfl
  · rintro μ ⟨hl, -⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl ⊢
    tauto
  · rintro μ ⟨hl, hA, hrest⟩
    refine ⟨?_, hA, by simp, hrest⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl ⊢
    tauto

end Assembly

end NLAlib.ShiftedQR
