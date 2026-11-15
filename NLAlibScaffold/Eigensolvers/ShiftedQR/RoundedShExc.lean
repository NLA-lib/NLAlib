/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedShTrial
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedRegularize

/-!
# The exceptional branch of the rounded shifting strategy

When the promising shift $r$ of `Sh` ([BanksGarzaVargasSrivastava2022, Lemma 5.4]) stagnates,
the exceptional shifts of `Exc` around $r$ (Lemma 5.3 there) are tried in turn
(`NLAlib.ShiftedQR.shTrials`). This file has the exceptional branch: the rounded radius and
potential threshold, the random shifts, the trials, and the mathematics that one shift passes.
The random shifts are a family of probabilistic blocks, one per centre and radius; their outcome
is read through a measurable set of memory pairs (`NLAlib.Ops.PWrites.pstep_of_forall`).

## Main definitions

* `NLAlib.ShiftedQR.shExcInit`, `NLAlib.ShiftedQR.shExc`: the programs.

## Main results

* `NLAlib.norm_toLp_inv_aeval_replicate_last_pos`,
  `NLAlib.measurable_norm_toLp_inv_aeval_replicate_last`: the last row of
  $(\mathbf{H} - s)^{-k}$, nonzero and measurable in $s$.
* `NLAlib.ShiftedQR.excRadius_window`: the rounded exceptional radius is in the window of
  `Exc`.
* `NLAlib.ShiftedQR.exists_mem_le_norm_inv_pow_of_excShifts`: the stored exceptional shifts
  contain a contracting shift.
* `NLAlib.ShiftedQR.shTrial_good`: a contracting shift passes the trial.
* `NLAlib.ShiftedQR.shExcInit_writes`: the start of the branch.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The last row of the inverse of a matrix with nonzero determinant is nonzero. -/
theorem norm_toLp_inv_apply_pos {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.det ≠ 0)
    (i : Fin (n + 1)) : 0 < ‖WithLp.toLp 2 (A⁻¹ i)‖ := by
  refine (norm_nonneg _).lt_of_ne fun h0 => ?_
  have hrow : A⁻¹ i = 0 := by
    have := (norm_eq_zero.mp h0.symm)
    simpa using congrArg WithLp.ofLp this
  have hdet : A⁻¹.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i fun j => by
    simp [hrow]
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdet
  exact hA (inv_eq_zero.mp hdet)

/-- The last row of $(\mathbf{H} - r)^{-k}$ is nonzero when $r$ is no eigenvalue of a
diagonalisable $\mathbf{H}$. -/
theorem norm_toLp_inv_aeval_replicate_last_pos {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) {r : ℂ}
    (hne : ∀ i, e i ≠ r) (k : ℕ) :
    0 < ‖WithLp.toLp 2
      ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖ := by
  refine norm_toLp_inv_apply_pos ?_ _
  rw [aeval_shiftPoly_replicate, Matrix.det_pow]
  exact pow_ne_zero _ (det_sub_smul_one_ne_zero_of_forall_ne hV hHV hne)

/-- The norm of the last row of $(\mathbf{H} - s)^{-k}$ is a measurable function of $s$. -/
theorem measurable_norm_toLp_inv_aeval_replicate_last (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (k : ℕ) : Measurable fun s : ℂ => ‖WithLp.toLp 2
      ((Polynomial.aeval H (shiftPoly (List.replicate k s)))⁻¹ (Fin.last n))‖ := by
  have hc : Continuous fun s : ℂ =>
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ^ k := by fun_prop
  have hinv : Measurable fun s : ℂ =>
      ((H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ^ k)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.measurable.inv).smul hc.matrix_adjugate.measurable
  simp only [aeval_shiftPoly_replicate]
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_apply (Fin.last n) |>.comp hinv) |>.norm

end NLAlib

namespace NLAlib.ShiftedQR

open Ops

/-- **The rounded exceptional radius is in the window of `Exc`**
([BanksGarzaVargasSrivastava2022, line 1 of `Exc`], with the window of the errata N2): on a
machine with the standard model at $10^5k\boldsymbol{u} \le 1$, $k \ge 1$, for $p$ within
$20\boldsymbol{u}$, relatively, of $\psi \ge 0$ and $X \ge 0$, the rounded product
$\tilde R = \mathrm{fl}(2^{1/k}X \cdot p)$ satisfies
$1.998^{1/k}X\psi \le \tilde R \le 2.002^{1/k}X\psi$. -/
theorem excRadius_window {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {k : ℕ} (hk : 0 < k)
    (hku : 100000 * k * u ≤ 1) {X ψ p : ℝ} (hX : 0 ≤ X) (hψ : 0 ≤ ψ)
    (hp : |p - ψ| ≤ 20 * u * ψ) :
    (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * X * ψ ≤ M.mul ((2 : ℝ) ^ ((k : ℝ)⁻¹) * X) p ∧
      M.mul ((2 : ℝ) ^ ((k : ℝ)⁻¹) * X) p ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * X * ψ := by
  have hu0 := hM.roundoff_nonneg
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have hm := hM.mul ((2 : ℝ) ^ ((k : ℝ)⁻¹) * X) p
  simp only [id] at hm
  set c := (2 : ℝ) ^ ((k : ℝ)⁻¹) * X
  have hc : 0 ≤ c := by positivity
  have hplo : (1 - 20 * u) * ψ ≤ p := by linarith [(abs_le.mp hp).1]
  have hphi : p ≤ (1 + 20 * u) * ψ := by linarith [(abs_le.mp hp).2]
  have hp0 : 0 ≤ p := le_trans (by nlinarith) hplo
  rw [abs_of_nonneg (mul_nonneg hc hp0)] at hm
  have hku' : (k : ℝ) * u ≤ 0.00001 := by nlinarith
  have hu1 : u ≤ 0.00001 := by nlinarith
  -- the factors $0.999^{1/k} \le 1 - 0.001/k$ and $1 + 0.0005/k \le 1.001^{1/k}$
  have hlo : (0.999 : ℝ) ^ ((k : ℝ)⁻¹) ≤ 1 - 0.001 / k := by
    have := rpow_one_add_le_one_add_mul_self (s := -0.001) (by norm_num)
      (p := (k : ℝ)⁻¹) (by positivity) (inv_le_one_of_one_le₀ hk1)
    rw [show (1 : ℝ) + -0.001 = 0.999 by norm_num] at this
    rw [div_eq_inv_mul]; linarith
  have hhi : 1 + 0.0005 / (k : ℝ) ≤ (1.001 : ℝ) ^ ((k : ℝ)⁻¹) := by
    have hb := one_add_pow_le_one_add_two_mul (u := 0.0005 / (k : ℝ)) (by positivity) (N := k)
      (by rw [mul_div_cancel₀ _ hk0.ne']; norm_num)
    rw [mul_assoc, mul_div_cancel₀ _ hk0.ne'] at hb
    have := Real.rpow_le_rpow (by positivity) hb (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) hk.ne', show (1 : ℝ) + 2 * 0.0005 = 1.001 by
      norm_num] at this
  have e1 : (1.998 : ℝ) ^ ((k : ℝ)⁻¹) = (0.999 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have e2 : (2.002 : ℝ) ^ ((k : ℝ)⁻¹) = (1.001 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hcψ : 0 ≤ c * ψ := mul_nonneg hc hψ
  have hdk : (0.001 : ℝ) / k * 1 ≥ 21 * u := by
    rw [ge_iff_le, mul_one, le_div_iff₀ hk0]; nlinarith
  have hdk' : (0.0005 : ℝ) / k ≥ 22 * u := by
    rw [ge_iff_le, le_div_iff₀ hk0]; nlinarith
  constructor
  · rw [e1, show (0.999 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) * X * ψ =
      (0.999 : ℝ) ^ ((k : ℝ)⁻¹) * (c * ψ) by ring]
    have h1 : (1 - u) * (1 - 20 * u) * (c * ψ) ≤ M.mul c p := by
      have : (1 - u) * (c * ((1 - 20 * u) * ψ)) ≤ (1 - u) * (c * p) := by
        have : 0 ≤ 1 - u := by linarith
        gcongr
      nlinarith [(abs_le.mp hm).1]
    have h2 : 1 - 0.001 / (k : ℝ) ≤ (1 - u) * (1 - 20 * u) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (hlo.trans h2) hcψ]
  · rw [e2, show (1.001 : ℝ) ^ ((k : ℝ)⁻¹) * 2 ^ ((k : ℝ)⁻¹) * X * ψ =
      (1.001 : ℝ) ^ ((k : ℝ)⁻¹) * (c * ψ) by ring]
    have h1 : M.mul c p ≤ (1 + u) * (1 + 20 * u) * (c * ψ) := by
      have : (1 + u) * (c * p) ≤ (1 + u) * (c * ((1 + 20 * u) * ψ)) := by gcongr
      nlinarith [(abs_le.mp hm).2]
    have h2 : (1 + u) * (1 + 20 * u) ≤ 1 + 0.0005 / (k : ℝ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (h2.trans hhi) hcψ]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

/-- The start of the exceptional branch of `Sh`: the flag `Fl` is $2$ (no step yet), the
search word `Gw` is $1$, the threshold $\mathrm{fl}(c_p\tilde\psi)$ of the potential test goes
to `Pt` and the radius $\mathrm{fl}(c_r\tilde\psi)$ to `Rt` (which held $\tilde\psi$). The
interface is `[] (Cr, Cp, Rt) → (Rt, Pt, Gw, Fl)`. -/
def shExcInit : Impl O Q := opsImpl% [] (Cr, Cp, Rt) → (Rt, Pt, Gw, Fl) {
  call (Has.inj (ScalarOp.lit 2)) [] () → (Fl);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Gw);
  call (Has.inj ScalarOp.mul) [] (Cp, Rt) → (Pt);
  call (Has.inj ScalarOp.mul) [] (Cr, Rt) → (Rt)
}

/-- The exceptional branch of `Sh`: its start (`NLAlib.ShiftedQR.shExcInit`), the exceptional
shifts around the centre `Z` (`NLAlib.ShiftedQR.excShifts`, with the radius `Rt`, the
translate factor `Cw` and the net `G`) into `Ss`, and the trials (`NLAlib.ShiftedQR.shTrials`).
The interface is
`[N, k, q, n0] (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, T, SR, Ds, Rg, P2, Ss) → (A, Gw, Fl)`. -/
def shExc : Impl O Q :=
  opsImpl% [N, k, q, n0] (A, Z, Cr, Cw, Cp, G, Thr, Rt, Pt, T, SR, Ds, Rg, P2, Ss) →
      (A, Gw, Fl) {
    run shExcInit.body [] (Cr, Cp, Rt, Rt, Pt, Gw, Fl);
    run (excShifts (O := O) (Q := Q)).body [n0] (Z, Rt, Cw, G, Ss);
    run shTrials.body [N, k, q, n0] (A, Ss, Thr, Pt, T, SR, Ds, Rg, P2, A, Gw, Fl)
  }

end Program

section Init

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

omit [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The start of the exceptional branch on a scalar machine with exact natural literals up to
$2$: from the words $c_r$, $c_p$ and $p$ at `Cr`, `Cp`, `Rt`, `NLAlib.ShiftedQR.shExcInit`
stores $\mathrm{fl}(c_r p)$ at `Rt`, $\mathrm{fl}(c_p p)$ at `Pt`, $1$ at `Gw` and $2$ at
`Fl`, and writes only these. -/
theorem shExcInit_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {u : ℝ}
    (hM : StdModel u id M) (hNat : IsExactNatLit id M 2) {τ : Tape ℝ} {m : Mem ℝ}
    {cr cp rt pt gw f : ℕ × ℕ} {crv cpv p : ℝ} (hcr : m.store.get cr.1 cr.2 = some crv)
    (hcp : m.store.get cp.1 cp.2 = some cpv) (hrt : m.store.get rt.1 rt.2 = some p)
    (hpt : pt.2 < m.store.len pt.1) (hgw : gw.2 < m.store.len gw.1)
    (hf : f.2 < m.store.len f.1)
    (hW : Fp.Disj (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock gw.1 gw.2 1 ⊔ Store.inBlock pt.1 pt.2 1)
      (Store.inBlock cr.1 cr.2 1 ⊔ Store.inBlock cp.1 cp.2 1 ⊔ Store.inBlock rt.1 rt.2 1))
    (hfg : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock gw.1 gw.2 1))
    (hfgp : Fp.Disj (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock gw.1 gw.2 1)
      (Store.inBlock pt.1 pt.2 1)) :
    Writes .total I τ (shExcInit (O := O) (Q := Q)).body
      (Env.frame [] [cr, cp, rt, rt, pt, gw, f])
      (Store.inBlock rt.1 rt.2 1 ⊔ Store.inBlock pt.1 pt.2 1 ⊔ Store.inBlock gw.1 gw.2 1 ⊔
        Store.inBlock f.1 f.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get rt.1 rt.2 = some (M.mul crv p) ∧
        m'.store.get pt.1 pt.2 = some (M.mul cpv p) ∧ m'.store.get gw.1 gw.2 = some 1 ∧
        m'.store.get f.1 f.2 = some 2) m := by
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have h2 : M.lit 2 = 2 := by simpa using hNat 2 le_rfl
  have hk : ∀ {F G : Fp} {b : ℕ × ℕ} {v : ℝ} {μ μ' : Mem ℝ}, μ.store.EqOff F μ'.store →
      Fp.Disj F G → Store.inBlock b.1 b.2 1 ≤ G → μ.store.get b.1 b.2 = some v →
      μ'.store.get b.1 b.2 = some v := fun hfr hd hb hv =>
    hfr.keep (Store.readsOnly_get _ _ _) (hd.mono le_rfl hb) hv
  unfold shExcInit
  refine (writes_call_const (hS (.lit 2)) (z := f) rfl trivial hf).seq_le (by fp_sub) ?_
  rintro m₁ hfr₁ ⟨hp₁, hF₁⟩
  refine (writes_call_const (hS (.lit 1)) (z := gw) rfl trivial
    (by rw [hfr₁.len_eq]; exact hgw)).seq_le (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨hp₂, hG₂⟩
  have hcp₂ := hk hfr₂ (hW.mono (by fp_sub) le_rfl) (by fp_sub) (hk hfr₁ (hW.mono (by fp_sub)
    le_rfl) (by fp_sub) hcp)
  have hrt₂ := hk hfr₂ (hW.mono (by fp_sub) le_rfl) (by fp_sub) (hk hfr₁ (hW.mono (by fp_sub)
    le_rfl) (by fp_sub) hrt)
  have hcr₂ := hk hfr₂ (hW.mono (by fp_sub) le_rfl) (by fp_sub) (hk hfr₁ (hW.mono (by fp_sub)
    le_rfl) (by fp_sub) hcr)
  refine (writes_call_bin (hS .mul) (x := cp) (y := rt) (z := pt) rfl rfl trivial hcp₂ hrt₂ rfl
    (fun _ => ⟨by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, Store.lt_length_of_get hcp,
      Store.lt_length_of_get hrt, Store.lt_length_of_lt_len hpt],
      by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hpt⟩)).seq_le (by fp_sub) ?_
  rintro m₃ hfr₃ ⟨hp₃, hP₃⟩
  have hrt₃ := hk hfr₃ (hW.mono (by fp_sub) le_rfl) (by fp_sub) hrt₂
  have hcr₃ := hk hfr₃ (hW.mono (by fp_sub) le_rfl) (by fp_sub) hcr₂
  refine (writes_call_bin (hS .mul) (x := cr) (y := rt) (z := rt) rfl rfl trivial hcr₃ hrt₃ rfl
    (fun _ => ⟨by simp [Mem.Live, Store.lt_length_of_get hcr₃, Store.lt_length_of_get hrt₃],
      Store.lt_len_of_get hrt₃⟩)).mono (by fp_sub) ?_
  rintro m₄ hfr₄ ⟨hp₄, hR₄⟩
  refine ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), hR₄,
    hk hfr₄ (hW.symm.mono (by fp_sub) le_rfl) (by fp_sub) hP₃, ?_, ?_⟩
  · refine hk hfr₄ (hW.symm.mono (by fp_sub) le_rfl) (by fp_sub)
      (hk hfr₃ hfgp.symm (by fp_sub) (by rw [hG₂, h1]))
  · refine hk hfr₄ (hW.symm.mono (by fp_sub) le_rfl) (by fp_sub)
      (hk hfr₃ hfgp.symm (by fp_sub) (hk hfr₂ hfg.symm le_rfl (by rw [hF₁, h2])))

end Init

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

/-- The outcomes of the exceptional shifts that `Sh` uses, as pairs of a memory before and after:
the frame `F`, an initialised column of $n_0$ complex words at `b`, one of them a shift $s$ with
$\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - s)^{-k}\| \ge K$, all at distance at least $d$ from
every $e_i$ and of modulus at most $c$. They form a measurable set. -/
theorem measurableSet_excOutcome {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (k n0 : ℕ)
    (e : Fin (n + 1) → ℂ) (K d c : ℝ) (b : ℕ × ℕ) (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * (1 * n0), (x.2.store.get b.1 (b.2 + j)).isSome) ∧
      (∃ j : Fin n0, K ≤ ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly
        (List.replicate k (storedMatrix b n0 1 x.2.store j 0))))⁻¹ (Fin.last n))‖) ∧
      (∀ j : Fin n0, ∀ i, d ≤ ‖e i - storedMatrix b n0 1 x.2.store j 0‖) ∧
      ∀ j : Fin n0, ‖storedMatrix b n0 1 x.2.store j 0‖ ≤ c} := by
  have hcol (j : Fin n0) : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix b n0 1 x.2.store j 0 :=
    (Matrix.measurable_apply j (0 : Fin 1)).comp ((measurable_storedMatrix b n0 1).comp
      measurable_snd)
  have hN := measurable_norm_toLp_inv_aeval_replicate_last H k
  simp only [Set.ofPred_and]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome b _)).inter
    ((?_ : MeasurableSet _).inter ((?_ : MeasurableSet _).inter ?_)))
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun j => measurableSet_le measurable_const (hN.comp (hcol j))
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const ((hcol j).const_sub _).norm
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (hcol j).norm measurable_const

/-- A column of complex words stored as interleaved pairs is read back entrywise by
`NLAlib.ShiftedQR.storedMatrix`. -/
theorem storedMatrix_col_of_readBlock {s : Store ℝ} {b : ℕ × ℕ} {zs : List ℂ}
    (h : s.readBlock b.1 b.2 (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]))
    (j : Fin zs.length) : storedMatrix b zs.length 1 s j 0 = zs[j] := by
  obtain ⟨h1, h2⟩ := get_of_readBlock_flatMap_pair h j.isLt
  apply Complex.ext <;> simp [storedMatrix, h1, h2]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- **The stored exceptional shifts contain a contracting shift** (the deterministic core of
`Exc`, [BanksGarzaVargasSrivastava2022, Lemma 5.3], corrected as in the errata G13, read on the
shifts `NLAlib.ShiftedQR.excShifts` stores): let
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\kappa(\mathbf{V}) \le B$, the $k \ge 2$ shifts `ss` $\theta$-optimal ($\theta \ge 1$), none an
eigenvalue, $r$ an $\alpha$-promising one ($\alpha \ge 1$) that stagnates with the ratio
$\xi = 0.998(1 - \gamma)$, $0 < \gamma < 1$, $\psi_k(\mathbf{H}) > 0$, the radius $\tilde R$
in the window $[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi_k(\mathbf{H})$,
$\varepsilon = (\xi(1 - \gamma)/((13B^4)^{1/k}\alpha^2\theta^2))^{k/(k-1)} \le 1/2$, and a list
of at most $9/\varepsilon^2$ shifts covering $\mathbb{D}(r, \tilde R)$ at radius
$\varepsilon\tilde R$, each at distance at least $\delta > 0$ from every eigenvalue. Then one
of them, $s$, has $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - s)^{-k}\| \ge
((1 - \gamma)\psi_k(\mathbf{H}))^{-k}$. -/
theorem exists_mem_le_norm_inv_pow_of_excShifts {B θ α γ R ε δ : ℝ} {k : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss zs : List ℂ} {r : ℂ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (hlen : ss.length = k) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hopt : IsOptimalRitzValues θ H ss) (hr : IsPromisingRitzValue α V e ss r)
    (hd : ∀ i, ∀ s ∈ ss, e i ≠ s) (hψ : 0 < hessenbergPotential k H) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hτ : ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹
      (Fin.last n))‖ ≤ (0.998 * (1 - γ) * hessenbergPotential k H)⁻¹ ^ k)
    (hRlo : (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H ≤ R)
    (hRhi : R ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2)
    (hcard : (zs.length : ℝ) ≤ 9 / ε ^ 2)
    (hcover : ∀ z : ℂ, ‖z - r‖ ≤ R → ∃ s ∈ zs, ‖z - s‖ ≤ ε * R) (hδ : 0 < δ)
    (hdist : ∀ s ∈ zs, ∀ i, δ ≤ ‖e i - s‖) :
    ∃ s ∈ zs, ((1 - γ) * hessenbergPotential k H)⁻¹ ^ k ≤
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k s)))⁻¹ (Fin.last n))‖ := by
  classical
  obtain ⟨s, hs, hle⟩ := exists_mem_le_norm_inv_pow_of_covers (S := zs.toFinset) (ξ := 0.998 * (1 - γ))
    hk hkn hlen hV hHV hκ hopt hr hd hψ hγ hγ1 (by nlinarith) hθ hα hτ hRlo hRhi hε hε2
    (fun z hz => by
      obtain ⟨s, hs, h⟩ := hcover z hz
      exact ⟨s, List.mem_toFinset.mpr hs, h⟩)
    ((Nat.cast_le.mpr (List.toFinset_card_le zs)).trans hcard)
    (fun s hs i he => by
      have := hdist s (List.mem_toFinset.mp hs) i
      rw [he, sub_self, norm_zero] at this
      linarith)
  exact ⟨s, List.mem_toFinset.mp hs, hle⟩

/-- **A contracting exceptional shift passes the trial**: under the hypotheses of
`NLAlib.IsStableQRChain.exists_norm_subdiag_lt_or_potential_pow_mul_le` for the shift $s$ (with
$x = 300(n+1)^2\boldsymbol{u}$), if $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - s)^{-k}\| \ge
((1 - \gamma)\psi)^{-k}$, $\psi = \psi_k(\mathbf{H}) > 0$, $\gamma < 1$, the word $p_H$ is within
$20\boldsymbol{u}$, relatively, of $\psi$, and $2 \cdot 10^5\boldsymbol{u} \le 1$, then every rounded
step with $s$ repeated has a bottom subdiagonal entry of modulus below $\omega$, or every value
within $20\boldsymbol{u}$, relatively, of its potential is below $\mathrm{fl}(1.0015(1 - \gamma)p_H)$. -/
theorem shTrial_good {M : Machine ℝ} {u C B S d ω γ pH : ℝ} (hM : StdModel u id M) {k : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {s : ℂ}
    (hu : 200000 * u ≤ 1) (hC : 0 ≤ C) (hd : 0 < d) (hω : 0 < ω) (hk : 0 < k) (hkn : k ≤ n)
    (hH0 : H ≠ 0) (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hS : specNorm H ≤ S) (hs : ‖s‖ ≤ C * specNorm H) (hdist : ∀ i, d ≤ ‖e i - s‖)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hγ1 : γ < 1) (hψ : 0 < hessenbergPotential k H)
    (hpH : |pH - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H)
    (hN : ((1 - γ) * hessenbergPotential k H)⁻¹ ^ k ≤
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k s)))⁻¹ (Fin.last n))‖)
    (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    (hch : IsStableQRChain (300 * (n + 1) ^ 2 * u) H (List.replicate k s) H' Rs) :
    (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ < ω) ∨
      ∀ p : ℝ, |p - hessenbergPotential k H'| ≤ 20 * u * hessenbergPotential k H' →
        p < M.mul (1.0015 * (1 - γ)) pH := by
  have hu0 := hM.roundoff_nonneg
  rcases hch.exists_norm_subdiag_lt_or_potential_pow_mul_le (by positivity) hC hd hω hk hkn hH0 hH
    hV hHV hκ hS hs hdist hxu hbound with h | h
  · exact Or.inl h
  right
  intro p hp
  have hg : 0 < (1 - γ) * hessenbergPotential k H := mul_pos (by linarith) hψ
  set c := (1 - γ) * hessenbergPotential k H
  have hA0 : 0 ≤ hessenbergPotential k H' ^ k := by
    have := hessenbergPotential_nonneg k H'; positivity
  have h1 : hessenbergPotential k H' ^ k * c⁻¹ ^ k ≤ 1.0011 ^ k :=
    (mul_le_mul_of_nonneg_left hN hA0).trans h
  have hle : hessenbergPotential k H' ^ k ≤ (1.0011 * c) ^ k := by
    calc hessenbergPotential k H' ^ k = hessenbergPotential k H' ^ k * c⁻¹ ^ k * c ^ k := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hg.ne', one_pow, mul_one]
      _ ≤ 1.0011 ^ k * c ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := (mul_pow _ _ _).symm
  have hle' := le_of_pow_le_pow_left₀ hk.ne' (by positivity) hle
  exact lt_of_potential_contract hu0 hu hγ1 hψ hp hpH (hM.mul _ _) (by linarith)

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- A column of complex words of length $N$ stored as interleaved pairs is read back entrywise. -/
theorem storedMatrix_col_of_readBlock' {s : Store ℝ} {b : ℕ × ℕ} {N : ℕ} {zs : List ℂ}
    (hlen : zs.length = N)
    (h : s.readBlock b.1 b.2 (2 * N) = some (zs.flatMap fun z => [z.re, z.im])) (j : Fin N) :
    storedMatrix b N 1 s j 0 = zs[(j : ℕ)]'(hlen ▸ j.isLt) := by
  subst hlen
  exact storedMatrix_col_of_readBlock h j

/-- The words `Sh` with scratch at `L, …, L + 11` reads, and the room it writes into: the
matrix $\mathbf{H}$ at `a`, the $k$ shifts `ss` at `s`, the words $c_g$, $c_r$, $c_w$, $c_p$
at `wg`, `wr`, `ww`, `wp`, the net `NLAlib.ShiftedQR.excNet ε` at `g`, the threshold word $t$
at `thr`, room for the flag at `f`, and twelve scratch buffers of the lengths of
`NLAlib.ShiftedQR.shStep` above the $L$ buffers of the caller. -/
def ShCtx (L : ℕ) (k : ℕ) (ε : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ)
    (cg cr cw cp tv : ℝ) (a s wg wr ww wp g thr f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  HoldsMatrix a H m.store ∧
    m.store.readBlock s.1 s.2 (2 * k) = some (ss.flatMap fun z => [z.re, z.im]) ∧
    m.store.get wg.1 wg.2 = some cg ∧ m.store.get wr.1 wr.2 = some cr ∧
    m.store.get ww.1 ww.2 = some cw ∧ m.store.get wp.1 wp.2 = some cp ∧
    m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
      some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧
    m.store.get thr.1 thr.2 = some tv ∧ f.2 < m.store.len f.1 ∧ m.store.length = L + 12 ∧
    m.store.len L = 2 ∧ m.store.len (L + 1) = 1 ∧ m.store.len (L + 2) = 1 ∧
    m.store.len (L + 3) = 1 ∧ m.store.len (L + 4) = 1 ∧
    m.store.len (L + 5) = 2 * ((n + 1) * (n + 1)) ∧ m.store.len (L + 6) = 2 * k ∧
    m.store.len (L + 7) = 2 * k ∧ m.store.len (L + 8) = 5 ∧ m.store.len (L + 9) = 1 ∧
    m.store.len (L + 10) = 2 * (excNet ε).length ∧ m.store.len (L + 11) = 1

/-- The context survives a write apart from the matrix and the input words. -/
theorem ShCtx.of_eqOff {L k : ℕ} {ε : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ss : List ℂ} {cg cr cw cp tv : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} {m m' : Mem ℝ} {F : Fp}
    (h : ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m)
    (hfr : m.store.EqOff F m'.store)
    (hF : Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
      Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
      Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔ Store.inBlock thr.1 thr.2 1)) :
    ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m' := by
  obtain ⟨hA, hs, hg, hr, hw, hp, hG, ht, hf, hlen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11⟩ := h
  refine ⟨hA.of_eqOff hfr (hF.mono le_rfl (by fp_sub)),
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hF.mono le_rfl (by fp_sub)) hs,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hg,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hr,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hw,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hp,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hF.mono le_rfl (by fp_sub)) hG,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) ht, ?_⟩
  simp only [hfr.len_eq, hfr.length_eq]
  exact ⟨hf, hlen, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The views of `Sh` are apart: the matrix and the flag from each other and from the input
words, all below the scratch handle $L$. -/
structure ShViews (L n k : ℕ) (ε : ℝ) (a s wg wr ww wp g thr f : ℕ × ℕ) : Prop where
  /-- Every view is below the scratch handle. -/
  lt : a.1 < L ∧ s.1 < L ∧ wg.1 < L ∧ wr.1 < L ∧ ww.1 < L ∧ wp.1 < L ∧ g.1 < L ∧ thr.1 < L ∧
    f.1 < L
  /-- The matrix and the flag are apart. -/
  af : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1)
  /-- The outputs are apart from the inputs. -/
  io : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
    (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔
      Store.inBlock ww.1 ww.2 1 ⊔ Store.inBlock wp.1 wp.2 1 ⊔
      Store.inBlock g.1 g.2 (2 * (excNet ε).length) ⊔ Store.inBlock thr.1 thr.2 1)

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- **The outcome of the exceptional shifts, read from the memory**: under the hypotheses of
`NLAlib.ShiftedQR.exists_mem_le_norm_inv_pow_of_excShifts` (with $\delta = \varepsilon\tilde R
\sqrt{\varphi/(11(n + 1))}/4$), if $N$ shifts are stored as pairs at `b`, cover
$\mathbb{D}(r, \tilde R)$ at radius $\varepsilon\tilde R$, are at most $9/\varepsilon^2$, at
distance at least $\delta$ from every eigenvalue and in $\mathbb{D}(r, 2.1\tilde R)$, then the
column read at `b` is initialised, contains a contracting shift, and its entries are at distance
at least $d \le \varepsilon\,1.998^{1/k}\theta\alpha B^{1/k}\psi_k(\mathbf{H})
\sqrt{\varphi/(11(n + 1))}/4$ from every eigenvalue and of modulus at most $C\|\mathbf{H}\|_2$,
for $\lvert r\rvert \le 1.1\|\mathbf{H}\|_2$ and
$1.1 + 2.1 \cdot 2.002^{1/k}\theta\alpha B^{1/k} \le C$. -/
theorem excOutcome_of_excShifts {s : Store ℝ} {b : ℕ × ℕ} {N : ℕ} {zs : List ℂ}
    {B θ α γ R ε φ d C : ℝ} {k : ℕ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hk : 2 ≤ k) (hkn : k ≤ n) (hlen : ss.length = k) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hopt : IsOptimalRitzValues θ H ss) (hr : IsPromisingRitzValue α V e ss r)
    (hd0 : ∀ i, ∀ s ∈ ss, e i ≠ s) (hψ : 0 < hessenbergPotential k H) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hτ : ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹
      (Fin.last n))‖ ≤ (0.998 * (1 - γ) * hessenbergPotential k H)⁻¹ ^ k)
    (hRlo : (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H ≤ R)
    (hRhi : R ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4) (hd' : 0 < d)
    (hrH : ‖r‖ ≤ 1.1 * specNorm H)
    (hC : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hzl : zs.length = N)
    (hblk : s.readBlock b.1 b.2 (2 * N) = some (zs.flatMap fun z => [z.re, z.im]))
    (hcard : (zs.length : ℝ) ≤ 9 / ε ^ 2)
    (hcover : ∀ z : ℂ, ‖z - r‖ ≤ R → ∃ s ∈ zs, ‖z - s‖ ≤ ε * R)
    (hdist : ∀ s ∈ zs, ∀ i, ε * R * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4 ≤ ‖e i - s‖)
    (hnear : ∀ s ∈ zs, ‖s - r‖ ≤ 2.1 * R) :
    (∀ j < 2 * (1 * N), (s.get b.1 (b.2 + j)).isSome) ∧
      (∃ j : Fin N, ((1 - γ) * hessenbergPotential k H)⁻¹ ^ k ≤ ‖WithLp.toLp 2
        ((Polynomial.aeval H (shiftPoly (List.replicate k (storedMatrix b N 1 s j 0))))⁻¹
          (Fin.last n))‖) ∧
      (∀ j : Fin N, ∀ i, d ≤ ‖e i - storedMatrix b N 1 s j 0‖) ∧
      ∀ j : Fin N, ‖storedMatrix b N 1 s j 0‖ ≤ C * specNorm H := by
  have hcol := storedMatrix_col_of_readBlock' hzl hblk
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hX : 0 ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) := by positivity
  have hψH := hessenbergPotential_le_specNorm (by omega) hkn H
  have hmem : ∀ j : Fin N, storedMatrix b N 1 s j 0 ∈ zs := fun j => by
    rw [hcol j]; exact List.getElem_mem _
  have hRd : d ≤ ε * R * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4 := by
    have hε0 : 0 ≤ ε := by rw [hε]; positivity
    refine hd.trans ?_
    gcongr
  refine ⟨fun j hj => ?_, ?_, fun j i => hRd.trans (hdist _ (hmem j) i), fun j => ?_⟩
  · rw [Option.isSome_iff_exists]
    exact ⟨_, Store.get_of_readBlock hblk (j := j) (by omega) 0⟩
  · obtain ⟨t, ht, hle⟩ := exists_mem_le_norm_inv_pow_of_excShifts hk hkn hlen hV hHV hκ hopt hr
      hd0 hψ hγ hγ1 hθ hα hτ hRlo hRhi hε hε2 hcard hcover (lt_of_lt_of_le hd' hRd) hdist
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    exact ⟨⟨i, hzl ▸ hi⟩, by rw [hcol]; exact hle⟩
  · have h1 := hnear _ (hmem j)
    have h2 := norm_le_norm_add_norm_sub' (storedMatrix b N 1 s j 0) r
    have h3 : R ≤ (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * specNorm H :=
      hRhi.trans (mul_le_mul_of_nonneg_left hψH hX)
    have h4 := mul_le_mul_of_nonneg_right hC (specNorm_nonneg H)
    nlinarith

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

variable {n : ℕ}

/-- The state of `Sh` before the exceptional shifts: the context, the promising centre $r$ at
`L` (a pair), stagnating with the ratio $0.998(1 - \gamma)$; the words
$\mathrm{fl}(c_r p)$ at `L + 1` and $\mathrm{fl}(c_p p)$ at `L + 2` for a $p$ within
$20\boldsymbol{u}$, relatively, of $\psi_k(\mathbf{H})$; the search word $1$ at `L + 11` and
the flag $2$. -/
def ShExcMid1 (M : Machine ℝ) (u : ℝ) (L k : ℕ) (ε : ℝ)
    (H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : Fin (n + 1) → ℂ) (ss : List ℂ)
    (α γ cg cr cw cp tv : ℝ) (a s wg wr ww wp g thr f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m ∧
    (∃ r : ℂ, m.store.readBlock L 0 2 = some [r.re, r.im] ∧ IsPromisingRitzValue α V e ss r ∧
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k r)))⁻¹ (Fin.last n))‖ ≤
        (0.998 * (1 - γ) * hessenbergPotential k H)⁻¹ ^ k) ∧
    (∃ p : ℝ, |p - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H ∧
      m.store.get (L + 1) 0 = some (M.mul cr p) ∧ m.store.get (L + 2) 0 = some (M.mul cp p)) ∧
    m.store.get (L + 11) 0 = some 1 ∧ m.store.get f.1 f.2 = some 2

/-- The state of `Sh` after the exceptional shifts: the context, the $n_0$ shifts as pairs at
`L + 10`, one contracting, all at distance at least $d$ from every $e_i$ and of modulus at most
$C\|\mathbf{H}\|_2$; the word $\mathrm{fl}(c_p p)$ at `L + 2`; the search word $1$ and the flag
$2$. -/
def ShExcMid2 (M : Machine ℝ) (u : ℝ) (L k : ℕ) (ε : ℝ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : Fin (n + 1) → ℂ) (ss : List ℂ)
    (γ cg cr cw cp tv d C : ℝ) (a s wg wr ww wp g thr f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  ShCtx L k ε H ss cg cr cw cp tv a s wg wr ww wp g thr f m ∧
    (∃ zs : Fin (excNet ε).length → ℂ,
      (∀ j : Fin (excNet ε).length,
        m.store.readBlock (L + 10) (2 * j) 2 = some [(zs j).re, (zs j).im]) ∧
      (∃ j, ((1 - γ) * hessenbergPotential k H)⁻¹ ^ k ≤
        ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k (zs j))))⁻¹
          (Fin.last n))‖) ∧
      (∀ j i, d ≤ ‖e i - zs j‖) ∧ ∀ j, ‖zs j‖ ≤ C * specNorm H) ∧
    (∃ p : ℝ, |p - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H ∧
      m.store.get (L + 2) 0 = some (M.mul cp p)) ∧
    m.store.get (L + 11) 0 = some 1 ∧ m.store.get f.1 f.2 = some 2

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

variable {n : ℕ}

section Random

variable {O Q : Type} [Has ScalarOp O] [Has DiskSampleOp O]

/-- **The exceptional shifts of `Sh` as a probabilistic block**: under a measurable, tape-local
interpretation on a scalar machine with the standard model at $10^5k\boldsymbol{u} \le 1$ and an
exact polar sampler on a stream `s₀` uniform on $[0, 1]$, from the state
`NLAlib.ShiftedQR.ShExcMid1` the shifts `NLAlib.ShiftedQR.excShifts` reach the state
`NLAlib.ShiftedQR.ShExcMid2`, except with probability at most $\varphi$, $0 < \varphi \le 1/5$,
under the hypotheses of `NLAlib.ShiftedQR.excOutcome_of_excShifts` on the data, the words
$c_r = 2^{1/k}\theta\alpha B^{1/k}$ and $c_w = \varepsilon/2$, and the rounding budget
$6\boldsymbol{u}(1.1\Sigma + 3R_{\mathrm{hi}}) \le \min(0.005, \sqrt{q}/8)\,\varepsilon R_{\mathrm{lo}}$,
$q = \varphi/(11(n + 1))$, for the window $[R_{\mathrm{lo}}, R_{\mathrm{hi}}] =
[1.998^{1/k}, 2.002^{1/k}]\,\theta\alpha B^{1/k}\psi_k(\mathbf{H})$ of the radius. The random
shifts form one probabilistic block per centre and radius; their outcome is the measurable set
`NLAlib.ShiftedQR.measurableSet_excOutcome`. -/
theorem shExcShifts_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) (hS : IsScalar M I)
    (hM : StdModel u id M) {law : ℕ → Measure ℝ} {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {L k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {ε : ℝ} {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {B S θ α γ φ d C cg cr cw cp tv : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} (hlen : ss.length = k) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hopt : IsOptimalRitzValues θ H ss)
    (hd0 : ∀ i, ∀ s ∈ ss, e i ≠ s) (hsH : ∀ s ∈ ss, ‖s‖ ≤ 1.1 * specNorm H)
    (hψ : 0 < hessenbergPotential k H) (hγ : 0 < γ) (hγ1 : γ < 1) (hθ : 1 ≤ θ) (hα : 1 ≤ α)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 * θ ^ 2)) ^
      ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : d ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4) (hd' : 0 < d)
    (hC : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hku : 100000 * k * u ≤ 1)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) *
      hessenbergPotential k H)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α *
        B ^ ((k : ℝ)⁻¹) * hessenbergPotential k H) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hcr : cr = (2 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹))) (hcw : cw = ε / 2) :
    PWrites law I (excShifts (O := O) (Q := Q)).body
      (Env.frame [(excNet ε).length] [(L, 0), (L + 1, 0), ww, g, (L + 10, 0)])
      (Store.inBlock (L + 10) 0 (2 * (excNet ε).length))
      (ShExcMid1 M u L k ε H V e ss α γ cg cr cw cp tv a s wg wr ww wp g thr f)
      (ShExcMid2 M u L k ε H e ss γ cg cr cw cp tv d C a s wg wr ww wp g thr f) φ := by
  classical
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthr, hf⟩, -, -⟩ := hv
  have hu0 := hM.roundoff_nonneg
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hψH := hessenbergPotential_le_specNorm (by omega) hkn H
  set ψ := hessenbergPotential k H
  set Rlo := (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * ψ
  set Rhi := (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * θ * α * B ^ ((k : ℝ)⁻¹) * ψ
  have hRlo0 : 0 < Rlo := by positivity
  have hg : 0 < 1 - γ := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hu1 : u ≤ 0.00001 := by nlinarith
  let ι := {x : ℂ × ℝ // IsPromisingRitzValue α V e ss x.1 ∧
    ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly (List.replicate k x.1)))⁻¹ (Fin.last n))‖ ≤
      (0.998 * (1 - γ) * ψ)⁻¹ ^ k ∧ Rlo ≤ x.2 ∧ x.2 ≤ Rhi}
  have hbud : ∀ x : ι, 6 * u * (‖x.1.1‖ + 3 * x.1.2) ≤ 6 * u * (1.1 * S + 3 * Rhi) := fun x => by
    have h1 := hsH _ x.2.1.1
    have h2 := x.2.2.2.2
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hfam : ∀ x : ι, _ := fun x => excShifts_pwrites (O := O) (Q := Q) hS hM hD hU e
    (r := x.1.1) (R := x.1.2) (lt_of_lt_of_le hRlo0 x.2.2.2.1) hε0 hε2 hφ.le hφ1
    (by linarith)
    ((hbud x).trans (hexc1.trans (by gcongr; exact x.2.2.2.1)))
    ((hbud x).trans (hexc2.trans (by gcongr; exact x.2.2.2.1)))
    (c := (L, 0)) (rt := (L + 1, 0)) (cw := ww) (g := g) (ss := (L + 10, 0))
  have hst := PWrites.pstep_of_forall hI hloc hfam (measurableSet_excOutcome H k
    (excNet ε).length e (((1 - γ) * ψ)⁻¹ ^ k) d (C * specNorm H) (L + 10, 0)
    (Store.inBlock (L + 10) 0 (2 * (excNet ε).length))) (by
      rintro x μ μ' - hfr ⟨zs, hzl, hblk, hcard, hcov, hdist, hnear⟩
      exact ⟨hfr, excOutcome_of_excShifts hk hkn hlen hV hHV hκ hopt x.2.1 hd0 hψ hγ hγ1 hθ hα
        x.2.2.1 x.2.2.2.1 x.2.2.2.2 hε hε2 hφ hd hd' (hsH _ x.2.1.1) hC hzl hblk hcard hcov
        hdist hnear⟩)
  refine PStep.mono hst (fun μ ⟨hctx, ⟨r, hZ, hr, hτ⟩, ⟨p, hp, hRt, hPt⟩, hGw, hF⟩ => ?_)
    (fun μ μ' ⟨hctx, _, ⟨p, hp, _, hPt⟩, hGw, hF⟩ ⟨hfr, hsome, hj, hdist, hnear⟩ => ?_) le_rfl
  · obtain ⟨-, -, -, -, hcw', -, hG, -, -, hlen', -, -, -, -, -, -, -, -, -, -, h10, -⟩ := hctx
    obtain ⟨hlo, hhi⟩ := excRadius_window hM (by omega) hku (X := θ * α * B ^ ((k : ℝ)⁻¹))
      (by positivity) hψ.le hp
    have e1 : (1.998 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹)) * ψ = Rlo := by ring
    have e2 : (2.002 : ℝ) ^ ((k : ℝ)⁻¹) * (θ * α * B ^ ((k : ℝ)⁻¹)) * ψ = Rhi := by ring
    rw [← hcr, e1] at hlo
    rw [← hcr, e2] at hhi
    have h0 := Store.get_of_readBlock hZ (j := 0) (by norm_num) 0
    have h1 := Store.get_of_readBlock hZ (j := 1) (by norm_num) 0
    simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add] at h0 h1
    refine ⟨⟨(r, M.mul cr p), hr, hτ, hlo, hhi⟩, by simp [Mem.Live, hlen']; omega, h0, h1, hRt,
      by rw [hcw', hcw], hG, by simp [h10], by disjoint, by disjoint⟩
  · refine ⟨hfr, hctx.of_eqOff hfr (by disjoint), ⟨fun j => storedMatrix (L + 10, 0)
      (excNet ε).length 1 μ'.store j 0, fun j => ?_, hj, hdist, hnear⟩,
      ⟨p, hp, hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hPt⟩,
      hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hGw,
      hfr.keep (Store.readsOnly_get _ _ _) (by disjoint) hF⟩
    simpa using (holdsMatrix_storedMatrix hsome).read_entry j 0

end Random

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

/-- **The outcome of `Sh`**, with the decoupling rate $\gamma$, the scan threshold $t$ and the
backward error $\varepsilon$: the flag is $1$ and `a` holds an upper Hessenberg perturbed unitary
similarity $\widehat{\mathbf{H}}$ of $\mathbf{H}$ with error $\varepsilon$ that is decoupled at
the bottom (one of its last $k$ subdiagonal entries passes the scan) or has
$\psi_k(\widehat{\mathbf{H}}) \le 1.002(1 - \gamma)\psi_k(\mathbf{H})$. -/
def ShOutcome (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (γ tv ε : ℝ)
    (a f : ℕ × ℕ) (m' : Mem ℝ) : Prop :=
  m'.store.get f.1 f.2 = some 1 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    IsPerturbedUnitarySimilar H H' ε ∧ IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
    ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ 1.002 * (1 - γ) * hessenbergPotential k H)

/-- An accepted trial is the outcome of `Sh`: a backward-stable step with the shift $s$ repeated,
$\lvert s\rvert \le C\|\mathbf{H}\|_2$, accepted against the potential threshold
$\mathrm{fl}(1.0015(1 - \gamma)p_H)$, $p_H$ within $20\boldsymbol{u}$, relatively, of
$\psi_k(\mathbf{H})$, $\gamma \le 1$, $2 \cdot 10^5\boldsymbol{u} \le 1$, with the error
$(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$. -/
theorem shOutcome_of_accepted {M : Machine ℝ} {u x C γ tv pH : ℝ} (hM : StdModel u id M)
    (hu : 200000 * u ≤ 1) (hx : 0 ≤ x) (hC : 0 ≤ C) (hγ1 : γ ≤ 1) {k : ℕ}
    {H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} {a f : ℕ × ℕ} {m' : Mem ℝ}
    (hpH : |pH - hessenbergPotential k H| ≤ 20 * u * hessenbergPotential k H)
    (hs : ‖s‖ ≤ C * specNorm H) (hch : IsStableQRChain x H (List.replicate k s) H' Rs)
    (hH' : IsUpperHessenberg H') (hA : HoldsMatrix a H' m'.store)
    (hf : m'.store.get f.1 f.2 = some 1)
    (hacc : ShAccepted u k tv (M.mul (1.0015 * (1 - γ)) pH) H') :
    ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + x) ^ k - 1)) a f m' := by
  have hsim := hch.isPerturbedUnitarySimilar hx hC (fun t ht => by
    rw [List.eq_of_mem_replicate ht]; exact hs)
  rw [List.length_replicate] at hsim
  refine ⟨hf, H', hsim, hH', hA, ?_⟩
  rcases hacc with h | ⟨p, hp, hlt⟩
  · exact Or.inl h
  · exact Or.inr (potential_contract_of_lt hM.roundoff_nonneg hu hγ1
      (hessenbergPotential_nonneg k H') (hessenbergPotential_nonneg k H) hp hpH (hM.mul _ _) hlt)

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

variable {n : ℕ}

section Trials

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- **The trials of the exceptional branch**: on a scalar machine with the standard model at
$(n + 1)\boldsymbol{u} \le 1/2500$ and $10^5k\boldsymbol{u} \le 1$, exact comparisons, index
literals and exact natural literals up to $n + 1$, for $2 \le k = 2^q \le n$, $\mathbf{H}$ upper
Hessenberg with $0 < \omega \le \psi_k(\mathbf{H})$, $\gamma < 1$, the threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, $c_p = 1.0015(1 - \gamma)$ and the forward-error conditions
of `NLAlib.IsStableQRChain.exists_norm_subdiag_lt_or_potential_pow_mul_le` at the distance $d$,
from the state `NLAlib.ShiftedQR.ShExcMid2` the trials end in `NLAlib.ShiftedQR.ShOutcome`
with the backward error $(1 + C)\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem shExcTrials_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {L k q : ℕ}
    (hk2 : 2 ≤ k) (hkn : k ≤ n) (hkq : k = 2 ^ q) (hku : 100000 * k * u ≤ 1) {ε : ℝ}
    {a s wg wr ww wp g thr f : ℕ × ℕ} (hv : ShViews L n k ε a s wg wr ww wp g thr f)
    {B S ω γ d C cg cr cw cp tv : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hSH : specNorm H ≤ S) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500) (hC0 : 0 ≤ C) (hd : 0 < d)
    (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H) (hγ1 : γ < 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (d / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / d) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) (hcp : cp = 1.0015 * (1 - γ))
    (hm : ShExcMid2 M u L k ε H e ss γ cg cr cw cp tv d C a s wg wr ww wp g thr f m) :
    Writes .total I τ (shTrials (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, q, (excNet ε).length] [a, (L + 10, 0), thr, (L + 2, 0), (L + 5, 0),
        (L + 6, 0), (L + 7, 0), (L + 8, 0), (L + 9, 0), a, (L + 11, 0), f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 11) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 5) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 6) 0 (2 * k) ⊔ Store.inBlock (L + 7) 0 (2 * k) ⊔
          Store.inBlock (L + 8) 0 5 ⊔ Store.inBlock (L + 9) 0 1))
      (ShOutcome u k H γ tv ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a f)
      m := by
  obtain ⟨⟨ha, hs, hwg, hwr, hww, hwp, hg, hthl, hfl⟩, haf, hio⟩ := hv
  obtain ⟨⟨hA, -, -, -, -, -, -, hthr, -, -, -, -, h2, -, -, h5, h6, h7, h8, h9, -, -⟩,
    ⟨zs, hzs, ⟨j, hj⟩, hdist, hnear⟩, ⟨p, hp, hPt⟩, hGw, hF⟩ := hm
  subst hcp
  have hu0 := hM.roundoff_nonneg
  have hk0 : 0 < k := by omega
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hH0 : H ≠ 0 := fun h0 => by
    have h1 : specNorm H = 0 := by rw [h0, specNorm_zero]
    linarith [hessenbergPotential_le_specNorm hk0 hkn H]
  have hthrA : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock f.1 f.2 1) (Store.inBlock thr.1 thr.2 1) := hio.mono le_rfl (by fp_sub)
  refine (shTrials_writes (τ := τ) (s := (L + 10, 0)) (pt := (L + 2, 0)) (t := (L + 5, 0))
    (sr := (L + 6, 0)) (ds := (L + 7, 0)) (rg := (L + 8, 0)) (p2 := (L + 9, 0))
    (g := (L + 11, 0)) hS hM hu1 hL hNat hC hk0 hkn hkq (by nlinarith) hH hnu hA
    (fun j => by simpa using hzs j) hthr hPt hGw hF (by simp [h5]) (by simp [h6])
    (by simp [h7]) (by simp [h8]) (by simp [h9]) (by disjoint) (by disjoint) (by disjoint)
    (by disjoint) (by disjoint)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨by disjoint, haf.symm⟩⟩)
    (by disjoint)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr ⟨by disjoint,
      hthrA.mono le_sup_left le_rfl⟩, by disjoint⟩, Fp.disj_sup_right.mpr ⟨by disjoint,
        hthrA.mono le_sup_right le_rfl⟩⟩)
    (by disjoint) (by disjoint) j
    (shTrial_good hM (by nlinarith) hC0 hd hω hk0 hkn hH0 hH hV hHV hκ hSH (hnear j)
      (fun i => hdist j i) hxu hbound hγ1 hψ0 hp hj) hthrω).mono le_rfl ?_
  rintro m' - ⟨hf1, j', H', Rs, hch, hH', hA', hacc⟩
  exact shOutcome_of_accepted hM (by nlinarith) (by positivity) hC0 hγ1.le hp (hnear j') hch hH'
    hA' hf1 hacc

end Trials

end NLAlib.ShiftedQR
