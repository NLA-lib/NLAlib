/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Verified
public import NLAlib.Eigensolvers.Schur.Dense

/-!
# The verified dense Schur solver

`NLAlib.Schur.verifiedSchur sG` is the verified wrapper `NLAlib.Schur.verifiedSchurWith` around
the dense Schur solver `NLAlib.Schur.denseSchur sG`, run at the internal backward error
$\delta_{\mathrm{int}} = \delta/(16(n + 1))$, with the check words $\theta = \delta/(2\sqrt{n + 1})$
and $\kappa = 32(n + 2)^2\boldsymbol{u}$. It is a Las Vegas algorithm: on every tape a flag $0$
certifies the Schur form; the flag is nonzero with probability at most $\varphi$.

## Main definitions

* `NLAlib.Schur.verifiedSchur`, `NLAlib.Schur.verifiedSchurParams`, `NLAlib.Schur.uVerifiedSchur`.

## Main results

* `NLAlib.Schur.verifiedSchur_writes`: on every tape, flag $0$ implies the Schur form.
* `NLAlib.Schur.verifiedSchur_measureReal_not_schur_le`: the flag is $0$ except with probability
  $\varphi$.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory ProbabilityTheory ShiftedQR SmallEig
open scoped Matrix

/-- The internal backward error of the verified dense Schur solver: $\delta/(16(n + 1))$. -/
noncomputable def verifiedSchurDelta (n : ℕ) (δ : ℝ) : ℝ := δ / (16 * ((n : ℝ) + 1))

/-- The tolerance word $\theta = \delta/(2\sqrt{n + 1})$ of the check. -/
noncomputable def verifiedSchurTheta (n : ℕ) (δ : ℝ) : ℝ := δ / (2 * √((n : ℝ) + 1))

/-- **The words of the verified dense Schur solver**: the words of the dense solver at the
internal backward error, then $\theta$ and $\kappa = 32(n + 2)^2\boldsymbol{u}$ at the unit
roundoff $\boldsymbol{u}$ of the machine. -/
noncomputable def verifiedSchurParams (u : ℝ) (n : ℕ) (δ φ : ℝ) : List ℝ :=
  denseSchurParams n (verifiedSchurDelta n δ) φ ++
    [verifiedSchurTheta n δ, 32 * ((n : ℝ) + 2) ^ 2 * u]

/-- **The unit roundoff threshold** of the verified dense Schur solver: that of the dense solver
at the internal backward error, and $\theta/(4096(n + 2)^3)$ for the check. -/
noncomputable def uVerifiedSchur (n : ℕ) (δ φ : ℝ) : ℝ :=
  min (uDenseSchur n (verifiedSchurDelta n δ) φ)
    (verifiedSchurTheta n δ / (4096 * ((n : ℝ) + 2) ^ 3))

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The verified dense Schur solver**: `NLAlib.Schur.verifiedSchurWith` around
`NLAlib.Schur.denseSchur` on the Gaussian stream `sG`. The interface is
`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`.
Algorithm: verified-schur -/
def verifiedSchur (sG : ℕ) : Impl O Q :=
  verifiedSchurWith (denseSchur (O := O) (Q := Q) sG)

end Program

/-- The parameters of the verified dense Schur solver at $0 < \delta \le 1$ and
$0 \le \boldsymbol{u} \le$ `NLAlib.Schur.uVerifiedSchur`. -/
theorem verifiedSchur_params_basic {n : ℕ} {δ φ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ≤ uVerifiedSchur n δ φ) :
    0 < verifiedSchurDelta n δ ∧ verifiedSchurDelta n δ ≤ δ ∧ verifiedSchurDelta n δ ≤ 1 / 16 ∧
      0 ≤ verifiedSchurTheta n δ ∧ verifiedSchurTheta n δ ≤ 1 ∧
      2 * verifiedSchurTheta n δ * √((n : ℝ) + 1) ≤ δ ∧
      √((n : ℝ) + 1) * verifiedSchurDelta n δ ≤ verifiedSchurTheta n δ / 8 ∧
      4096 * ((n : ℝ) + 2) ^ 3 * u ≤ verifiedSchurTheta n δ ∧
      64 * ((n : ℝ) + 2) ^ 3 * u ≤ 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs1 : (1 : ℝ) ≤ √((n : ℝ) + 1) := by rw [Real.one_le_sqrt]; linarith
  have hs0 : (0 : ℝ) < √((n : ℝ) + 1) := by linarith
  have hss : √((n : ℝ) + 1) * √((n : ℝ) + 1) = (n : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
  have hθ1 : verifiedSchurTheta n δ ≤ 1 := by
    unfold verifiedSchurTheta; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hθ0 : 0 ≤ verifiedSchurTheta n δ := by unfold verifiedSchurTheta; positivity
  have huθ : 4096 * ((n : ℝ) + 2) ^ 3 * u ≤ verifiedSchurTheta n δ := by
    have := hu.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  refine ⟨by unfold verifiedSchurDelta; positivity, ?_, ?_, hθ0, hθ1, ?_, ?_, huθ, ?_⟩
  · unfold verifiedSchurDelta; rw [div_le_iff₀ (by positivity)]; nlinarith
  · unfold verifiedSchurDelta; rw [div_le_iff₀ (by positivity)]; nlinarith
  · unfold verifiedSchurTheta
    rw [show 2 * (δ / (2 * √((n : ℝ) + 1))) * √((n : ℝ) + 1) = δ by field_simp]
  · unfold verifiedSchurDelta verifiedSchurTheta
    have e : √((n : ℝ) + 1) * (δ / (16 * ((n : ℝ) + 1))) =
        δ / (2 * √((n : ℝ) + 1)) / 8 := by
      rw [show 16 * ((n : ℝ) + 1) = 16 * (√((n : ℝ) + 1) * √((n : ℝ) + 1)) by rw [hss]]
      field_simp
      norm_num
    rw [e]
  · linarith

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The verified dense Schur solver on every tape** (Las Vegas, the accuracy half): on a scalar
machine with the standard model at $\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact
natural literals up to $n + 1$, exact `toNat` and comparisons, draws that store the tape entry and
an exact polar disk sampler, for $0 < \delta \le 1$, any $\varphi$ and every complex $\mathbf{A}$
of order $n + 1$, from a memory holding $\mathbf{A}$ and the words of `verifiedSchurParams`, on
every tape the run of `verifiedSchur` terminates, writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$
and the flag, stores the flag $0$ or $1$, a matrix and an accumulator with
$\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}$,
and if the flag is $0$: $\widehat{\mathbf{T}}$ is upper triangular and
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$. Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uVerifiedSchur` and $R$ is
`NLAlib.Schur.denseSchurRotations` at the internal backward error. No probability.
No printed source.
Result: verified-schur-every-tape -/
theorem verifiedSchur_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : u ≤ uVerifiedSchur n δ φ) {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (verifiedSchurParams u n δ φ) a p uo f A μ) (τ : Tape ℝ) :
    Writes .total I τ (verifiedSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n (verifiedSchurDelta n δ) φ) [a, p, a, uo, f])
      (schurFp n a uo f)
      (VerifiedSchurOutput Mch a uo f A δ
        (58 * denseSchurRotations n (verifiedSchurDelta n δ) φ * u)) μ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨hd0, -, hd1, hθ0, -, hθ, -, -, hu64⟩ := verifiedSchur_params_basic hδ hδ1 hu
  replace hd1 : verifiedSchurDelta n δ ≤ 1 := by linarith
  have hud : u ≤ uDenseSchur n (verifiedSchurDelta n δ) φ := hu.trans (min_le_left _ _)
  exact verifiedSchurWith_writes hS hM hL hC
    (fun A' hin' => denseSchur_terminates hS hM hL hNat hQ hC hSmp hDisk hd0 hd1 hud hin' _)
    hu64 le_rfl hθ0 hθ (by simp [denseSchurParams, denseSchurParamsWith]) hin τ

/-- **The verified dense Schur solver** (Las Vegas, the probability half): on the machine and
streams of `NLAlib.Schur.denseSchur_measureReal_not_schur_le` (the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, a measurable interpretation reading the tape only in its windows whose
draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on
it and a stream $s_G$ with the standard real Gaussian law), for $0 < \delta \le 1$,
$0 < \varphi \le 1$ and every complex $\mathbf{A}$ of order $n + 1$, from a memory holding
$\mathbf{A}$ and the words of `verifiedSchurParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{verifiedSchur}(\mathbf{A}) \text{ fails, writes outside }
  \mathbf{A}, \widehat{\mathbf{U}} \text{ and the flag, or stores no flag } 0 \text{ with }
  \widehat{\mathbf{U}}, \widehat{\mathbf{T}},\ \widehat{\mathbf{T}} \text{ upper triangular},\
  \|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
  \delta_{\mathrm{int}}\|\mathbf{A}\|_2,\
  \|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}
  \bigr] \le \varphi\,,$$
$\delta_{\mathrm{int}} = \delta/(16(n + 1))$. With `NLAlib.Schur.verifiedSchur_writes` the flag
is a certificate on every tape. Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uVerifiedSchur` and $R$
is `NLAlib.Schur.denseSchurRotations` at $\delta_{\mathrm{int}}$.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1]
for the solver; the a posteriori check has no printed source.
Result: verified-schur-failure -/
theorem verifiedSchur_measureReal_not_schur_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {δ φ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uVerifiedSchur n δ φ)
    {a p uo f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SchurPipelineInput (verifiedSchurParams u n δ φ) a p uo f A μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (verifiedSchur (O := O) (Q := Q) sG).body
      (Env.frame (denseSchurDims n (verifiedSchurDelta n δ) φ) [a, p, a, uo, f])
      (schurFp n a uo f)
      (SchurOutput a uo f A (verifiedSchurDelta n δ)
        (58 * denseSchurRotations n (verifiedSchurDelta n δ) φ * u)) μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨hd0, -, hd16, -, hθ1, -, hδ', huθ, hu64⟩ := verifiedSchur_params_basic hδ hδ1 hu
  have hd1 : verifiedSchurDelta n δ ≤ 1 := by linarith
  have hud : u ≤ uDenseSchur n (verifiedSchurDelta n δ) φ := hu.trans (min_le_left _ _)
  obtain ⟨h58, -, -⟩ := denseSchur_orth_le (n := n) hd0 hd1 hud
  obtain ⟨hl, -, hap, -, -⟩ := id hin
  obtain ⟨-, -, h3, -, -, h6⟩ := apart_four hap
  have hlt : ∀ z ∈ [a, p, uo, f], z.1 < μ.store.length := hl
  have hκ : 32 * ((n : ℝ) + 2) ^ 2 * u ≤ 64 * ((n : ℝ) + 2) ^ 2 * u := by
    have : (0 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 * u := by positivity
    linarith
  have h := verifiedSchurWith_measureReal_not_flag_le (κ := 32 * ((n : ℝ) + 2) ^ 2 * u) hS hM hL
    hC hI hloc
    (fun μ' hin' {Ω} _ {P} {ξ} hξ' => denseSchur_measureReal_not_schur_le hS hM hL hNat hQ hC
      hI hloc hSmp hDisk hU hG hd0 hd1 hφ hφ1 hud hin' hξ')
    (measurableSet_eqOff_schurOutput _ a uo f A _ _) (fun _ h => h) ?_ ?_ hu64 (by positivity)
    hκ hθ1 huθ (h58.trans (by linarith)) hδ' (by simp [denseSchurParams, denseSchurParamsWith])
    hin hξ
  · refine (measureReal_mono ?_).trans h
    intro ω hω hw
    exact hω (hw.mono le_rfl fun _ _ h => h.2)
  · intro μ' μ'' h hfr h0
    obtain ⟨-, U, T, hT, hUs, hTu, hr, ho⟩ := h
    exact ⟨h0, U, T, hT.of_eqOff hfr h3.symm, hUs.of_eqOff hfr h6.symm, hTu, hr, ho⟩
  · intro s s' q hB h
    obtain ⟨hf0, U, T, hT, hUs, hTu, hr, ho⟩ := h
    exact ⟨((hB f.1 (hlt f (by simp))).2 f.2).trans hf0, U, T,
      hT.of_below hB (hlt a (by simp)), hUs.of_below hB (hlt uo (by simp)), hTu, hr, ho⟩

end Theorems

end NLAlib.Schur
