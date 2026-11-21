/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.SmallEig.Decoupler
public import NLAlib.Eigensolvers.SmallEig.Leaf

/-!
# The core of the small-eigenvalue solver

The deflation of [BanksGarzaVargasSrivastava2025, §6] is the merged rounded worklist
(`NLAlib.ShiftedQR.solveRoundedWith`) at the bottom width $k = 1$, with the decoupler
`NLAlib.SmallEig.smallEigDecoupler` and the order-one leaf `NLAlib.SmallEig.copyLeaf`. On an upper
Hessenberg matrix in the class of the core (condition $B_c$, separation $g_c$) it stores, except
with probability at most $\varphi/4$, all eigenvalues of a matrix within $\delta/4$
(Theorem 6.1 in class form: no shattering vocabulary).

## Main definitions

* `NLAlib.SmallEig.smallEigCore`: the program `[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`.
* `NLAlib.SmallEig.SmallEigCoreInput`: the memory of a call.

## Main results

* `NLAlib.SmallEig.smallEigCore_pwrites`,
  `NLAlib.SmallEig.smallEigCore_measureReal_not_spectrum_le`,
  `NLAlib.SmallEig.smallEigCore_terminates`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The core of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, Theorem 6.1]):
the rounded worklist `NLAlib.ShiftedQR.solveRoundedWith` with the decoupler
`NLAlib.SmallEig.smallEigDecoupler` and the leaf `NLAlib.SmallEig.copyLeaf`. Run at the bottom
width $k = 1$. The interface is `[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`.
Algorithm: small-eig -/
def smallEigCore (sG : ℕ) : Stmt O Q :=
  solveRoundedWith (smallEigDecoupler (O := O) (Q := Q) sG) (copyLeaf (O := O) (Q := Q))

end Program

/-- The memory of a call of the core on $\mathbf{H}$ of order $n + 1$ with the words `qs`: the
views of the matrix, the threshold word (the word $6$ of `qs`), the words, the output and the
failure word are live, have room and are apart, and the matrix, the threshold and the words are
stored. -/
def SmallEigCoreInput {n : ℕ} (qs : List ℝ) (a t p out f : ℕ × ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * (n + 1), 1] ∧
    ShQRViewsApart (n + 1) qs.length a t p out f ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (qs.getD 6 0) ∧
    μ.store.readBlock p.1 p.2 qs.length = some qs

/-- The backward error of the decoupler at the norm bound $2\Sigma$ of the core is at most
$\omega/100$: for tail records with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $0 \le \boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEig` (the `Decouple`
term of the threshold). -/
theorem smallEigDecoupleError_le_omega {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ u : ℝ} (hu0 : 0 ≤ u) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) :
    0 ≤ smallEigDecoupleError nmax S δ φ c₂ u (2 * S) ∧
      smallEigDecoupleError nmax S δ φ c₂ u (2 * S) ≤ smallEigOmega nmax S δ φ c₁ c₂ / 100 := by
  have hS0 : 0 < S := hδ.trans_le hδS
  obtain ⟨-, -, -, -, -, -, hg⟩ := smallEigDecoupler_precision hb₁ hb₂ hn hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, hωδ, -⟩ := smallEigParams_spec hb₁ hb₂ hn hδ hδS hφ hφ1
  have hBc := smallEigCondition_ge hb₂ hn hS0.le hδ hφ hφ1
  have hη₁ := smallEigInnerRadius_pos hb₁ hb₂ hn hδ hδS hφ hφ1
  obtain ⟨hβ, hβS⟩ := smallEigAccuracy_le hb₁ hb₂ hn hδ hδS hφ hφ1
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
    nlinarith
  have hsep := smallEigSeparation_pos hb₁ hn hS0.le hδ hφ hφ1
  have hη₁6 := oneEigInnerRadius_le hβ hβS
    (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4) hD1
  have hη₂β : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ / 40 :=
    min_le_left _ _
  have hη₁S : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ S := by
    change oneEigInnerRadius _ _ _ _ ≤ S
    unfold smallEigOuterRadius at hη₂β
    linarith
  set m := smallEigDecoupleSteps nmax S δ φ c₂
  set y := 300 * ((nmax : ℝ) + 1) ^ 2 * u with hy
  have hy0 : 0 ≤ y := by positivity
  set r := 22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂
  have hr : 2 ≤ r := by rw [le_div_iff₀ hη₁]; linarith
  have hZ : (m : ℝ) + 1 ≤ r ^ m := by
    have h1 : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
    exact h1.trans (pow_le_pow_left₀ (by norm_num) hr m)
  have hsq : 1 ≤ √((nmax : ℝ) + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith [(nmax.cast_nonneg : (0 : ℝ) ≤ nmax)]
  have hD : 0 < 86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) * r ^ m *
      √((nmax : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hD] at hg
  have hyZ : y * ((m : ℝ) + 1) * (11008 * S) ≤ smallEigOmega nmax S δ φ c₁ c₂ := by
    have h1 : y * ((m : ℝ) + 1) * (5504 * S) ≤ y * (86 * (8 * smallEigCondition nmax S δ φ c₂) *
        (2 * S) * r ^ m * √((nmax : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hy0 |>.trans' (by rw [mul_assoc])
      calc ((m : ℝ) + 1) * (5504 * S) ≤ r ^ m * (86 * (8 * 4) * (2 * S) * 1) := by nlinarith
        _ ≤ 86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) * r ^ m *
            √((nmax : ℝ) + 1) := by
          have : 0 ≤ r ^ m := by positivity
          have := mul_le_mul_of_nonneg_left hBc (by positivity : (0 : ℝ) ≤ 86 * 8 * (2 * S) * r ^ m)
          nlinarith [mul_le_mul_of_nonneg_left hsq
            (by positivity :
              (0 : ℝ) ≤ 86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) * r ^ m)]
    linarith
  have hωS : smallEigOmega nmax S δ φ c₁ c₂ ≤ S := by
    have : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
    nlinarith
  have hmy : (m : ℝ) * y ≤ 1 / 2 := by nlinarith
  have hpow : (1 + y) ^ m - 1 ≤ 2 * m * y := by
    linarith [ShiftedQR.one_add_pow_le_one_add_two_mul hy0 (by linarith : (m : ℝ) * y ≤ 1)]
  have hpow0 : 0 ≤ (1 + y) ^ m - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := m) (le_add_of_nonneg_right hy0); linarith
  unfold smallEigDecoupleError
  rw [← hy]
  constructor
  · positivity
  · nlinarith

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The core stores a nearby spectrum** ([BanksGarzaVargasSrivastava2025, Theorem 6.1], in
class form, as a probabilistic block specification): on a scalar machine with the standard
model at $\boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEig`, index literals, exact natural literals
up to $n + 1$, exact comparisons and conversion, a measurable interpretation reading the tape
only in its windows whose draws store the tape entry, a stream `sG` with the standard real
Gaussian law and an exact polar sampler on a stream `sU` uniform on $[0, 1]$: for tail records
with $b_1, b_2 > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, let $\mathbf{H}$ of order
$n + 1 \le n_{\max}$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B_c$, eigenvalues separated by $g_c$
(`NLAlib.SmallEig.smallEigCondition`, `NLAlib.SmallEig.smallEigSeparation`) and
$\|\mathbf{H}\|_2 \le \Sigma + 3\delta/4$, stored with the words
`NLAlib.SmallEig.smallEigParams` (`NLAlib.SmallEig.SmallEigCoreInput`). Then, except with
probability at most $\varphi/4$, `NLAlib.SmallEig.smallEigCore` at the bottom width $1$ writes
only the matrix, the output and the failure word, sets the failure word to $0$ and stores all
eigenvalues of $\mathbf{H} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta/4$.
Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and
`NLAlib.SmallEig.smallEigRoutine`, on their scratch. -/
theorem smallEigCore_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) {n : ℕ}
    (hNat : IsExactNatLit id Mch (n + 1)) {nmax : ℕ} (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (hn : n + 1 ≤ nmax)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ ≤ ‖d i - d j‖)
    (hHS : specNorm H ≤ S + 3 * δ / 4) {a t p out f : ℕ × ℕ} :
    PWrites law I (smallEigCore (O := O) (Q := Q) sG)
      (Env.frame [n + 1, 1, (smallEigParams nmax S δ φ c₁ c₂).length,
        smallEigCap nmax S δ φ c₁ c₂, smallEigCap nmax S δ φ c₁ c₂] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (SmallEigCoreInput (smallEigParams nmax S δ φ c₁ c₂) a t p out f H)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ δ / 4 ∧ (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))
      (φ / 4) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hzero : Mch.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn1 : 1 ≤ nmax := by omega
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  have hnn : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
  obtain ⟨ha, -⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, -, -⟩ := smallEigParams_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  obtain ⟨hε0, hε⟩ := smallEigDecoupleError_le_omega hb₁ hb₂ hn1 hu0 hδ hδS hφ hφ1 hu
  have hΩ := two_mul_mul_smallEigOmega (c₁ := c₁) (c₂ := c₂) hn1 S δ φ
  have hBc := smallEigCondition_ge hb₂ hn1 hS0.le hδ hφ hφ1
  have hsep := smallEigSeparation_pos hb₁ hn1 hS0.le hδ hφ hφ1
  set ω := smallEigOmega nmax S δ φ c₁ c₂
  set X := min (δ / 4) (smallEigSeparation nmax S δ φ c₁ /
    (16 * nmax * smallEigCondition nmax S δ φ c₂))
  have hK : 2 * ((n : ℝ) + 1) * (2.25 * ω + smallEigDecoupleError nmax S δ φ c₂ u (2 * S) + 0) ≤
      0.38 * X := by
    have h1 : 2 * ((n : ℝ) + 1) * (2.25 * ω + smallEigDecoupleError nmax S δ φ c₂ u (2 * S) + 0)
        ≤ 2 * nmax * (2.26 * ω) := by
      have : 2.25 * ω + smallEigDecoupleError nmax S δ φ c₂ u (2 * S) + 0 ≤ 2.26 * ω := by linarith
      calc _ ≤ 2 * ((n : ℝ) + 1) * (2.26 * ω) := by gcongr
        _ ≤ 2 * nmax * (2.26 * ω) := by gcongr
    have hX : 0 ≤ X := le_min (by positivity) (div_nonneg hsep.le (by positivity))
    have : 0 ≤ ω := hω.le
    nlinarith
  have hX1 : X ≤ δ / 4 := min_le_left _ _
  have hX2 : X ≤
      smallEigSeparation nmax S δ φ c₁ / (16 * (n + 1) * smallEigCondition nmax S δ φ c₂) :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_left hsep.le (by positivity) (by gcongr))
  have hX0 : 0 ≤ X := le_min (by positivity) (div_nonneg hsep.le (by positivity))
  have hu' : u ≤ 1 / 100 := by
    have : (1 : ℝ) ≤ ((nmax : ℝ) + 1) ^ 2 := by nlinarith
    have := le_mul_of_one_le_left hu0 this; linarith
  have hDn : RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1
      (smallEigCap nmax S δ φ c₁ c₂) (smallEigCap nmax S δ φ c₁ c₂) n (2 * S)
      (smallEigParams nmax S δ φ c₁ c₂) (1.5 * ω) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I := by
    intro n' N' w' q' f' H' V' d' hk' hn₁ hN' hH' hHN' hV' hHV' hκ' hgap'
    exact smallEigDecoupler_randomDecouplingRoutineContract_of_le (O := O) (Q := Q) hS hM hzero
      hL (by omega : n ≤ nmax) hNat hC hQ hI hloc hSmp hDisk hU hG hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu _
      H' V' d' hk' hn₁ hN' hH' hHN' hV' hHV' hκ' hgap'
  have hLeaf : RandomLeafRoutineContract law 0 0 (min 1 (n + 1)) (2 * S)
      (smallEigParams nmax S δ φ c₁ c₂) (smallEigCap nmax S δ φ c₁ c₂)
      (copyLeaf (O := O) (Q := Q)) I := by
    rw [show min 1 (n + 1) = 1 by omega]; exact copyLeaf_randomLeafRoutineContract hS law _ _ _
  have h6 : (smallEigParams nmax S δ φ c₁ c₂).getD 6 0 = 2 * (1.5 * ω) ^ 2 := by
    simp [smallEigParams, ω]
  have hsqu : (1 + u) ^ 2 ≤ 2 := by
    have := mul_le_mul hu' hu' hu0 (by norm_num : (0 : ℝ) ≤ 1 / 100); nlinarith
  have hsqd : 0.98 ≤ (1 - u) ^ 2 := by nlinarith
  have hW := solveRoundedWith_pwrites (c := 2.25 * ω)
    (thr := (smallEigParams nmax S δ φ c₁ c₂).getD 6 0) (a := a) (t := t) (p := p) (out := out)
    (f := f) hS hM hu0 (by linarith) hL hNat hQ hC hI hloc _ hDn _ hLeaf
    (by unfold smallEigDecouplerFailure; positivity) le_rfl hHess hV hHV hκ hsep hgap
    (by rw [h6]; nlinarith [sq_nonneg (1.5 * ω)]) (by rw [h6]; nlinarith [sq_nonneg ω])
    (by positivity) le_rfl hε0 (by linarith) (by linarith)
  refine hW.mono (fun _ h => h) le_rfl (fun μ' ⟨hf, roots, E, hO, hE, hr⟩ =>
    ⟨hf, roots, E, hO, by linarith, hr⟩) ?_
  unfold smallEigDecouplerFailure
  rw [add_zero, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **The core stores a nearby spectrum** ([BanksGarzaVargasSrivastava2025, Theorem 6.1], in
class form): on a scalar machine with the standard model at $\boldsymbol{u} \le$
`NLAlib.SmallEig.uSmallEig`, index literals, exact natural literals up to
$n + 1$, exact comparisons and conversion, a measurable interpretation reading the tape
only in its windows whose draws store the tape entry, a stream `sG` with the standard real
Gaussian law and an exact polar sampler on a stream `sU` uniform on $[0, 1]$: for tail records
with $b_1, b_2 > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, let $\mathbf{H}$ of order
$n + 1 \le n_{\max}$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B_c$, eigenvalues separated by $g_c$
(`NLAlib.SmallEig.smallEigCondition`, `NLAlib.SmallEig.smallEigSeparation`) and
$\|\mathbf{H}\|_2 \le \Sigma + 3\delta/4$, stored with the words
`NLAlib.SmallEig.smallEigParams` (`NLAlib.SmallEig.SmallEigCoreInput`). Then, under a random tape
with the stream laws, the probability that `NLAlib.SmallEig.smallEigCore` at the bottom width $1$
fails to write only the matrix, the output and the failure word, set the failure word to $0$ and
store all eigenvalues of $\mathbf{H} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta/4$ is at
most $\varphi/4$. -/
theorem smallEigCore_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I) {n : ℕ}
    (hNat : IsExactNatLit id Mch (n + 1)) {nmax : ℕ} (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (hn : n + 1 ≤ nmax)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ ≤ ‖d i - d j‖)
    (hHS : specNorm H ≤ S + 3 * δ / 4) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SmallEigCoreInput (smallEigParams nmax S δ φ c₁ c₂) a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (smallEigCore (O := O) (Q := Q) sG)
      (Env.frame [n + 1, 1, (smallEigParams nmax S δ φ c₁ c₂).length,
        smallEigCap nmax S δ φ c₁ c₂, smallEigCap nmax S δ φ c₁ c₂] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ δ / 4 ∧ (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ} ≤
      φ / 4 :=
  (smallEigCore_pwrites (O := O) (Q := Q) hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hb₁ hb₂
    hδ hδS hφ hφ1 hu hn hHess hV hHV hκ hgap hHS).measureReal_not_writes_le hin hξ

/-- The core terminates: on a scalar machine with index literals, exact natural literals up
to $n + 1$, exact comparisons and conversion, draws that store the tape entry and an exact polar
sampler, for words `qs` with valid cap words for the cap $T$ (`NLAlib.SmallEig.SmallEigCaps`) and
at least twelve words, from `NLAlib.SmallEig.SmallEigCoreInput` with any matrix of order $n + 1$
and on every tape, `NLAlib.SmallEig.smallEigCore` at the bottom width $1$ writes only the matrix,
the output and the failure word. -/
theorem smallEigCore_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tape : Tape ℝ} {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SmallEigCoreInput qs a t p out f H μ) :
    Writes .total I tape (smallEigCore (O := O) (Q := Q) sG)
      (Env.frame [n + 1, 1, qs.length, F, T] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun _ => True) μ :=
  solveRoundedWith_terminates hS hL hNat hQ hC _
    (smallEigDecoupler_terminatingDecouplerRoutine hS hL hNat hC hQ hSmp hDisk hqs hlen) _
    (copyLeaf_terminates hS _ qs T) hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1 hin.2.2.2.2.1
    hin.2.2.2.2.2

/-- The core keeps stored output words stored: `NLAlib.SmallEig.smallEigCore_terminates`,
and if the $2(n + 1)$ output words are stored before the run, they are stored after it, also
when the core stops early. -/
theorem smallEigCore_terminates_stored {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tape : Tape ℝ}
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigCoreInput qs a t p out f H μ) :
    Writes .total I tape (smallEigCore (O := O) (Q := Q) sG)
      (Env.frame [n + 1, 1, qs.length, F, T] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ ys, μ.store.readBlock out.1 out.2 (2 * (n + 1)) = some ys) →
        ∃ ys, μ'.store.readBlock out.1 out.2 (2 * (n + 1)) = some ys) μ :=
  solveRoundedWith_terminates_stored hS hL hNat hQ hC _
    (smallEigDecoupler_terminatingDecouplerRoutine hS hL hNat hC hQ hSmp hDisk hqs hlen) _
    (copyLeaf_terminates hS _ qs T) hin.1 hin.2.1 hin.2.2.1 hin.2.2.2.1 hin.2.2.2.2.1
    hin.2.2.2.2.2

end Theorems

end NLAlib.SmallEig
