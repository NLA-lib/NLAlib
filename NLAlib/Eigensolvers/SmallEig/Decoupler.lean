/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.SmallEig.Decouple
public import NLAlib.Eigensolvers.SmallEig.OneEig
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Eigensolvers.SmallEig.RandomHessenberg

/-!
# The decoupler of the small-eigenvalue solver

One node of the deflation of [BanksGarzaVargasSrivastava2025, §6] (the paper's `Eig` on a block,
with `RHess` at every node, decision D7 of the design): `RHess` makes the last-row weights large,
`OneEig` finds a shift within $\beta' = \omega/20$ of an eigenvalue and at least $\eta_1$ away from
the spectrum, and `Decouple` makes the last subdiagonal entry at most $\omega$. As the decoupler of
the rounded worklist at the bottom width $k = 1$ it meets the randomized decoupling contract on the
class of the blocks; Lemma 6.2's preservation of the class is carried by the composition of the
three contracts, and the class inside the node by one doubling
(`NLAlib.SmallEig.class_of_rhess`).

## Main definitions

* `NLAlib.SmallEig.smallEigDecoupler`: the program `[N, k, np, F, T] (W, P) → (W, Fl)`.
* `NLAlib.SmallEig.smallEigDecoupleError`: its backward error.

## Main results

* `NLAlib.SmallEig.class_of_rhess`,
  `NLAlib.SmallEig.smallEigDecoupler_randomDecouplingRoutineContract`,
  `NLAlib.SmallEig.smallEigDecoupler_terminatingDecouplerRoutine`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The decoupler of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, §6], one
node): read the cap words $m$ (bound $T$), $q$ (bound $m$), $t$ and $m_2$ (bound $T$) from
`P[8..11]`; `NLAlib.SmallEig.rhess` on the block `W` in place; `NLAlib.SmallEig.oneEig` with the
words `P` into the shift `Lam` and the flag; if the flag is $0$,
`NLAlib.SmallEig.decoupleLast` with the shift. The interface is
`[N, k, np, F, T] (W, P) → (W, Fl)`, that of the decoupling routine of
`NLAlib.ShiftedQR.solveRoundedWith`; the bottom width and the iteration cap are not read.
Algorithm: small-eig -/
def smallEigDecoupler (sG : ℕ) : Impl O Q := opsImpl% [N, k, np, F, T] (W, P) → (W, Fl) {
  let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ T;
  let q ← index (Has.inj IdxTst.toNat) (P[9]) ≤ m;
  let t ← index (Has.inj IdxTst.toNat) (P[10]) ≤ T;
  let m2 ← index (Has.inj IdxTst.toNat) (P[11]) ≤ T;
  let Lam ← alloc 2;
  run (rhess (O := O) (Q := Q) sG).body [N] (W, W);
  run (oneEig (O := O) (Q := Q)).body [N, m, q, t] (W, P, Lam, Fl);
  if (Has.inj CmpTst.isZero) [] (Fl) {
    run (decoupleLast (O := O) (Q := Q)).body [N, m2] (W, Lam, P, W, Fl)
  } else { skip }
}

end Program

/-- The backward error of the decoupler on a block of norm at most $N$ at the unit roundoff
$\boldsymbol{u}$: `RHess`, $200(n_{\max} + 1)^2\boldsymbol{u}N$, and `Decouple` from a block of norm
at most $2N$ with the shift reach $10$,
$11 \cdot 2N((1 + 300(n_{\max} + 1)^2\boldsymbol{u})^{m_2} - 1)$. -/
noncomputable def smallEigDecoupleError (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) (u N : ℝ) :
    ℝ :=
  200 * ((nmax : ℝ) + 1) ^ 2 * u * N +
    11 * (2 * N) * ((1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ smallEigDecoupleSteps nmax S δ φ c₂ - 1)

/-- A unitary similarity carries a diagonalization: $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is
diagonalized by $\mathbf{Q}^{\mathsf{H}}\mathbf{V}$, with the same eigenvalues and condition. -/
private theorem exists_diagonalization_conjTranspose_mul_mul {n : ℕ}
    {A Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) (hQ : HasOrthonormalCols Q) :
    IsUnit (Qᴴ * V) ∧ (Qᴴ * A * Q) * (Qᴴ * V) = (Qᴴ * V) * Matrix.diagonal d ∧
      pseudoConditionNumber (Qᴴ * V) = pseudoConditionNumber V := by
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ.conjTranspose_mul_self
  have hU : HasOrthonormalCols Qᴴ := by
    unfold HasOrthonormalCols; rwa [Matrix.conjTranspose_conjTranspose]
  have hQu : IsUnit Qᴴ := ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQQ⟩, rfl⟩
  refine ⟨hQu.mul hV, ?_,
    hU.pseudoConditionNumber_mul_left V⟩
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQQ, Matrix.one_mul, hAV]

/-- **The class after `RHess`** ([BanksGarzaVargasSrivastava2025, Lemma 6.2], the class part, as
the merged deflation's class doubling): if $\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le 2B$,
eigenvalues separated by $g/2$, $g > 0$, $\mathbf{Q}$ unitary and
$\|\mathbf{H} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le g/(64(n + 1)B)$, then
$\mathbf{H}$ has a diagonalization with condition at most $4B$ and eigenvalues separated by
$g/4$. -/
theorem class_of_rhess {n : ℕ} {A H Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {B g : ℝ} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 * B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g / 2 ≤ ‖d i - d j‖) (hQ : HasOrthonormalCols Q)
    (hH : specNorm (H - Qᴴ * A * Q) ≤ g / (64 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 4 * B ∧
      ∀ i j, i ≠ j → g / 4 ≤ ‖d' i - d' j‖ := by
  have hB : 0 < B := by
    have := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ; linarith
  obtain ⟨hV₀, hAV₀, hκ₀⟩ := exists_diagonalization_conjTranspose_mul_mul hV hAV hQ
  have hE : specNorm (H - Qᴴ * A * Q) ≤ g / 2 / (16 * (n + 1) * (2 * B)) := by
    convert hH using 1; field_simp; ring
  obtain ⟨V', d', hV', hHV', hκ', hgap'⟩ := exists_pseudoConditionNumber_le_and_le_norm_sub hV₀
    hAV₀ (hκ₀.trans_le hκ) (by positivity) hgap hE
  rw [add_sub_cancel] at hHV'
  refine ⟨V', d', hV', hHV', by linarith, fun i j hij => le_trans ?_ (hgap' i j hij)⟩
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h1 : 2 * (2 * B) * specNorm (H - Qᴴ * A * Q) ≤ g / 16 := by
    calc 2 * (2 * B) * specNorm (H - Qᴴ * A * Q) ≤ 4 * B * (g / (64 * (n + 1) * B)) := by
          rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]; gcongr
      _ = g / (16 * (n + 1)) := by field_simp; ring
      _ ≤ g / 16 := div_le_div_of_nonneg_left hg.le (by norm_num) (by linarith)
  linarith

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The decoupler meets the randomized decoupling contract** ([BanksGarzaVargasSrivastava2025,
Theorem 6.1], one node; [BanksGarzaVargasSrivastava2025, Lemma 6.2] carried by the composition):
on a scalar machine with the standard model at $\boldsymbol{u} \le$
`NLAlib.SmallEig.uSmallEig`, $M.\mathrm{lit}(0) = 0$, index literals, exact natural literals up to
$n_{\max} + 1$, exact comparisons and conversion, a measurable interpretation reading the tape
only in its windows whose draws store the tape entry, a stream `sG` with the standard real
Gaussian law and an exact polar sampler on a stream `sU` uniform on $[0, 1]$: for tail records
with $b_1, b_2 > 0$, $1 \le n_{\max}$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
`NLAlib.SmallEig.smallEigDecoupler` with the words `NLAlib.SmallEig.smallEigParams` and the cap
`NLAlib.SmallEig.smallEigCap` meets `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` at the
bottom width $1$, any iteration cap, orders up to $n_{\max}$ and norms up to $2\Sigma$, on the
class $(2B_c, g_c/2)$ of the blocks ($B_c, g_c$ = `NLAlib.SmallEig.smallEigCondition`,
`NLAlib.SmallEig.smallEigSeparation`), with failure probability $\varphi_D$ =
`NLAlib.SmallEig.smallEigDecouplerFailure`, the level $1.5\,\omega$ and the backward error
`NLAlib.SmallEig.smallEigDecoupleError`. -/
theorem smallEigDecoupler_randomDecouplingRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} (hS : IsScalar M I) (hM : StdModel u id M) (hzero : M.lit 0 = 0)
    (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (F : ℕ) :
    RandomDecouplingRoutineContract law (2 * smallEigCondition nmax S δ φ c₂)
      (smallEigSeparation nmax S δ φ c₁ / 2) (smallEigDecouplerFailure nmax φ) 1 F
      (smallEigCap nmax S δ φ c₁ c₂) nmax (2 * S) (smallEigParams nmax S δ φ c₁ c₂)
      (1.5 * smallEigOmega nmax S δ φ c₁ c₂) (smallEigDecoupleError nmax S δ φ c₂ u)
      (smallEigDecoupler (O := O) (Q := Q) sG) I := by
  sorry

/-- The decoupler terminates: on a scalar machine with index literals, exact natural literals
up to $n_{\max} + 1$, exact comparisons and conversion, draws that store the tape entry and an
exact polar sampler, for words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`) and at least twelve words, `NLAlib.SmallEig.smallEigDecoupler`
is a terminating decoupling routine (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) at the
bottom width $1$, any iteration cap and orders up to $n_{\max} + 1$. -/
theorem smallEigDecoupler_terminatingDecouplerRoutine {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) :
    TerminatingDecouplerRoutine nmax 1 F T qs (smallEigDecoupler (O := O) (Q := Q) sG) I := by
  intro n w q f tape μ H hk hn hW hq hl hwr hfr hwf hqwf
  obtain ⟨m, qq, t, m₂, h8, h9, h10, h11, hmq, hmT, htT, hm2T⟩ := hqs
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hget : ∀ i < qs.length, μ.store.get q.1 (q.2 + i) = some (qs.getD i 0) :=
    fun i hi => Store.get_of_readBlock hq hi 0
  have hlive : w.1 < μ.store.length ∧ q.1 < μ.store.length ∧ f.1 < μ.store.length := by
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl
    exact ⟨hl.1, hl.2.1, hl.2.2.2⟩
  have hqm : qq ≤ m := hmq ▸ Nat.lt_two_pow_self.le
  have hzero : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  unfold smallEigDecoupler
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 8 (by omega)) (by simpa using h8) hmT ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 9 (by omega)) (by simpa using h9) hqm ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 10 (by omega)) (by simpa using h10) htT ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hget 11 (by omega)) (by simpa using h11) hm2T ?_
  change Writes .total I tape (Stmt.allocs [.const 2] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2]) rfl (fun hBelow ⟨⟨x, hx⟩, H', hH'⟩ =>
    ⟨⟨x, hBelow.get_of hlive.2.2 hx⟩, H', hH'.of_below hBelow hlive.1⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hL2 : s₁.len L = 2 := by simpa using hlens 0 (by simp)
  have hq₁ := hBelow.readBlock_of hlive.2.1 hq
  have hqr : q.2 + qs.length ≤ s₁.len q.1 := Store.le_len_of_readBlock hq₁ (by omega)
  have hwr₁ : w.2 + 2 * ((n' + 1 + 1) * (n' + 1 + 1)) ≤ s₁.len w.1 := by
    rw [(hBelow w.1 hlive.1).1]; exact hwr
  have hfr₁ : f.2 + 1 ≤ s₁.len f.1 := by rw [(hBelow f.1 hlive.2.2).1]; exact hfr
  have hD : ∀ {b o k : ℕ}, b < L → Fp.Disj (Store.inBlock L 0 2) (Store.inBlock b o k) :=
    fun hb => Fp.disj_inBlock_of_ne (by omega)
  refine (rhess_terminates (τ := tape) (μ := ⟨s₁, μ.pos⟩) hS hC hSmp
    (by simp [Mem.Live, hlen]; omega) (hW.of_below hBelow hlive.1)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen]; omega) (by fp_sub) ?_
  rintro μ₁ hfr₁' ⟨H₁, hH₁⟩
  have hqw : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n' + 1 + 1) * (n' + 1 + 1))))
      (Store.inBlock q.1 q.2 qs.length) := (hqwf.mono le_rfl le_sup_left).symm
  have hqf : Fp.Disj (Store.inBlock q.1 q.2 qs.length) (Store.inBlock f.1 f.2 1) :=
    hqwf.mono le_rfl le_sup_right
  have hq₂ := hfr₁'.keep (Store.readsOnly_readBlock _ _ _ _) hqw hq₁
  have hin : OneEigInput H₁ qs w q (L, 0) f μ₁ := by
    refine ⟨by simp [Mem.Live, hfr₁'.length_eq, hlen]; omega, ?_, ?_, hH₁, hq₂⟩
    · simp only [Mem.Room, hfr₁'.len_eq]
      exact ⟨hwr₁, hqr, by rw [hL2], by omega, trivial⟩
    · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
        and_true]
      exact ⟨⟨hqw, (hD hlive.1).symm, hwf⟩, ⟨(hD hlive.2.1).symm, hqf⟩, hD hlive.2.2⟩
  refine (oneEig_terminates (m := m) (q := qq) (t := t) hS hzero hL hC hDisk (by omega)
    hin).frame_seq_le rfl rfl (by simp [Mem.Live, hfr₁'.length_eq, hlen]; omega)
    (by fp_sub) ?_
  rintro μ₂ hfr₂ ⟨⟨z, hz⟩, x, hx⟩
  have hH₂ : HoldsMatrix w H₁ μ₂.store :=
    hH₁.of_eqOff hfr₂ (Fp.disj_sup_left.mpr ⟨hD hlive.1, hwf.symm⟩)
  refine writes_ite (a := [f]) rfl rfl (hC.test_isZero hx) ?_
  split_ifs
  · have hin₂ : DecoupleInput H₁ z qs w (L, 0) q f μ₂ := by
      refine ⟨by simp [Mem.Live, hfr₂.length_eq, hfr₁'.length_eq, hlen]; omega, ?_, ?_, hH₂, hz,
        hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
          (Fp.disj_sup_left.mpr ⟨hD hlive.2.1, hqf.symm⟩) hq₂⟩
      · simp only [Mem.Room, hfr₂.len_eq, hfr₁'.len_eq]
        exact ⟨hwr₁, by rw [hL2], hqr, by omega, trivial⟩
      · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right,
          Fp.disj_bot_right, and_true]
        exact ⟨⟨(hD hlive.1).symm, hqw, hwf⟩, ⟨hD hlive.2.1, hD hlive.2.2⟩, hqf⟩
    exact ((decoupleLast_terminates (m₂ := m₂) hS hL hC (hNat.mono (by omega)) (by omega)
      hin₂).in_frame rfl rfl
      (by simp [Mem.Live, hfr₂.length_eq, hfr₁'.length_eq, hlen]; omega)).mono (by fp_sub)
      fun _ _ ⟨⟨H₃, hH₃⟩, y, hy⟩ => ⟨⟨y, hy⟩, H₃, hH₃⟩
  · exact (Writes.skip ⟨⟨x, hx⟩, H₁, hH₂⟩).mono bot_le fun _ _ h => h

end Theorems

end NLAlib.SmallEig
