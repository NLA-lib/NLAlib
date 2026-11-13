/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLevelWords
public import NLAlib.Eigensolvers.SpectralBisection.DownWork
public import NLAlib.Eigensolvers.SpectralBisection.ZeroWork
public import NLAlib.Ops.Logic.Count

/-!
# Actual matrix-kernel work of a prepared downward level

Parameter updates and sampling have zero matrix weight. Their ordinary word postcondition
supplies the same scan inputs used by the functional proof, after which the actual slot costs
sum at the selected stored sizes. Incoming counts and live scratch are unrestricted.

## Main results

* `NLAlib.SpectralBisection.downLevelImpl_kernelWeight_sum_le_of_exec`: actual level costs.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Actual preparation and scan add exactly the same partition-sensitive upper bound as the
scan alone. Scalar arithmetic and samples retain their independent full canonical charges. -/
theorem downLevelImpl_kernelWeight_sum_le_of_exec {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hC : IsCmp dec I) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (hQR : IsMatrixQR (EntryCodec.pair K) qr I) (hQ : IsToNat dec I) (hSample : IsSample I)
    {τ : Tape K} {μ : Mem K} {n L fuel d : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (ks : ℕ → ℕ) (A : (lo : ℕ) → Matrix (Fin (ks lo)) (Fin (ks lo)) (K × K))
    (R0 eps0 beta R eps : K) (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (hexact : IsExactNatLit dec M (max n 4))
    (hsizes : ∀ lo < n, μ.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (ks lo : ℕ)))
    (hmat : ∀ lo < n, 0 < ks lo →
      μ.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
        (2 * (ks lo * ks lo)) = some ((EntryCodec.pair K).packFinMatrix (A lo)))
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hlv : μ.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hG : DownLevelGeometry n d ks par lv su sg ma ua qa ea sz kd kp c t μ.store)
    (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ)
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K} (hmem : a.mem = μ)
    (hr : evalCounted I W τ (downLevelImpl (node (Op := DenseOp)
      (Tst := CmpTst ⊕ IdxTst))).body
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost +
      ∑ lo ∈ Finset.range n, (2 * fuel + 9) * T (ks lo) := by
  subst μ
  have hl := hG.live
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  rcases hl with ⟨hparl, hlvl, hsul, hsgl, hmal, hual, hqal, heal, hszl, hkdl, hkpl, hcl, htl⟩
  have hp := writes_downPrepare (τ := τ) (m := a.mem) (L := L) hS hL hSample
    (M.lit 1) (M.lit 2) (M.div (M.lit 1) (M.lit 2)) R eps (by room) hG.prepare_apart
    (by simpa using Store.readBlock_sub hc (o := 0) (n := 3) (by omega)) hlv
    hG.next_room hG.uniform_room hG.gaussian_room (by have := hG.scratch_room; omega)
  change evalCounted I W τ (.seq _ _) _ a = some b at hr
  rw [evalCounted] at hr
  obtain ⟨mid, hprep, hscan⟩ := Option.bind_eq_some_iff.mp hr
  have hprep' := evalCounted_frame_body (d := [n, L, d]) (as := [c, lv, su, sg, t])
    rfl rfl hprep
  obtain ⟨hfr, hpost⟩ := hp.post_of_evalCounted hprep'
  have hzero := evalCounted_weight_le
    (Dense.matrixWeight (MatrixOp.dimensionWeight T)) (fun _ _ => 0) hprep'
  rw [downPrepareImpl_matrixWork_zero, Nat.add_zero] at hzero
  obtain ⟨hsizes', hread'⟩ := downScan_inputs_of_prepare M ks A R0 eps0 beta R eps
    (τ.window Stream.unif a.mem.pos n) (τ.window Stream.gauss (a.mem.pos + n) (4 * (n * n)))
    hslot hsizes hmat hpar hlv hc hG.prepare_read hfr hpost.2.2.1 hpost.2.2.2
  have hscan' := evalCounted_frame_body (d := [n, L, fuel, d])
    (as := [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]) rfl rfl hscan
  have hw := downNodes_kernelWeight_sum_le_of_exec M dec mm qr hS hL hC hMM hQR hQ
    ks A R0 beta R eps (fun lo => vec (τ.window Stream.unif a.mem.pos n) lo)
    (fun i j => (EntryCodec.pair K).entry
      (τ.window Stream.gauss (a.mem.pos + n) (4 * (n * n))) (j * n + i))
    hslot hexact hsizes' hread' (hG.congr hfr.length_eq hfr.len_eq) T W rfl hscan'
  exact hw.trans (Nat.add_le_add_right hzero _)

end NLAlib.SpectralBisection
