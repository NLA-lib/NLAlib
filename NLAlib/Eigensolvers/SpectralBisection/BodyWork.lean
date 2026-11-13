/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownwardWork
public import NLAlib.Eigensolvers.SpectralBisection.ReconstructWork
public import NLAlib.Eigensolvers.SpectralBisection.InitialArena
public import NLAlib.Ops.Logic.Count

/-!
# Matrix work of the complete caller-owned solver

Initialization contributes no matrix calls. The actual downward and upward traversals charge
their disjoint node partitions, and final copies contribute no matrix weight. Word-level
contracts supply the intermediate mathematical data on the same counted execution.

## Main results

* `NLAlib.SpectralBisection.solveBody_kernelWeight_le_of_arenas`: complete body increment.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K : Type} [Inhabited K]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} {τ : Tape K} {μ : Mem K}
  {n L fuel base : ℕ} {input par u dv c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}
  (R0 eps beta : K) (A : Matrix (Fin n) (Fin n) (K × K))

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "ARENA" => Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
  (arenaLengths n L)

/-- The caller-owned solver adds at most `(L + 1) * (2 * fuel + 11) * T n` to actual
matrix-kernel weight. Its local model, stored input and arena hypotheses are explicit.
Scalar and structural instructions remain in the full count with their separate charges. -/
theorem solveBody_kernelWeight_le_of_arenas
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I) (hLit : IsExactNatLit dec M (max n 4))
    (hPos : μ.pos = base)
    (hl : μ.Live ([input, par, u, dv] ++ arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hA : μ.store.readBlock input.1 input.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : μ.store.readBlock par.1 par.2 3 = some [R0, eps, beta])
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hSource : Fp.Disj (Store.inBlock input.1 input.2 (2 * (n * n)))
      (Store.inBlock par.1 par.2 3))
    (hProtect : Fp.Disj ARENA (Fp.blocks [input, par] [2 * (n * n), 3]))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (W : DenseOp → List ℕ → ℕ) {start finish : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : start.mem = μ)
    (hr : evalCounted I W τ (solveBody (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
      (Env.frame [n, L, fuel] [input, par, u, dv, c, ma, ua, qa, ea, sz, kd, kp, lv, su, sg])
      start = some finish) :
    Dense.kernelWeight T finish.cost ≤ Dense.kernelWeight T start.cost +
      (L + 1) * (2 * fuel + 11) * T n := by
  subst μ
  have hlArena : start.mem.Live (arenaOperands c ma ua qa ea sz kd kp lv su sg) :=
    ((Mem.live_append start.mem _ _).mp hl).2
  simp only [arenaOperands, List.cons_append, List.nil_append, Mem.live_cons,
    Mem.live_nil, and_true] at hl
  rcases hl with ⟨hi, hp, hu, hdv, hc, hma, hua, hqa, hea, hsz, hkd, hkp, hlv, hsu, hsg⟩
  have hInit := writes_initializeArenas_stored (μ := start.mem) (τ := τ)
    M F fuel R0 eps beta A hS hL (by room) hRoom hAP hSource hProtect hA hPar
  dsimp only [solveBody] at hr
  rw [evalCounted] at hr
  obtain ⟨first, hInitRun, hr⟩ := Option.bind_eq_some_iff.mp hr
  rw [evalCounted] at hr
  obtain ⟨second, hDownRun, hReconRun⟩ := Option.bind_eq_some_iff.mp hr
  have hInitRaw := evalCounted_frame_body (d := [n, L])
    (as := [input, par, c, ma, sz, lv]) rfl rfl hInitRun
  obtain ⟨hfr₁, hp₁, hPar₁, hC₁, hLevel₁, hZero₁⟩ := hInit.post_of_evalCounted hInitRaw
  have hParSep : Fp.Disj (Store.inBlock par.1 par.2 3) ARENA :=
    hProtect.symm.mono (by fp_sub) le_rfl
  have hDownRaw := evalCounted_frame_body (d := [n, L, fuel])
    (as := [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c]) rfl rfl hDownRun
  have hDownWord := writes_downwardPass_of_arenas (μ := first.mem) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := base)
    M dec mm qr R0 eps beta A hS hL hC hMM hQR hQ hSample hLit (by room)
    (hp₁.trans hPos) hLevel₁ hPar₁ hC₁ hZero₁ (hRoom.congr hfr₁.len_eq) hAP hParSep
  have hDown := downwardPass_kernelWeight_le_of_exec (μ := first.mem) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := base)
    M dec mm qr R0 eps beta A hS hL hC hMM hQR hQ hSample hLit (by room)
    (hp₁.trans hPos) hLevel₁ hPar₁ hC₁ hZero₁ (hRoom.congr hfr₁.len_eq) hAP hParSep
    T hT hadd W rfl hDownRaw
  obtain ⟨hfr₂, _, _, hC₂, hLevels₂, hRecords₂⟩ := hDownWord.post_of_evalCounted hDownRaw
  have hTwo₂ := Store.get_of_readBlock hC₂ (j := 1) (by simp) (M.lit 0)
  have hReconRaw := evalCounted_frame_body (d := [n, L])
    (as := [c, ua, qa, ea, sz, kd, kp, lv, u, dv]) rfl rfl hReconRun
  have hRecon := reconstructResult_kernelWeight_le_of_arenas (μ := second.mem) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := base)
    M dec mm qr R0 eps beta A hS hQ hMM hLit
    (hlArena.congr (hfr₂.length_eq.trans hfr₁.length_eq))
    (hRoom.congr fun buf => (hfr₂.len_eq buf).trans (hfr₁.len_eq buf)) hAP
    hLevels₂ hRecords₂ (by simpa using hTwo₂) T hT hadd W rfl hReconRaw
  have hInitCost := evalCounted_weight_le (Dense.matrixWeight (MatrixOp.dimensionWeight T))
    (fun _ _ => 0) hInitRaw
  rw [initializeArenas_matrixWork_zero, Nat.add_zero] at hInitCost
  calc
    Dense.kernelWeight T finish.cost ≤ Dense.kernelWeight T second.cost +
        (L + 1) * (2 * T n) := hRecon
    _ ≤ (Dense.kernelWeight T first.cost + (L + 1) * ((2 * fuel + 9) * T n)) +
        (L + 1) * (2 * T n) := Nat.add_le_add_right hDown _
    _ ≤ (Dense.kernelWeight T start.cost + (L + 1) * ((2 * fuel + 9) * T n)) +
        (L + 1) * (2 * T n) := Nat.add_le_add_right (Nat.add_le_add_right hInitCost _) _
    _ = Dense.kernelWeight T start.cost + (L + 1) * (2 * fuel + 11) * T n := by ring

end

end NLAlib.SpectralBisection
