/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.SolveBody
public import NLAlib.Ops.Logic.Allocation

/-!
# Total allocated spectral-bisection solver

The solver allocates its eleven arenas, executes the checked traversal, copies the root
result and releases all arenas. The mathematical result uses the actual tape at its initial
position. All inputs are ordinary stored words; scratch contains no supplied numerical data.

## Main results

* `NLAlib.SpectralBisection.writes_solve`: total stored output with scoped arena cleanup.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The complete allocated solver returns the existing mathematical word algorithm under
local primitive contracts and exact bounded dimension literals. Source inputs are readable;
the two output regions have capacity and are separated. Outputs may overlap source regions
because their final copies follow every traversal read. Numerical accuracy is separate. -/
theorem writes_solve {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (R0 eps beta : K) {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    {τ : Tape K} {μ : Mem K} {L fuel : ℕ} {a par u dv : ℕ × ℕ}
    (hLit : IsExactNatLit dec M (max n 4)) (hl : μ.Live [a, par, u, dv])
    (hA : μ.store.readBlock a.1 a.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : μ.store.readBlock par.1 par.2 3 = some [R0, eps, beta])
    (hRoom : μ.Room [u, dv] [2 * (n * n), n])
    (hSource : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock par.1 par.2 3))
    (hOutput : Fp.Disj (Store.inBlock u.1 u.2 (2 * (n * n))) (Store.inBlock dv.1 dv.2 n)) :
    let F := tapeMachine M dec mm qr n μ.pos τ
    let result := eigh F fuel L A R0 eps beta
      (eighSlotTree F n fuel R0 beta 0 0 (EighNode.mk n A R0 eps L))
    Writes .total I τ (solve (node (Op := Op) (Tst := Tst)))
      (Env.frame [n, L, fuel] [a, par, u, dv]) (Fp.blocks [u, dv] [2 * (n * n), n])
      (fun ν => ν.pos = μ.pos + (L + 1) * levelSampleSize n ∧
        StoresResult n 0 0 u dv result ν.store) μ := by
  dsimp only
  generalize hResult : eigh (tapeMachine M dec mm qr n μ.pos τ) fuel L A R0 eps beta
    (eighSlotTree (tapeMachine M dec mm qr n μ.pos τ) n fuel R0 beta 0 0
      (EighNode.mk n A R0 eps L)) = answer
  let z := fun i : ℕ => (μ.store.length + i, 0)
  let arenas := arenaOperands (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
    (z 6) (z 7) (z 8) (z 9) (z 10)
  have hArena : (List.range (arenaLengths n L).length).map z = arenas := by
    simp [arenas, z, arenaOperands, arenaLengths, List.range_succ]
  have hLiveOut : μ.Live [u, dv] := fun b hb => hl b (by simp at hb ⊢; tauto)
  allocs_preserving (arenaLengths n L)
  case sizes => rfl
  case keep =>
    intro s s' p hBelow hp
    refine ⟨hp.1, ?_⟩
    exact StoresResult.of_below (h := hp.2) hBelow (hLiveOut u (by simp))
      (hLiveOut dv (by simp))
  intro store hlength hlens hBelow
  have hsAbove : Fp.blocks arenas (arenaLengths n L) ≤ Fp.above μ.store.length := by
    apply Fp.blocks_le_above
    intro b hb
    rw [← hArena] at hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    exact Nat.le_add_right _ _
  have hsRoom : (⟨store, μ.pos⟩ : Mem K).Room arenas (arenaLengths n L) := by
    rw [← hArena]
    exact Mem.room_allocs ⟨store, μ.pos⟩ μ.store.length
      (arenaLengths n L) hlens
  have hsApart : Fp.Apart arenas (arenaLengths n L) := by
    rw [← hArena]
    exact Fp.apart_allocs μ.store.length (arenaLengths n L)
  have hsLive : (⟨store, μ.pos⟩ : Mem K).Live arenas := by
    rw [← hArena]
    exact Mem.live_allocs ⟨store, μ.pos⟩ μ.store.length
      (arenaLengths n L) hlength
  have hlOld : (⟨store, μ.pos⟩ : Mem K).Live [a, par, u, dv] := by
    intro b hb
    exact (hl b hb).trans_le (by rw [hlength]; exact Nat.le_add_right _ _)
  have hlBody := (Mem.live_append (⟨store, μ.pos⟩ : Mem K) _ _).mpr ⟨hlOld, hsLive⟩
  have hsProtect : Fp.Disj (Fp.blocks arenas (arenaLengths n L))
      (Fp.blocks [a, par, u, dv] [2 * (n * n), 3, 2 * (n * n), n]) :=
    (Fp.blocks_disj_above hl).symm.mono hsAbove le_rfl
  have hbody := writes_solveBody (μ := ⟨store, μ.pos⟩) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := μ.pos) (a := a) (par := par) (u := u) (dv := dv)
    (c := z 0) (ma := z 1) (ua := z 2) (qa := z 3) (ea := z 4) (sz := z 5)
    (kd := z 6) (kp := z 7) (lv := z 8) (su := z 9) (sg := z 10)
    M dec mm qr R0 eps beta A hS hL hC hMM hQR hQ hSample hLit rfl hlBody
    ((hBelow.readBlock (hl a (by simp)) _ _).trans hA)
    ((hBelow.readBlock (hl par (by simp)) _ _).trans hPar) hsRoom
    (by rw [Mem.room_eq_of_below hBelow hLiveOut]; exact hRoom)
    hsApart hSource hOutput hsProtect
  simp only [eigh] at hResult
  rw [hResult] at hbody
  exact (hbody.in_frame rfl rfl hlBody).mono
    (sup_le (hsAbove.trans le_sup_right) le_sup_left) (fun _ _ h => h)

end NLAlib.SpectralBisection
