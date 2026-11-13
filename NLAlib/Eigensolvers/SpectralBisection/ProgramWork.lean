/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.BodyWork
public import NLAlib.Eigensolvers.SpectralBisection.Certification
public import NLAlib.Ops.Logic.Allocation

/-!
# Actual matrix work of the allocated spectral-bisection program

The actual allocation prefix exposes the caller-owned solver body without duplicating its
syntax. The canonical projection then keeps the exact matrix counts of the instrumented run;
structural work remains in the full instruction count.

## Main results

* `NLAlib.SpectralBisection.solve_kernelWeight_le_of_exec`: allocated source kernel bound.
* `NLAlib.SpectralBisection.program_kernelWeight_le_of_exec`: canonical actual-count bound.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section Source

variable {K : Type} [Inhabited K]

/-- The complete allocated solver adds at most `(L + 1) * (2 * fuel + 11) * T n` to
matrix-kernel weight. Arbitrary incoming counts and live scratch history are supported.
Primitive meanings, bounded literal exactness and actual source reads are explicit. -/
theorem solve_kernelWeight_le_of_exec
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (R0 eps beta : K) {n : ℕ} (A : Matrix (Fin n) (Fin n) (K × K))
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    {τ : Tape K} {μ : Mem K} {L fuel : ℕ} {input par u dv : ℕ × ℕ}
    (hLit : IsExactNatLit dec M (max n 4)) (hl : μ.Live [input, par, u, dv])
    (hA : μ.store.readBlock input.1 input.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : μ.store.readBlock par.1 par.2 3 = some [R0, eps, beta])
    (hSource : Fp.Disj (Store.inBlock input.1 input.2 (2 * (n * n)))
      (Store.inBlock par.1 par.2 3))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (W : DenseOp → List ℕ → ℕ) {start finish : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : start.mem = μ)
    (hr : evalCounted I W τ (solve (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
      (Env.frame [n, L, fuel] [input, par, u, dv]) start = some finish) :
    Dense.kernelWeight T finish.cost ≤ Dense.kernelWeight T start.cost +
      (L + 1) * (2 * fuel + 11) * T n := by
  subst μ
  let statement := solve (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
  let z := fun i : ℕ => (start.mem.store.length + i, 0)
  let arenas := arenaOperands (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
    (z 6) (z 7) (z 8) (z 9) (z 10)
  have hArena : (List.range (arenaLengths n L).length).map z = arenas := by
    simp [arenas, z, arenaOperands, arenaLengths, List.range_succ]
  obtain ⟨inner, final, hInner, hlength, hlens, hBelow, hpos, hcost, hfinal⟩ :=
    evalCounted_allocsAs_inv (allocations := statement.splitAllocations.1)
      (body := statement.splitAllocations.2) (ns := arenaLengths n L)
      (ρ := Env.frame [n, L, fuel] [input, par, u, dv]) (a := start) (b := finish) (by rfl)
      (by rw [Stmt.allocsAs_splitAllocations]; exact hr)
  have hsAbove : Fp.blocks arenas (arenaLengths n L) ≤ Fp.above start.mem.store.length := by
    apply Fp.blocks_le_above
    intro b hb
    rw [← hArena] at hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    exact Nat.le_add_right _ _
  have hsRoom : inner.mem.Room arenas (arenaLengths n L) := by
    rw [← hArena]
    exact Mem.room_allocs inner.mem start.mem.store.length (arenaLengths n L) hlens
  have hsApart : Fp.Apart arenas (arenaLengths n L) := by
    rw [← hArena]
    exact Fp.apart_allocs start.mem.store.length (arenaLengths n L)
  have hsLive : inner.mem.Live arenas := by
    rw [← hArena]
    exact Mem.live_allocs inner.mem start.mem.store.length (arenaLengths n L) hlength
  have hlOld : inner.mem.Live [input, par, u, dv] := by
    intro b hb
    exact (hl b hb).trans_le (by rw [hlength]; exact Nat.le_add_right _ _)
  have hlBody := (Mem.live_append inner.mem _ _).mpr ⟨hlOld, hsLive⟩
  have hlInputs : start.mem.Live [input, par] :=
    fun b hb => hl b (List.mem_append_left [u, dv] hb)
  have hProtect : Fp.Disj (Fp.blocks arenas (arenaLengths n L))
      (Fp.blocks [input, par] [2 * (n * n), 3]) :=
    (Fp.blocks_disj_above hlInputs).symm.mono hsAbove le_rfl
  have hBodyRaw := evalCounted_frame_body
    (body := solveBody (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
    (d := [n, L, fuel]) (as := [input, par, u, dv] ++ arenas) rfl rfl hInner
  have hWork := solveBody_kernelWeight_le_of_arenas (μ := inner.mem) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := start.mem.pos)
    (input := input) (par := par) (u := u) (dv := dv)
    (c := z 0) (ma := z 1) (ua := z 2) (qa := z 3) (ea := z 4) (sz := z 5)
    (kd := z 6) (kp := z 7) (lv := z 8) (su := z 9) (sg := z 10)
    M dec mm qr R0 eps beta A hS hL hC hMM hQR hQ hSample hLit hpos hlBody
    ((hBelow.readBlock (hl input (by simp)) _ _).trans hA)
    ((hBelow.readBlock (hl par (by simp)) _ _).trans hPar)
    hsRoom hsApart hSource hProtect T hT hadd W rfl hBodyRaw
  simpa only [hcost, hfinal] using hWork

end Source

section Canonical

variable {K : Type} [Inhabited K]
  {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The actual canonical execution has the same matrix-kernel bound, after removing only
its structural instruction coordinates. Its raw buffers are supplied without preprocessing. -/
theorem program_kernelWeight_le_of_exec
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d)
    (hLit : IsExactNatLit dec M (max (d 0) 4))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (R : ResourceModel DenseOp (CmpTst ⊕ IdxTst)) {τ : Tape K}
    {st : St (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) K}
    (hr : exec (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) I R
      (problem (K := K) domain admitted).formats τ d
      ((problem (K := K) domain admitted).initial d x) = some st) :
    Dense.kernelWeight T (Count.original st.cost) ≤
      (d 1 + 1) * (2 * d 2 + 11) * T (d 0) := by
  obtain ⟨raw, hraw, _, hcost⟩ := exec_original_count hr
  obtain ⟨hl, _, _, _, _⟩ := initial_problem_geometry d x
  have h := solve_kernelWeight_le_of_exec M dec mm qr
    (vec x.val.1.2 0) (vec x.val.1.2 1) (vec x.val.1.2 2) (inputMatrix d x)
    hS hL hC hMM hQR hQ hSample (τ := τ) (L := d 1) (fuel := d 2)
    (input := (0, 0)) (par := (1, 0)) (u := (2, 0)) (dv := (3, 0)) hLit hl
    (initial_readBlock_inputMatrix d x) (initial_parameter_words d x) (by disjoint)
    T hT hadd R.workspace rfl hraw
  simpa only [St.init, map_zero, Nat.zero_add, hcost] using h

end Canonical

end NLAlib.SpectralBisection
