/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.InitialConstants
public import NLAlib.Eigensolvers.SpectralBisection.InitialSizes
public import NLAlib.Eigensolvers.SpectralBisection.InitialParameters
public import NLAlib.Ops.Blas.MatrixCorrect
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Total initialization of the bisection arenas

The caller supplies input words and arena capacity. The program computes the constants,
initializes all size slots, and copies the root matrix and level parameters. Actual output
blocks are composed with the shared sequential block rule, rather than an algorithm phase
record or an assumed successful execution.

## Main results

* `NLAlib.SpectralBisection.writes_initializeArenas`: the four actual initialized output blocks.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private theorem apart_initialize {n L : ℕ} {a par c ma sz lv : ℕ × ℕ}
    (h : Fp.Apart [a, par, c, ma, sz, lv]
      [2 * (n * n), 2, 5, 2 * (n * n), n * (L + 2) + 1, 2]) :
    Fp.Apart [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2] := by
  have hv := h.subviews (fun i : Fin 4 => (![2, 4, 3, 5] : Fin 4 → Fin 6) i)
    (fun _ => 0) ![5, n * (L + 2) + 1, 2 * (n * n), 2]
    (by intro i; fin_cases i <;> simp)
    (by intro i j hij hp; fin_cases i <;> fin_cases j <;> simp at hp hij ⊢)
  simpa using hv

/-- Actual initialization returns the constant block, size slots, root matrix and root
parameter pair, in execution order. It writes no cells outside these regions and preserves the
random tape position. The input matrix is copied as stored, with no numerical assumptions. -/
theorem writes_initializeArenas {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hIndex : IsIndexLit M I) {τ : Tape K} {n L : ℕ}
    {a par c ma sz lv : ℕ × ℕ} {m : Mem K} (xs : List K) (R eps : K)
    (hl : m.Live [a, par, c, ma, sz, lv])
    (hAP : Fp.Apart [a, par, c, ma, sz, lv]
      [2 * (n * n), 2, 5, 2 * (n * n), n * (L + 2) + 1, 2])
    (hA : m.store.readBlock a.1 a.2 (2 * (n * n)) = some xs)
    (hPar : m.store.readBlock par.1 par.2 2 = some [R, eps])
    (hc : c.2 + 5 ≤ m.store.len c.1)
    (hma : ma.2 + 2 * (n * n) ≤ m.store.len ma.1)
    (hsz : sz.2 + (n * (L + 2) + 1) ≤ m.store.len sz.1)
    (hlv : lv.2 + 2 ≤ m.store.len lv.1) :
    Writes .total I τ initializeArenas.body (Env.frame [n, L] [a, par, c, ma, sz, lv])
      (Fp.blocks [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2])
      (fun μ => μ.pos = m.pos ∧
        μ.readBlocks [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2] =
          some [[M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1),
              M.sqrt (M.div (M.lit 1) (M.lit 2))],
            (List.range (n * (L + 2) + 1)).map
              (fun i => if i = 0 then M.lit (n : ℚ) else M.lit 0), xs, [R, eps]]) m := by
  have hLive : a.1 < m.store.length ∧ par.1 < m.store.length ∧ c.1 < m.store.length ∧
      ma.1 < m.store.length ∧ sz.1 < m.store.length ∧ lv.1 < m.store.length := by
    simpa [Mem.Live] using hl
  rcases hLive with ⟨hla, hlpar, hlc, hlma, hlsz, hllv⟩
  have hd (i j : Fin 6) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hOut := apart_initialize hAP
  have hSource := (Store.readsOnly_readBlock a.1 a.2 (2 * (n * n)) xs).and
    (Store.readsOnly_readBlock par.1 par.2 2 [R, eps])
  have hC := writes_initialConstants (τ := τ) hS hIndex hc
  refine (writes_frame rfl rfl (by room) hC).seq_readBlock hOut.1 fun μ hfr0 _ _ => ?_
  have hSz := writes_initialSizes (τ := τ) (m := μ) (b := sz.1) (off := sz.2)
    (n := n) (L := L) hIndex
    (by rw [hfr0.len_eq]; exact hsz)
  refine (writes_frame rfl rfl (by room) hSz).seq_readBlock hOut.2.1 fun ν hfr1 _ _ => ?_
  have hfr01 := hfr0.trans' hfr1
  have hInputs := hfr01.keep hSource (Fp.disj_sup_left.mpr
    ⟨Fp.disj_sup_right.mpr ⟨hd 2 0 (by simp), hd 2 1 (by simp)⟩,
      Fp.disj_sup_right.mpr ⟨hd 4 0 (by simp), hd 4 1 (by simp)⟩⟩) ⟨hA, hPar⟩
  have hMa := PairMatrix.writes_copy (md := .total) (τ := τ) (x := a) (y := ma)
    (rows := n) (cols := n) hS
    (by room) (Or.inl (hd 0 3 (by simp))) hInputs.1
    (by rw [hfr01.len_eq]; exact hma)
  refine (writes_frame rfl rfl (by room) hMa).seq_readBlock hOut.2.2.1
    fun χ hfr2 _ _ => ?_
  have hfr012 := hfr01.trans' hfr2
  have hPar' := hfr012.keep (Store.readsOnly_readBlock par.1 par.2 2 [R, eps])
    (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hd 2 1 (by simp),
      hd 4 1 (by simp)⟩, hd 3 1 (by simp)⟩) hPar
  have hLv := writes_initialParameters (τ := τ) (lb := lv.1) (lo := lv.2)
    hS R eps hPar' (hd 1 5 (by simp))
    (by rw [hfr012.len_eq]; exact hlv)
  exact (writes_frame rfl rfl (by room) hLv).readBlocks_singleton

end NLAlib.SpectralBisection
