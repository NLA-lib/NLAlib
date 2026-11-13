/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.MatrixPacked
public import NLAlib.Ops.Blas.MatrixCorrect
public import NLAlib.Ops.Logic.EntryRows

/-!
# Stored functional refinement of randomized deflation

The sample stage multiplies the actual stored Gaussian component words by the actual stored
scale. Multiplication and QR then apply their supplied word-level routines. Selecting the
leading columns copies their actual packed words; no numerical subspace conclusion or
successful-run premise is part of a primitive contract.

## Main results

* `NLAlib.SpectralBisection.sampledGaussian` is the actual scaled sample matrix.
* `NLAlib.SpectralBisection.writes_deflateSamples` connects the sample program to that matrix.
* `NLAlib.SpectralBisection.writes_deflate` returns the actual selected QR columns.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]

/-- The selected stored sample matrix, with one actual rounded multiplication per component.
The two sample sets occupy alternating columns of the level's Gaussian matrix. -/
def sampledGaussian (M : Machine K) (k lo side : ℕ) (S : ℕ → ℕ → K × K) (a : K) :
    Matrix (Fin k) (Fin k) (K × K) := Matrix.of fun i j =>
  (M.mul (S i (2 * (lo + j) + side)).1 a, M.mul (S i (2 * (lo + j) + side)).2 a)

omit [Inhabited K] [Has MatrixOp Op] in
/-- The sample stage writes exactly the selected, machine-scaled Gaussian matrix. The sample
span and scale cell are spatially disjoint from its output span; shared buffers are permitted.
Explicit side and slot bounds ensure every stored sample used by the program exists. -/
theorem writes_deflateSamples {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {n k lo side : ℕ} {sg sq g : ℕ × ℕ}
    (S : ℕ → ℕ → K × K) (a : K) (hside : side < 2) (hslot : lo + k ≤ n)
    (hl : m.Live [sg, sq, g])
    (hsg : m.store.HoldsEntries (EntryCodec.pair K) ⟨sg.1, sg.2, n, 2 * n, n⟩ S)
    (hsq : m.store.get sq.1 sq.2 = some a)
    (hg : g.2 + 2 * (k * k) ≤ m.store.len g.1)
    (hsgg : Fp.Disj (Store.inBlock sg.1 sg.2 (2 * ((2 * n) * n)))
      (Store.inBlock g.1 g.2 (2 * (k * k))))
    (hsqg : Fp.Disj (Store.inBlock sq.1 sq.2 1) (Store.inBlock g.1 g.2 (2 * (k * k)))) :
    Writes md I τ (deflateSamples (Op := Op) (Tst := Tst)).body
      (Env.frame [n, k, lo, side] [sg, sq, g]) (Store.inBlock g.1 g.2 (2 * (k * k)))
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock g.1 g.2 (2 * (k * k)) =
        some ((EntryCodec.pair K).packFinMatrix (sampledGaussian M k lo side S a))) m := by
  let C := EntryCodec.pair K
  let A := fun i j =>
    (M.mul (S i (2 * (lo + j) + side)).1 a, M.mul (S i (2 * (lo + j) + side)).2 a)
  have hfp := C.regionFp_le_inBlock g.1 g.2 k (k * k)
    (fun i j => j * k + i) (fun _ => k) (fun j hj i hi => Idx.add_lt_mul hj hi)
  suffices hw : Writes md I τ (deflateSamples (Op := Op) (Tst := Tst)).body
      (Env.frame [n, k, lo, side] [sg, sq, g])
      (C.regionFp g.1 g.2 k (fun i j => j * k + i) (fun _ => k))
      (fun m' => m'.store.HoldsEntryRegion C g.1 g.2 k (fun i j => j * k + i)
        (fun _ => k) A ∧ m'.pos = m.pos) m by
    refine hw.mono hfp fun m' _ hp => ⟨hp.2, ?_⟩
    have hG : m'.store.HoldsEntries C ⟨g.1, g.2, k, k, k⟩ A :=
      fun i hi j hj z => hp.1 j hj i hi z
    simpa [C, sampledGaussian, A, Nat.mul_comm] using hG.readBlock_packFinMatrix rfl
  refine writes_fillEntryRegion C g.1 g.2 k (fun i j => j * k + i) (fun _ => k)
    ?_ rfl (fun _ => rfl) A (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    have hd := congrArg (· / k) he
    have hm := congrArg (· % k) he
    simp only [Idx.div_add hp.2, Idx.div_add hq.2] at hd
    simp only [Idx.mod_add hp.2, Idx.mod_add hq.2] at hm
    exact Prod.ext hm hd
  · intro j hj i hi m' hfr hp
    have hfull := (hfr.mono (C.regionUpto_le_regionFp g.1 g.2 k
      (fun i j => j * k + i) (fun _ => k) hj hi.le)).mono hfp
    have hinput := hfull.keep
      (Store.readsOnly_holdsEntries C ⟨sg.1, sg.2, n, 2 * n, n⟩ S le_rfl) hsgg.symm hsg
    have hscale := hfull.keep (Store.readsOnly_get sq.1 sq.2 a) hsqg.symm hsq
    have hin : i < n := by omega
    have hjn : 2 * (lo + j) + side < 2 * n := by omega
    have hxr := hinput i hin (2 * (lo + j) + side) hjn 0
    have hxi := hinput i hin (2 * (lo + j) + side) hjn 1
    have hspace : g.2 + 2 * (j * k + i) + 2 ≤ m'.store.len g.1 :=
      C.room_entry (L := ⟨g.1, g.2, k, k, k⟩) le_rfl hi hj
        (by rw [hfr.len_eq]; exact hg)
    have hsrc := C.entryBlock_le_inBlock sg.1 sg.2 ((2 * n) * n)
      (Idx.add_lt_mul hjn hin)
    have hdst := C.entryBlock_le_inBlock g.1 g.2 (k * k) (Idx.add_lt_mul hj hi)
    have hw := Pair.writes_multiply hS (md := md) (τ := τ) (m := m')
      (x := (sg.1, sg.2 + 2 * (n * (2 * (lo + j) + side) + i)))
      (c := sq) (z := (g.1, g.2 + 2 * (j * k + i)))
      (by simpa [C, EntryCodec.entryBlock, Nat.mul_comm n] using hsgg.mono hsrc hdst)
      (hsqg.mono le_rfl hdst)
      (by simpa [C, Nat.mul_comm n] using hxr)
      (by simpa [C, Nat.mul_comm n] using hxi) hscale hspace
    refine writes_frame rfl rfl (by simpa [Mem.Live] using hl.congr hfr.length_eq) ?_
    refine hw.mono le_rfl fun m'' _ he => ?_
    subst m''
    refine ⟨?_, hp⟩
    intro z
    have hg' := Store.get_updBlock (s := m'.store) (b := g.1)
      (off := g.2 + 2 * (j * k + i))
      (xs := [M.mul (S i (2 * (lo + j) + side)).1 a, M.mul (S i (2 * (lo + j) + side)).2 a])
      (by simpa using hspace) z.isLt
    fin_cases z <;> simpa [C, A] using hg'

/-- Deflation executes sample scaling, the supplied multiplication and QR routines, and
copies the first requested QR columns. All four scratch matrices are scoped. The output may
alias an original input: its copy occurs after every input-dependent computation. -/
theorem writes_deflate {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) (K × K) →
      Matrix (Fin m) (Fin n) (K × K) → Matrix (Fin l) (Fin n) (K × K)}
    {qr : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) (K × K) →
      Matrix (Fin m) (Fin m) (K × K) × Matrix (Fin m) (Fin n) (K × K)}
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    {τ : Tape K} {μ : Mem K} {n k r lo side : ℕ} {sg sq p z : ℕ × ℕ}
    (S : ℕ → ℕ → K × K) (a : K) (P : Matrix (Fin k) (Fin k) (K × K))
    (hside : side < 2) (hslot : lo + k ≤ n) (hr : r ≤ k)
    (hl : μ.Live [sg, sq, p, z])
    (hsg : μ.store.HoldsEntries (EntryCodec.pair K) ⟨sg.1, sg.2, n, 2 * n, n⟩ S)
    (hsq : μ.store.get sq.1 sq.2 = some a)
    (hP : μ.store.readBlock p.1 p.2 (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix P))
    (hz : z.2 + 2 * (k * r) ≤ μ.store.len z.1) :
    Writes .total I τ (deflate (Op := Op) (Tst := Tst)).body
      (Env.frame [n, k, r, lo, side] [sg, sq, p, z])
      (Store.inBlock z.1 z.2 (2 * (k * r)))
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock z.1 z.2 (2 * (k * r)) =
        some ((EntryCodec.pair K).packFinMatrix
          ((qr (mm P (sampledGaussian M k lo side S a))).1.submatrix id (Fin.castLE hr)))) μ := by
  let C := EntryCodec.pair K
  let G := sampledGaussian M k lo side S a
  obtain ⟨hsgL, hsqL, hpL, hzL⟩ : sg.1 < μ.store.length ∧ sq.1 < μ.store.length ∧
      p.1 < μ.store.length ∧ z.1 < μ.store.length := by simpa using hl
  refine writes_allocs_readBlock (lens := List.replicate 4 (.const 2 * (.var 1 * .var 1)))
    (ns := List.replicate 4 (2 * (k * k))) rfl hzL fun s hs hlen hBelow => ?_
  have hGlen := hlen 0 (by simp)
  have hYlen := hlen 1 (by simp)
  have hQlen := hlen 2 (by simp)
  have hRlen := hlen 3 (by simp)
  simp only [List.length_replicate, List.getElem_replicate, Nat.add_zero] at *
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    Nat.add_zero] at ⊢
  have hsg₀ := hBelow.keep
    (Store.readsOnly_holdsEntries C ⟨sg.1, sg.2, n, 2 * n, n⟩ S le_rfl)
    (fun b i hb => by rcases hb with ⟨rfl, _, _⟩; exact hsgL) hsg
  have hsq₀ := ((hBelow sq.1 hsqL).2 sq.2).trans hsq
  have hP₀ := (hBelow.readBlock hpL p.2 (2 * (k * k))).trans hP
  have hz₀ : z.2 + 2 * (k * r) ≤ s.len z.1 := by rw [(hBelow z.1 hzL).1]; exact hz
  refine (writes_frame rfl rfl (by simp [Mem.Live, hs]; omega)
    (writes_deflateSamples hS S a hside hslot (by simp [Mem.Live, hs]; omega)
      hsg₀ hsq₀ (by simpa using hGlen.ge)
      (Fp.disj_inBlock_of_ne (by dsimp only; omega))
      (Fp.disj_inBlock_of_ne (by dsimp only; omega)))).seq_le
    (Fp.inBlock_le_sup_above (by dsimp only; omega)) ?_
  intro μ₁ hfr₁ ⟨hpos₁, hG₁⟩
  have hP₁ := hfr₁.readBlock_of hP₀ (by intro q hq hin; dsimp only at hin; have := hin.1; omega)
  refine (writes_matrixMul_packFinMatrix C mm hMM P G rfl rfl rfl
    (by simp [Mem.Live, hfr₁.length_eq, hs]; omega) (by simpa [C, Nat.mul_comm] using hP₁)
    (by simpa [C, G, Nat.mul_comm] using hG₁)
    (by simpa [C, hfr₁.len_eq, Nat.mul_comm] using hYlen.ge)).seq_le
    (Fp.inBlock_le_sup_above (by dsimp only; omega)) ?_
  intro μ₂ hfr₂ ⟨hpos₂, hY₂⟩
  refine (writes_matrixQR_packFinMatrix C qr hQR (mm P G) rfl rfl rfl
    (by simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq, hs]) hY₂
    (Fp.disj_inBlock_of_ne (by dsimp only; omega))
    (by simpa [C, hfr₂.len_eq, hfr₁.len_eq, Nat.mul_comm] using hQlen.ge)
    (by simpa [C, hfr₂.len_eq, hfr₁.len_eq, Nat.mul_comm] using hRlen.ge)).seq_le
    (sup_le (Fp.inBlock_le_sup_above (by dsimp only; omega))
      (Fp.inBlock_le_sup_above (by dsimp only; omega))) ?_
  intro μ₃ hfr₃ ⟨hpos₃, hQ₃, _⟩
  have hread : μ₃.store.readBlock (μ.store.length + 2) 0 (2 * (k * r)) =
      some (C.packFinMatrix ((qr (mm P G)).1.submatrix id (Fin.castLE hr))) := by
    simpa [C, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Store.readBlock_packFinMatrix_columns C hQ₃ hr
  have hz₃ : z.2 + 2 * (k * r) ≤ μ₃.store.len z.1 := by
    rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; exact hz₀
  refine (writes_frame rfl rfl (by
    simp [Mem.Live, hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq, hs]; omega)
    (PairMatrix.writes_copy hS (by
      simp [Mem.Live, hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq, hs]; omega)
      (Or.inl (Fp.disj_inBlock_of_ne (by dsimp only; omega))) hread hz₃)).mono le_sup_left ?_
  exact fun _ _ hp => ⟨hp.1.trans (hpos₃.trans (hpos₂.trans hpos₁)), hp.2⟩

end NLAlib.SpectralBisection
