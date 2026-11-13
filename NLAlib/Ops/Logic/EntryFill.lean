/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Logic.Loop

/-!
# Filling matrices with fixed-width entries

A round writes all component words of one logical matrix entry. The shared rule preserves
previous entries and assembles the final matrix; a kernel proof supplies only the scalar
computation for its current entry.

## Main results

* `NLAlib.Ops.writes_fillEntries₂`: two loops fill any fixed-width matrix representation.
* `NLAlib.Ops.Store.HoldsMatUpto.extend`: a block write extends a partially filled column.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K E : Type} {md : Mode} {I : Interp Op Tst K} {τ : Tape K}
  {ρ : Env} {m : Mem K}

namespace MatLayout

/-- Extending a fill by a block adds exactly that block to its footprint. -/
theorem upto_add (L : MatLayout) (j i n : ℕ) :
    L.upto j (i + n) = L.upto j i ⊔ Store.inBlock L.buf (L.cell i j) n := by
  induction n with
  | zero =>
    have hz : Store.inBlock L.buf (L.cell i j) 0 = ⊥ := by
      funext b x
      apply propext
      change (b = L.buf ∧ L.cell i j ≤ x ∧ x < L.cell i j + 0) ↔ False
      constructor
      · rintro ⟨_, hle, hlt⟩; omega
      · exact False.elim
    simp only [Nat.add_zero, hz, sup_bot_eq]
  | succ n ih =>
    rw [show i + (n + 1) = i + n + 1 by omega, upto_succ, ih, sup_assoc]
    have hc : L.cell (i + n) j = L.cell i j + n := by simp [cell, Nat.add_assoc]
    rw [hc, Fp.inBlock_add]

end MatLayout

namespace EntryCodec

/-- The scalar-word layout obtained by expanding every logical matrix entry. -/
def wordLayout (C : EntryCodec K E) (L : MatLayout) : MatLayout :=
  ⟨L.buf, L.off, C.width * L.rows, L.cols, C.width * L.ld⟩

/-- Expanding entries preserves validity of the leading dimension. -/
theorem valid_wordLayout (C : EntryCodec K E) {L : MatLayout} (hL : L.Valid) :
    (C.wordLayout L).Valid := Nat.mul_le_mul_left C.width hL

/-- The scalar matrix of component words for a logical entry matrix. -/
def wordMatrix (C : EntryCodec K E) (A : ℕ → ℕ → E) : ℕ → ℕ → K :=
  fun q j => C.words (A (q / C.width) j) ⟨q % C.width, Nat.mod_lt _ C.width_pos⟩

/-- Each component of an expanded entry is its encoded component word. -/
@[simp] theorem wordMatrix_apply (C : EntryCodec K E) (A : ℕ → ℕ → E)
    (i j : ℕ) (z : Fin C.width) :
    C.wordMatrix A (C.width * i + z) j = C.words (A i j) z := by
  simp [wordMatrix, Nat.mul_comm C.width i, Idx.div_add z.isLt, Idx.mod_add z.isLt]

/-- A logical entry address agrees with its scalar-word layout address. -/
@[simp] theorem cell_wordLayout (C : EntryCodec K E) (L : MatLayout) (i j z : ℕ) :
    (C.wordLayout L).cell (C.width * i + z) j =
      L.off + C.width * (j * L.ld + i) + z := by
  simp [wordLayout, MatLayout.cell, Nat.mul_add, Nat.mul_left_comm, Nat.add_assoc]

end EntryCodec

namespace Store

/-- A block write within the current column extends a filled matrix prefix. Earlier columns
and earlier rows are preserved by the frame, so callers supply no component preservation proof. -/
theorem HoldsMatUpto.extend {s s' : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    {j i n : ℕ} (h : s.HoldsMatUpto L A j i) (hL : L.Valid)
    (hfr : s.EqOff (inBlock L.buf (L.cell i j) n) s')
    (hw : s'.HoldsVec L.buf (L.cell i j) n (fun z => A (i + z) j)) :
    s'.HoldsMatUpto L A j (i + n) := by
  constructor
  · intro r hr c hc
    rw [hfr.get_eq fun hin => ?_]
    · exact h.1 r hr c hc
    · obtain ⟨-, hstart, -⟩ := hin
      have hb := Nat.mul_le_mul_right L.ld (show c + 1 ≤ j by omega)
      have hrl := hr.trans_le hL
      simp only [MatLayout.cell] at hstart
      rw [Nat.succ_mul] at hb
      omega
  · intro r hr
    by_cases hri : r < i
    · rw [hfr.get_eq fun hin => ?_]
      · exact h.2 r hri
      · obtain ⟨-, hstart, -⟩ := hin
        simp only [MatLayout.cell] at hstart
        omega
    · have hz : r - i < n := by omega
      have he : i + (r - i) = r := by omega
      simpa [he, MatLayout.cell, Nat.add_assoc] using hw (r - i) hz

end Store

/-- Two loops fill a matrix one whole fixed-width entry at a time. The step supplies the
component words of its current entry and the next tape position. The frame of all earlier
entries is available for input reads; maintaining the output matrix invariant is automatic. -/
theorem writes_fillEntries₂ {n₁ n₂ : IExp} {body : Stmt Op Tst}
    (C : EntryCodec K E) (L : MatLayout) (hL : L.Valid)
    (hn₁ : n₁.eval ρ.idx = some L.cols) (hn₂ : ∀ j, n₂.eval (ρ.pushIdx j).idx = some L.rows)
    (A : ℕ → ℕ → E) (pos : ℕ → ℕ) (hpos : m.pos = pos 0)
    (hstep : ∀ j < L.cols, ∀ i < L.rows, ∀ m',
      m.store.EqOff ((C.wordLayout L).upto j (C.width * i)) m'.store →
      m'.pos = pos (j * L.rows + i) →
      Writes md I τ body ((ρ.pushIdx j).pushIdx i)
        (Store.inBlock L.buf (L.off + C.width * (j * L.ld + i)) C.width)
        (fun m'' => (∀ z : Fin C.width,
          m''.store.get L.buf (L.off + C.width * (j * L.ld + i) + z) =
            some (C.words (A i j) z)) ∧ m''.pos = pos (j * L.rows + i + 1)) m') :
    Writes md I τ (.loop n₁ (.loop n₂ body)) ρ (C.wordLayout L).fp
      (fun m' => m'.store.HoldsEntries C L A ∧ m'.pos = pos (L.cols * L.rows)) m := by
  let W := C.wordLayout L
  have hW : W.Valid := C.valid_wordLayout hL
  have h := writes_loop₂ (md := md) (I := I) (τ := τ) (body := body) (P := fun j i m' =>
      m'.store.HoldsMatUpto W (C.wordMatrix A) j (C.width * i) ∧
        m'.pos = pos (j * L.rows + i)) hn₁ hn₂ (fun j i => W.upto j (C.width * i))
    (fun j _ i _ => by rw [Nat.mul_succ, MatLayout.upto_add]; exact le_sup_left)
    (fun j _ => by change W.upto j W.rows ≤ W.upto (j + 1) 0; rw [MatLayout.upto_col])
    ⟨⟨fun _ _ _ h => by omega, fun _ h => by omega⟩, by simpa using hpos⟩
    (fun j _ m' hp => ⟨⟨fun r hr c hc => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
      · exact hp.1.1 r hr c hc
      · exact hp.1.2 r hr, fun _ h => by omega⟩,
      by simpa [Nat.succ_mul, Nat.add_assoc] using hp.2⟩)
    fun j hj i hi m' hfr hp => ?_
  · change Writes md I τ (.loop n₁ (.loop n₂ body)) ρ W.fp _ m
    have hf : W.upto L.cols 0 = W.fp := by
      change W.upto W.cols 0 = W.fp
      exact W.upto_cols
    rw [show C.width * 0 = 0 by omega, hf] at h
    refine h.mono le_rfl fun m' _ hp => ⟨?_, by simpa using hp.2⟩
    have hm := Store.holdsMatUpto_cols.mp hp.1
    intro i hi j hj z
    have hz : C.width * i + z < W.rows := by
      have hh := Idx.add_lt_mul hi z.isLt
      simpa [W, EntryCodec.wordLayout, Nat.mul_comm] using hh
    have hh := hm _ hz j hj
    change m'.store.get L.buf ((C.wordLayout L).cell (C.width * i + z) j) =
      some (C.wordMatrix A (C.width * i + z) j) at hh
    simpa only [EntryCodec.cell_wordLayout, EntryCodec.wordMatrix_apply] using hh
  · have hs := hstep j hj i hi m' hfr hp.2
    have hc : W.cell (C.width * i) j = L.off + C.width * (j * L.ld + i) := by
      simpa [W] using C.cell_wordLayout L i j 0
    refine hs.mono (by rw [Nat.mul_succ, MatLayout.upto_add, hc]; exact le_sup_right)
      fun m'' hfr' hs' => ⟨?_, hs'.2⟩
    rw [Nat.mul_succ]
    apply hp.1.extend hW (hc ▸ hfr')
    intro z hz
    have he := C.wordMatrix_apply A i j ⟨z, hz⟩
    change m''.store.get L.buf (W.cell (C.width * i) j + z) =
      some (C.wordMatrix A (C.width * i + z) j)
    rw [hc, he]
    exact hs'.1 ⟨z, hz⟩

end NLAlib.Ops
