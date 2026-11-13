/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.EntryLayout

/-!
# Scalar entry arithmetic for Hermitian completion

The upper entry of a rounded Hermitian sum needs four scalar instructions. Its execution
statement is independent of a matrix layout: matrix kernels supply the two transposed entries
and the divisor as operands.

## Main results

* `NLAlib.Ops.Hermitian.averagePair` exposes the four scalar instructions.
* `NLAlib.Ops.Hermitian.wp_averagePair` computes their stored word pair under the scalar contract.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst : Type} [Has ScalarOp Op]

omit [Has ScalarOp Op] in
/-- An exact pair-update execution theorem supplies the component reads and the frame needed
by entry-fill rules. No scalar-call, memory-update or component preservation proof is repeated
by its matrix-level consumers. -/
theorem writes_pair_of_wp {md : Mode} {I : Interp Op Tst K} {τ : Tape K}
    {body : Stmt Op Tst} {ρ : Env} {m : Mem K} {z : ℕ × ℕ} {v : K × K}
    (h : Wp md I τ body ρ (fun m' => m' = m.updBlock z [v.1, v.2]) m)
    (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes md I τ body ρ (Store.inBlock z.1 z.2 2)
      (fun m' => (∀ u : Fin 2, m'.store.get z.1 (z.2 + u) =
        some ((EntryCodec.pair K).words v u)) ∧ m'.pos = m.pos) m := by
  refine (Writes.of_wp_eq_updBlock h).mono le_rfl ?_
  rintro m' _ rfl
  refine ⟨fun u => ?_, rfl⟩
  have hg := Store.get_updBlock (s := m.store) (b := z.1) (off := z.2)
    (xs := [v.1, v.2]) (by simpa using hz) u.isLt
  fin_cases u <;> simpa using hg

/-- Add the real words, subtract the imaginary words, and divide both results by a stored
scalar. Inputs are two word pairs and one scalar cell; output is one word pair. -/
def averagePair : Impl Op Tst := opsImpl% [] (x, y, c) → (z) {
  call (Has.inj ScalarOp.add) [] (x, y) → (z);
  call (Has.inj ScalarOp.div) [] (z, c) → (z);
  call (Has.inj ScalarOp.sub) [] (x[1], y[1]) → (z[1]);
  call (Has.inj ScalarOp.div) [] (z[1], c) → (z[1])
}

/-- The entry kernel returns the actual machine word pair and preserves all other memory.
The output pair is disjoint from both input pairs and the scalar cell; each input
word is readable and both output cells fit. This is a functional execution theorem, so it
requires no numerical accuracy claim about a zero divisor. -/
theorem wp_averagePair {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x y c z : ℕ × ℕ} {ar ai br bi a : K}
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2))
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 2) (Store.inBlock z.1 z.2 2))
    (hcz : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2))
    (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai)
    (hyr : m.store.get y.1 y.2 = some br)
    (hyi : m.store.get y.1 (y.2 + 1) = some bi)
    (hc : m.store.get c.1 c.2 = some a) (hz : z.2 + 2 ≤ m.store.len z.1)
    {Q : Mem K → Prop}
    (hQ : Q (m.updBlock z [M.div (M.add ar br) a, M.div (M.sub ai bi) a])) :
    Wp md I τ (averagePair (Op := Op) (Tst := Tst)).body
      (Env.frame [] [x, y, c, z]) Q m := by
  have hx1z0 := hxz.ne_cells
    (show Store.inBlock x.1 x.2 2 x.1 (x.2 + 1) from ⟨rfl, by omega, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  have hy1z0 := hyz.ne_cells
    (show Store.inBlock y.1 y.2 2 y.1 (y.2 + 1) from ⟨rfl, by omega, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  have hc0 := hcz.ne_cells
    (show Store.inBlock c.1 c.2 1 c.1 c.2 from ⟨rfl, le_rfl, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  have hc1 := hcz.ne_cells
    (show Store.inBlock c.1 c.2 1 c.1 c.2 from ⟨rfl, le_rfl, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 (z.2 + 1) from ⟨rfl, by omega, by omega⟩)
  refine wp_seq (wp_call_bin (hI .add) rfl rfl rfl trivial hxr hyr rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_seq (wp_call_bin (hI .div) rfl rfl rfl trivial
    (a := M.add ar br) (b := a) ?_ ?_ rfl ?_ ?_)
  · store_simp
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hc0] using hc
  · store_simp
  refine wp_seq (wp_call_bin (hI .sub) rfl rfl rfl trivial
    (a := ai) (b := bi) ?_ ?_ rfl ?_ ?_)
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hx1z0] using hxi
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hy1z0] using hyi
  · store_simp
  refine wp_call_bin (hI .div) rfl rfl rfl trivial
    (a := M.sub ai bi) (b := a) ?_ ?_ rfl ?_ ?_
  · store_simp
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hc0, Store.get_upd_of_ne hc1] using hc
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd, Store.upd_upd] using hQ

/-- Copy a complete stored word pair without arithmetic or scratch. -/
def copyPair : Impl Op Tst := opsImpl% [] (x) → (z) {
  call (Has.inj ScalarOp.copy) [] (x) → (z);
  call (Has.inj ScalarOp.copy) [] (x[1]) → (z[1])
}

/-- The pair copy writes both input words into a disjoint word block, including another
region of the same buffer. -/
theorem wp_copyPair_of_disj {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x z : ℕ × ℕ} {ar ai : K}
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2))
    (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai) (hz : z.2 + 2 ≤ m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock z [ar, ai])) :
    Wp md I τ (copyPair (Op := Op) (Tst := Tst)).body (Env.frame [] [x, z]) Q m := by
  refine wp_seq (wp_call_un (hI .copy) rfl rfl rfl trivial hxr rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_call_un (hI .copy) rfl rfl rfl trivial (a := ai) ?_ rfl ?_ ?_
  · have hne := hxz.ne_cells (show Store.inBlock x.1 x.2 2 x.1 (x.2 + 1) from
      ⟨rfl, by omega, by omega⟩) (show Store.inBlock z.1 z.2 2 z.1 z.2 from
      ⟨rfl, le_rfl, by omega⟩)
    simpa only [Mem.store_upd, Store.get_upd_of_ne hne] using hxi
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd] using hQ

/-- A pair copy between different buffers specializes the disjoint-block rule. -/
theorem wp_copyPair {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x z : ℕ × ℕ} {ar ai : K}
    (hxz : x.1 ≠ z.1) (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai) (hz : z.2 + 2 ≤ m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock z [ar, ai])) :
    Wp md I τ (copyPair (Op := Op) (Tst := Tst)).body (Env.frame [] [x, z]) Q m :=
  wp_copyPair_of_disj hI (Fp.disj_inBlock_of_ne hxz) hxr hxi hz hQ

/-- Divide both component words by a stored scalar. -/
def scalePair : Impl Op Tst := opsImpl% [] (x, c) → (z) {
  call (Has.inj ScalarOp.div) [] (x, c) → (z);
  call (Has.inj ScalarOp.div) [] (x[1], c) → (z[1])
}

/-- The pair scaling kernel computes both rounded quotients in a disjoint output word block. -/
theorem wp_scalePair {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x c z : ℕ × ℕ} {ar ai a : K}
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2))
    (hcz : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2))
    (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai)
    (hc : m.store.get c.1 c.2 = some a) (hz : z.2 + 2 ≤ m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock z [M.div ar a, M.div ai a])) :
    Wp md I τ (scalePair (Op := Op) (Tst := Tst)).body (Env.frame [] [x, c, z]) Q m := by
  have hx1z0 := hxz.ne_cells
    (show Store.inBlock x.1 x.2 2 x.1 (x.2 + 1) from ⟨rfl, by omega, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  have hc0 := hcz.ne_cells
    (show Store.inBlock c.1 c.2 1 c.1 c.2 from ⟨rfl, le_rfl, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  refine wp_seq (wp_call_bin (hI .div) rfl rfl rfl trivial hxr hc rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_call_bin (hI .div) rfl rfl rfl trivial (a := ai) (b := a) ?_ ?_ rfl ?_ ?_
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hx1z0] using hxi
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hc0] using hc
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd] using hQ

/-- Copy the real word and negate the imaginary word. -/
def conjugatePair : Impl Op Tst := opsImpl% [] (x) → (z) {
  call (Has.inj ScalarOp.copy) [] (x) → (z);
  call (Has.inj ScalarOp.neg) [] (x[1]) → (z[1])
}

/-- Conjugation computes the word pair with exactly one machine negation. -/
theorem wp_conjugatePair {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x z : ℕ × ℕ} {ar ai : K}
    (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai)
    (hz : z.2 + 2 ≤ m.store.len z.1)
    (hprotect : x.1 ≠ z.1 ∨ x.2 + 1 ≠ z.2)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock z [ar, M.neg ai])) :
    Wp md I τ (conjugatePair (Op := Op) (Tst := Tst)).body (Env.frame [] [x, z]) Q m := by
  refine wp_seq (wp_call_un (hI .copy) rfl rfl rfl trivial hxr rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_call_un (hI .neg) rfl rfl rfl trivial (a := ai) ?_ rfl ?_ ?_
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hprotect] using hxi
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd] using hQ

/-- Subtract a stored scalar from a diagonal real word and write literal zero to its
imaginary word. -/
def shiftDiagonal : Impl Op Tst := opsImpl% [] (x, c) → (z) {
  call (Has.inj ScalarOp.sub) [] (x, c) → (z);
  call (Has.inj (ScalarOp.lit 0)) [] () → (z[1])
}

/-- Diagonal shifting returns the actual rounded difference and literal zero. -/
theorem wp_shiftDiagonal {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x c z : ℕ × ℕ} {ar a : K}
    (hxr : m.store.get x.1 x.2 = some ar) (hc : m.store.get c.1 c.2 = some a)
    (hz : z.2 + 2 ≤ m.store.len z.1) {Q : Mem K → Prop}
    (hQ : Q (m.updBlock z [M.sub ar a, M.lit 0])) :
    Wp md I τ (shiftDiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [] [x, c, z]) Q m := by
  refine wp_seq (wp_call_bin (hI .sub) rfl rfl rfl trivial hxr hc rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial ?_ ?_
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd] using hQ

/-- Divide a diagonal real word by a stored scalar and write literal zero to its imaginary
word. -/
def scaleDiagonal : Impl Op Tst := opsImpl% [] (x, c) → (z) {
  call (Has.inj ScalarOp.div) [] (x, c) → (z);
  call (Has.inj (ScalarOp.lit 0)) [] () → (z[1])
}

/-- Diagonal scaling returns the actual rounded quotient and literal zero. -/
theorem wp_scaleDiagonal {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x c z : ℕ × ℕ} {ar a : K}
    (hxr : m.store.get x.1 x.2 = some ar) (hc : m.store.get c.1 c.2 = some a)
    (hz : z.2 + 2 ≤ m.store.len z.1) {Q : Mem K → Prop}
    (hQ : Q (m.updBlock z [M.div ar a, M.lit 0])) :
    Wp md I τ (scaleDiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [] [x, c, z]) Q m := by
  refine wp_seq (wp_call_bin (hI .div) rfl rfl rfl trivial hxr hc rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial ?_ ?_
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd] using hQ

/-- Add the diagonal real word to itself, divide by a stored scalar, and write imaginary zero. -/
def averageDiagonal : Impl Op Tst := opsImpl% [] (x, c) → (z) {
  call (Has.inj ScalarOp.add) [] (x, x) → (z);
  call (Has.inj ScalarOp.div) [] (z, c) → (z);
  call (Has.inj (ScalarOp.lit 0)) [] () → (z[1])
}

/-- Diagonal averaging returns the actual two rounded scalar operations and literal zero. -/
theorem wp_averageDiagonal {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x c z : ℕ × ℕ} {ar a : K}
    (hcz : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2))
    (hxr : m.store.get x.1 x.2 = some ar)
    (hc : m.store.get c.1 c.2 = some a) (hz : z.2 + 2 ≤ m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock z [M.div (M.add ar ar) a, M.lit 0])) :
    Wp md I τ (averageDiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [] [x, c, z]) Q m := by
  have hc0 := hcz.ne_cells
    (show Store.inBlock c.1 c.2 1 c.1 c.2 from ⟨rfl, le_rfl, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  refine wp_seq (wp_call_bin (hI .add) rfl rfl rfl trivial hxr hxr rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_seq (wp_call_bin (hI .div) rfl rfl rfl trivial
    (a := M.add ar ar) (b := a) ?_ ?_ rfl ?_ ?_)
  · store_simp
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hc0] using hc
  · store_simp
  refine wp_call_const (hI (.lit 0)) rfl rfl rfl trivial ?_ ?_
  · store_simp
  simpa [Mem.updBlock, Store.updBlock, Mem.upd, Store.upd_upd] using hQ

end NLAlib.Ops.Hermitian
