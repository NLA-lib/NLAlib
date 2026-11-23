/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.ShiftedTriSolve
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# The run of the rounded shifted back substitution

The program `NLAlib.shiftedTriSolve` stores the words `NLAlib.shiftedTriSolveWord` and sets its
flag exactly when a pivot was floored, on any scalar machine; under the standard model the stored
column is a componentwise backward solution. The tree is a fragment of the column
`NLAlib.Schur.triEigColumn` of the eigenvector stage.

## Main results

* `NLAlib.shiftedTriSolve_writes_word`: the program stores the computed words and the flag.
* `NLAlib.shiftedTriSolve_writes`: the program under the standard model.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

section Writes

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

omit [Has IndexOp O] [Has CmpTst Q] in
/-- A binary scalar call, from its stored operands. -/
private theorem writes_scalar_bin {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ}
    {ρ : Env} {m : Mem ℝ} (o : ScalarOp) {f : ℝ → ℝ → ℝ}
    (ho : M.fn o = .bin fun a b => some (f a b)) {a b z : Operand} {x y w : ℕ × ℕ} {u v : ℝ}
    (ha : a.eval ρ = some x) (hb : b.eval ρ = some y) (hz : z.eval ρ = some w)
    (hx : m.store.get x.1 x.2 = some u) (hy : m.store.get y.1 y.2 = some v)
    (hw : w.2 < m.store.len w.1) :
    Writes .total I τ (.call (Has.inj o) [] [a, b] [z]) ρ (Store.inBlock w.1 w.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get w.1 w.2 = some (f u v)) m := by
  have h := hS o
  rw [ho] at h
  exact writes_call_bin h (by simp [Operand.evalList, ha, hb]) (by simp [Operand.evalList, hz])
    trivial hx hy rfl fun _ => ⟨by
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      exact ⟨Store.lt_length_of_get hx, Store.lt_length_of_get hy,
        Store.lt_length_of_lt_len hw⟩, hw⟩

omit [Has IndexOp O] [Has CmpTst Q] in
/-- A unary scalar call, from its stored operand. -/
private theorem writes_scalar_un {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {τ : Tape ℝ}
    {ρ : Env} {m : Mem ℝ} (o : ScalarOp) {f : ℝ → ℝ}
    (ho : M.fn o = .un fun a => some (f a)) {a z : Operand} {x w : ℕ × ℕ} {u : ℝ}
    (ha : a.eval ρ = some x) (hz : z.eval ρ = some w)
    (hx : m.store.get x.1 x.2 = some u) (hw : w.2 < m.store.len w.1) :
    Writes .total I τ (.call (Has.inj o) [] [a] [z]) ρ (Store.inBlock w.1 w.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get w.1 w.2 = some (f u)) m := by
  have h := hS o
  rw [ho] at h
  exact writes_call_un h (by simp [Operand.evalList, ha]) (by simp [Operand.evalList, hz])
    trivial hx rfl hw

/-- The environment of a row. -/
private def stEnv (N j : ℕ) (t sm y g : ℕ × ℕ) (L r : ℕ) : Env :=
  ⟨[N, j, t.2, sm.2, y.2, g.2, y.2, g.2, r],
    [t.1, sm.1, y.1, g.1, y.1, g.1, L, L + 1, L + 2, L + 3, L + 4, L + 5, L + 6]⟩


local notation "rowI" => (IExp.var 1 - IExp.const 1 - IExp.var 8)

/-- The pivot of a row. -/
private def rowPivot (next : Stmt O Q) : Stmt O Q :=
  .seq (.call (Has.inj ScalarOp.sub) []
    [⟨0, .var 2 + .const 2 * (rowI * .var 0 + rowI)⟩,
      ⟨0, .var 2 + .const 2 * (.var 1 * .var 0 + .var 1)⟩] [⟨7, .const 0⟩]) <|
  .seq (.call (Has.inj ScalarOp.sub) []
    [⟨0, .var 2 + .const 2 * (rowI * .var 0 + rowI) + .const 1⟩,
      ⟨0, .var 2 + .const 2 * (.var 1 * .var 0 + .var 1) + .const 1⟩] [⟨7, .const 1⟩]) <|
  .seq (.call (Has.inj ScalarOp.mul) [] [⟨7, .const 0⟩, ⟨7, .const 0⟩] [⟨12, .const 0⟩]) <|
  .seq (.call (Has.inj ScalarOp.mul) [] [⟨7, .const 1⟩, ⟨7, .const 1⟩] [⟨9, .const 0⟩]) <|
  .seq (.call (Has.inj ScalarOp.add) [] [⟨12, .const 0⟩, ⟨9, .const 0⟩] [⟨12, .const 0⟩]) <|
  .seq (.ite (Has.inj CmpTst.le) [] [⟨12, .const 0⟩, ⟨12, .const 1⟩]
    (.seq (.call (Has.inj ScalarOp.copy) [] [⟨1, .var 3⟩] [⟨7, .const 0⟩])
      (.seq (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨7, .const 1⟩])
        (.call (Has.inj IndexOp.lit) [.const 1] [] [⟨3, .var 5⟩]))) .skip) next

/-- One multiply–add of the sum of a row. -/
private def rowSumBody : Stmt O Q :=
  .seq (.frame []
    [⟨0, .var 2 + .const 2 * ((.var 1 - .var 8 + .var 9) * .var 0 + rowI)⟩, ⟨6, .const 0⟩,
      ⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + (.var 1 - .var 8 + .var 9))⟩,
      ⟨8, .const 0⟩, ⟨9, .const 0⟩, ⟨10, .const 0⟩] Pair.linearCombination) <|
  .seq (.call (Has.inj ScalarOp.copy) [] [⟨10, .const 0⟩] [⟨8, .const 0⟩])
    (.call (Has.inj ScalarOp.copy) [] [⟨10, .const 1⟩] [⟨8, .const 1⟩])

/-- The sum of a row. -/
private def rowSum (next : Stmt O Q) : Stmt O Q :=
  .seq (.call (Has.inj ScalarOp.copy) []
    [⟨0, .var 2 + .const 2 * (.var 1 * .var 0 + rowI)⟩] [⟨8, .const 0⟩]) <|
  .seq (.call (Has.inj ScalarOp.copy) []
    [⟨0, .var 2 + .const 2 * (.var 1 * .var 0 + rowI) + .const 1⟩] [⟨8, .const 1⟩]) <|
  .seq (.loop (.var 8) rowSumBody) next

/-- The quotient of a row, negated into the column. -/
private def rowFinish : Stmt O Q :=
  .seq (.frame [] [⟨8, .const 0⟩, ⟨7, .const 0⟩, ⟨11, .const 0⟩, ⟨10, .const 0⟩]
    ShiftedQR.complexDivideWithScratch) <|
  .seq (.call (Has.inj ScalarOp.neg) [] [⟨10, .const 0⟩]
    [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + rowI)⟩])
    (.call (Has.inj ScalarOp.neg) [] [⟨10, .const 1⟩]
      [⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + rowI) + .const 1⟩])

/-- The tree is its head and the loop over the rows. -/
private theorem shiftedTriSolve_eq : (shiftedTriSolve : Stmt O Q) =
    Stmt.allocs [.const 2, .const 2, .const 2, .const 2, .const 2, .const 4, .const 2]
      (.seq (.call (Has.inj (ScalarOp.lit 1)) [] [] [⟨6, .const 0⟩]) <|
       .seq (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨6, .const 1⟩]) <|
       .seq (.call (Has.inj ScalarOp.mul) [] [⟨1, .var 3⟩, ⟨1, .var 3⟩] [⟨12, .const 1⟩]) <|
       .loop (.var 1) (rowPivot (rowSum rowFinish))) := rfl

/-- The scratch of a row. -/
private def stScratch (L : ℕ) : Fp :=
  Store.inBlock (L + 1) 0 2 ⊔ Store.inBlock (L + 2) 0 2 ⊔ Store.inBlock (L + 3) 0 2 ⊔
    Store.inBlock (L + 4) 0 2 ⊔ Store.inBlock (L + 5) 0 4 ⊔ Store.inBlock (L + 6) 0 1

/-- The facts every row keeps. -/
private structure StCtx (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) (smin : ℝ)
    (t sm y g : ℕ × ℕ) (L : ℕ) (s : Store ℝ) : Prop where
  hT : HoldsMatrix t T s
  hsm : s.get sm.1 sm.2 = some smin
  hlen : s.length = L + 7
  hl : ∀ k < 7, s.len (L + k) = if k = 5 then 4 else 2
  one0 : s.get L 0 = some (M.lit 1)
  one1 : s.get L 1 = some (M.lit 0)
  sq : s.get (L + 6) 1 = some (M.mul smin smin)
  ry : y.2 + 2 * (N * N) ≤ s.len y.1
  rg : g.2 + 1 ≤ s.len g.1

/-- What a row must not write. -/
private def stProt {N : ℕ} (_T : Matrix (Fin N) (Fin N) ℂ) (t sm : ℕ × ℕ) (L : ℕ) : Fp :=
  Store.inBlock t.1 t.2 (2 * (N * N)) ⊔ Store.inBlock sm.1 sm.2 1 ⊔ Store.inBlock L 0 2 ⊔
    Store.inBlock (L + 6) 1 1

/-- The facts of a row survive writes off the cells they read. -/
private theorem StCtx.keep {M : Machine ℝ} {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ}
    {t sm y g : ℕ × ℕ} {L : ℕ} {s s' : Store ℝ} {F : Fp} (h : StCtx M T smin t sm y g L s)
    (hfr : s.EqOff F s') (hD : Fp.Disj F (stProt T t sm L)) : StCtx M T smin t sm y g L s' where
  hT := h.hT.of_eqOff hfr fun b i hF hG => hD b i hF (Or.inl (Or.inl (Or.inl hG)))
  hsm := hfr.keep (Store.readsOnly_get _ _ _)
    (fun b i hF hG => hD b i hF (Or.inl (Or.inl (Or.inr hG)))) h.hsm
  hlen := by rw [hfr.length_eq]; exact h.hlen
  hl k hk := by rw [hfr.len_eq]; exact h.hl k hk
  one0 := hfr.keep (Store.readsOnly_get _ _ _) (fun b i hF hG => hD b i hF
    (Or.inl (Or.inr ⟨hG.1, by have := hG.2; omega⟩))) h.one0
  one1 := hfr.keep (Store.readsOnly_get _ _ _) (fun b i hF hG => hD b i hF
    (Or.inl (Or.inr ⟨hG.1, by have := hG.2; omega⟩))) h.one1
  sq := hfr.keep (Store.readsOnly_get _ _ _) (fun b i hF hG => hD b i hF (Or.inr hG)) h.sq
  ry := by rw [hfr.len_eq]; exact h.ry
  rg := by rw [hfr.len_eq]; exact h.rg

/-- The rounded shift of row `r`. -/
private noncomputable def stM (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (j r : ℕ) : ℂ :=
  ⟨M.sub (entryAt T (j - 1 - r) (j - 1 - r)).re (entryAt T j j).re,
    M.sub (entryAt T (j - 1 - r) (j - 1 - r)).im (entryAt T j j).im⟩

/-- Whether the pivot of row `r` is floored. -/
private def stFl (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) (smin : ℝ)
    (j r : ℕ) : Prop :=
  M.add (M.mul (stM M T j r).re (stM M T j r).re) (M.mul (stM M T j r).im (stM M T j r).im) ≤
    M.mul smin smin

/-- An entry of the stored matrix, at natural indices, as two cells. -/
private theorem StCtx.T_get {M : Machine ℝ} {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ}
    {t sm y g : ℕ × ℕ} {L : ℕ} {s : Store ℝ} (h : StCtx M T smin t sm y g L s) {i k : ℕ}
    (hi : i < N) (hk : k < N) :
    s.get t.1 (t.2 + 2 * (k * N + i)) = some (entryAt T i k).re ∧
      s.get t.1 (t.2 + 2 * (k * N + i) + 1) = some (entryAt T i k).im := by
  have e : entryAt T i k = T ⟨i, hi⟩ ⟨k, hk⟩ := by simp [entryAt, hi, hk]
  rw [e]
  exact ⟨h.hT.get_re ⟨i, hi⟩ ⟨k, hk⟩, h.hT.get_im ⟨i, hi⟩ ⟨k, hk⟩⟩

/-- The branch on the pivot. -/
private theorem rowPivot_ite {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j r : ℕ}
    {t sm y g : ℕ × ℕ} {L : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (ctx : StCtx M T smin t sm y g L μ.store)
    (g0 : μ.store.get (L + 1) 0 = some (stM M T j r).re)
    (g1 : μ.store.get (L + 1) 1 = some (stM M T j r).im)
    (gP : μ.store.get (L + 6) 0 = some (M.add (M.mul (stM M T j r).re (stM M T j r).re)
      (M.mul (stM M T j r).im (stM M T j r).im)))
    (hD : Fp.Disj (stScratch L ⊔ Store.inBlock g.1 g.2 1) (stProt T t sm L))
    (hgL : g.1 < L) {next : Stmt O Q} {F : Fp} {P : Mem ℝ → Prop}
    (hF : stScratch L ⊔ Store.inBlock g.1 g.2 1 ≤ F)
    (hnext : ∀ μ', μ.store.EqOff (stScratch L ⊔ Store.inBlock g.1 g.2 1) μ'.store →
      μ'.pos = μ.pos → StCtx M T smin t sm y g L μ'.store →
      (stFl M T smin j r → μ'.store.get (L + 1) 0 = some smin ∧
        μ'.store.get (L + 1) 1 = some (M.lit 0) ∧ μ'.store.get g.1 g.2 = some (M.lit 1)) →
      (¬ stFl M T smin j r → μ'.store.get (L + 1) 0 = some (stM M T j r).re ∧
        μ'.store.get (L + 1) 1 = some (stM M T j r).im ∧
        μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) →
      Writes .total I τ next (stEnv N j t sm y g L r) F P μ') :
    Writes .total I τ (.seq (.ite (Has.inj CmpTst.le) [] [⟨12, .const 0⟩, ⟨12, .const 1⟩]
      (.seq (.call (Has.inj ScalarOp.copy) [] [⟨1, .var 3⟩] [⟨7, .const 0⟩])
        (.seq (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨7, .const 1⟩])
          (.call (Has.inj IndexOp.lit) [.const 1] [] [⟨3, .var 5⟩]))) .skip) next)
      (stEnv N j t sm y g L r) F P μ := by
  have htest := hC.test_le (d := []) (m := μ) (x := (L + 6, 0)) (y := (L + 6, 1)) gP ctx.sq
  have hl1 : ∀ {s : Store ℝ}, StCtx M T smin t sm y g L s → ∀ o < 2, o < s.len (L + 1) :=
    fun c o ho => by rw [c.hl 1 (by omega)]; simpa using ho
  by_cases hfl : stFl M T smin j r
  · have hc : decide (id (M.add (M.mul (stM M T j r).re (stM M T j r).re)
        (M.mul (stM M T j r).im (stM M T j r).im)) ≤ id (M.mul smin smin)) = true :=
      decide_eq_true hfl
    rw [hc] at htest
    have hb : Writes .total I τ (.seq (.call (Has.inj ScalarOp.copy) [] [⟨1, .var 3⟩]
        [⟨7, .const 0⟩]) (.seq (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨7, .const 1⟩])
          (.call (Has.inj IndexOp.lit) [.const 1] [] [⟨3, .var 5⟩])))
        (stEnv N j t sm y g L r) (stScratch L ⊔ Store.inBlock g.1 g.2 1)
        (fun μ' => μ'.pos = μ.pos ∧ μ'.store.get (L + 1) 0 = some smin ∧
          μ'.store.get (L + 1) 1 = some (M.lit 0) ∧
          μ'.store.get g.1 g.2 = some (M.lit 1)) μ := by
      refine (writes_scalar_un (z := ⟨7, .const 0⟩) (w := (L + 1, 0)) hS .copy (f := id) rfl rfl
        rfl ctx.hsm (hl1 ctx 0 (by omega))).seq_le
        (le_sup_of_le_left (by simp only [stScratch]; fp_sub)) fun μ₁ h₁ ⟨p₁, g₁'⟩ => ?_
      have r₁ : 1 < μ₁.store.len (L + 1) := by rw [h₁.len_eq]; exact hl1 ctx 1 (by omega)
      refine (writes_call_const (hS (.lit 0)) (out := ⟨7, .const 1⟩) (z := (L + 1, 1)) rfl trivial
        r₁).seq_le (le_sup_of_le_left (by simp only [stScratch]; fp_sub))
        fun μ₂ h₂ ⟨p₂, g₂'⟩ => ?_
      have r₂ : g.2 < μ₂.store.len g.1 := by
        rw [h₂.len_eq, h₁.len_eq]; have := ctx.rg; omega
      refine (writes_indexLit (n := 1) (z := g) (out := ⟨3, .var 5⟩) hL rfl rfl r₂).mono
        le_sup_right fun μ₃ h₃ ⟨p₃, g₃'⟩ => ?_
      have hne : ∀ o, g.1 ≠ L + 1 → Fp.Disj (Store.inBlock g.1 g.2 1)
          (Store.inBlock (L + 1) o 1) := fun o hn b i h h' => hn (h.1.symm.trans h'.1)
      have hgne : g.1 ≠ L + 1 := by omega
      refine ⟨p₃.trans (p₂.trans p₁), h₃.keep (Store.readsOnly_get _ _ _) (hne 0 hgne)
        (h₂.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁'),
        h₃.keep (Store.readsOnly_get _ _ _) (hne 1 hgne) g₂', ?_⟩
      simpa using g₃'
    refine Writes.seq_le (writes_ite (c := true) (d := []) (a := [(L + 6, 0), (L + 6, 1)]) rfl rfl
      htest hb) hF fun μ' h' ⟨p', a, b, c⟩ => ?_
    exact hnext μ' h' p' (ctx.keep h' hD) (fun _ => ⟨a, b, c⟩) (fun hn => absurd hfl hn)
  · have hc : decide (id (M.add (M.mul (stM M T j r).re (stM M T j r).re)
        (M.mul (stM M T j r).im (stM M T j r).im)) ≤ id (M.mul smin smin)) = false :=
      decide_eq_false hfl
    rw [hc] at htest
    refine Writes.seq_le (writes_ite (c := false) (d := []) (a := [(L + 6, 0), (L + 6, 1)]) rfl rfl
      htest (Writes.skip (P := fun μ' => μ' = μ) rfl)) (bot_le.trans (le_sup_left.trans hF))
      fun μ' h' e => ?_
    subst e
    exact hnext μ' (Store.EqOff.refl _ _) rfl ctx (fun h => absurd h hfl)
      (fun _ => ⟨g0, g1, rfl⟩)

/-- The pivot of a row: the rounded shift, its rounded squared modulus and the branch. -/
private theorem rowPivot_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j r : ℕ} (hj : j < N) (hr : r < j)
    {t sm y g : ℕ × ℕ} {L : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (ctx : StCtx M T smin t sm y g L μ.store)
    (hD : Fp.Disj (stScratch L ⊔ Store.inBlock g.1 g.2 1) (stProt T t sm L))
    (hgL : g.1 < L) {next : Stmt O Q} {F : Fp} {P : Mem ℝ → Prop}
    (hF : stScratch L ⊔ Store.inBlock g.1 g.2 1 ≤ F)
    (hnext : ∀ μ', μ.store.EqOff (stScratch L ⊔ Store.inBlock g.1 g.2 1) μ'.store →
      μ'.pos = μ.pos → StCtx M T smin t sm y g L μ'.store →
      (stFl M T smin j r → μ'.store.get (L + 1) 0 = some smin ∧
        μ'.store.get (L + 1) 1 = some (M.lit 0) ∧ μ'.store.get g.1 g.2 = some (M.lit 1)) →
      (¬ stFl M T smin j r → μ'.store.get (L + 1) 0 = some (stM M T j r).re ∧
        μ'.store.get (L + 1) 1 = some (stM M T j r).im ∧
        μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) →
      Writes .total I τ next (stEnv N j t sm y g L r) F P μ') :
    Writes .total I τ (rowPivot next) (stEnv N j t sm y g L r) F P μ := by
  have sc : ∀ {G : Fp}, G ≤ stScratch L → G ≤ F := fun h => (h.trans le_sup_left).trans hF
  have dj : ∀ {G : Fp}, G ≤ stScratch L → Fp.Disj G (stProt T t sm L) := fun h =>
    hD.mono (h.trans le_sup_left) le_rfl
  have hi : j - 1 - r < N := by omega
  have len : ∀ {s : Store ℝ}, StCtx M T smin t sm y g L s → ∀ k (hk : k < 7) o,
      o < (if k = 5 then 4 else 2) → o < s.len (L + k) := fun c k hk o ho => by
    rw [c.hl k hk]; exact ho
  have b10 : Store.inBlock (L + 1) 0 1 ≤ stScratch L := by simp only [stScratch]; fp_sub
  have b11 : Store.inBlock (L + 1) 1 1 ≤ stScratch L := by simp only [stScratch]; fp_sub
  have b60 : Store.inBlock (L + 6) 0 1 ≤ stScratch L := by simp only [stScratch]; fp_sub
  have b30 : Store.inBlock (L + 3) 0 1 ≤ stScratch L := by simp only [stScratch]; fp_sub
  refine (writes_scalar_bin (z := ⟨7, .const 0⟩) (w := (L + 1, 0)) hS .sub (f := M.sub) rfl rfl rfl
    rfl (ctx.T_get hi hi).1 (ctx.T_get hj hj).1 (len ctx 1 (by omega) 0 (by simp))).seq_le
    (sc b10) fun μ₁ h₁ ⟨p₁, g₁⟩ => ?_
  have c₁ := ctx.keep h₁ (dj b10)
  refine (writes_scalar_bin (z := ⟨7, .const 1⟩) (w := (L + 1, 1)) hS .sub (f := M.sub) rfl rfl rfl
    rfl (c₁.T_get hi hi).2 (c₁.T_get hj hj).2 (len c₁ 1 (by omega) 1 (by simp))).seq_le
    (sc b11) fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
  have c₂ := c₁.keep h₂ (dj b11)
  have g₁₂ := h₂.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁
  refine (writes_scalar_bin (z := ⟨12, .const 0⟩) (w := (L + 6, 0)) hS .mul (f := M.mul) rfl rfl rfl
    rfl g₁₂ g₁₂ (len c₂ 6 (by omega) 0 (by simp))).seq_le (sc b60) fun μ₃ h₃ ⟨p₃, g₃⟩ => ?_
  have c₃ := c₂.keep h₃ (dj b60)
  have g₂₃ := h₃.keep (Store.readsOnly_get _ _ _) (by disjoint) g₂
  have g₁₃ := h₃.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁₂
  refine (writes_scalar_bin (z := ⟨9, .const 0⟩) (w := (L + 3, 0)) hS .mul (f := M.mul) rfl rfl rfl
    rfl g₂₃ g₂₃ (len c₃ 3 (by omega) 0 (by simp))).seq_le (sc b30) fun μ₄ h₄ ⟨p₄, g₄⟩ => ?_
  have c₄ := c₃.keep h₄ (dj b30)
  have g₃₄ := h₄.keep (Store.readsOnly_get _ _ _) (by disjoint) g₃
  have g₁₄ := h₄.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁₃
  have g₂₄ := h₄.keep (Store.readsOnly_get _ _ _) (by disjoint) g₂₃
  refine (writes_scalar_bin (z := ⟨12, .const 0⟩) (w := (L + 6, 0)) hS .add (f := M.add) rfl rfl rfl
    rfl g₃₄ g₄ (len c₄ 6 (by omega) 0 (by simp))).seq_le (sc b60) fun μ₅ h₅ ⟨p₅, g₅⟩ => ?_
  have c₅ := c₄.keep h₅ (dj b60)
  have hsc : μ.store.EqOff (stScratch L) μ₅.store :=
    ((((h₁.mono b10).trans (h₂.mono b11)).trans (h₃.mono b60)).trans (h₄.mono b30)).trans
      (h₅.mono b60)
  refine rowPivot_ite hS hL hC c₅ (h₅.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁₄)
    (h₅.keep (Store.readsOnly_get _ _ _) (by disjoint) g₂₄) g₅ hD hgL hF fun μ' h' p' c' a b => ?_
  have hgk : μ₅.store.get g.1 g.2 = μ.store.get g.1 g.2 := hsc.2 _ _ (by
    simp only [stScratch, Fp.sup_apply, Store.inBlock]; omega)
  exact hnext μ' ((hsc.mono fun _ _ => Or.inl).trans h') (p'.trans (p₅.trans (p₄.trans (p₃.trans
    (p₂.trans p₁))))) c' a fun hn => by
      obtain ⟨u, v, w⟩ := b hn
      exact ⟨u, v, w.trans hgk⟩


/-- The rounded sum of row `r` after `l` multiply–adds. -/
private noncomputable def stSum (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) (st : ℕ → ℂ)
    (j r l : ℕ) : ℂ :=
  (List.range l).foldl (fun s l => linearComplex M (entryAt T (j - 1 - r) (j - r + l))
    ⟨M.lit 1, M.lit 0⟩ (st (j - r + l)) s) (entryAt T (j - 1 - r) j)

/-- The cells the sum of a row writes. -/
private def stSumFp (L : ℕ) : Fp :=
  Store.inBlock (L + 2) 0 2 ⊔ Store.inBlock (L + 3) 0 2 ⊔ Store.inBlock (L + 4) 0 2

private theorem stSumFp_le (L : ℕ) : stSumFp L ≤ stScratch L := by
  simp only [stSumFp, stScratch]; fp_sub

omit [Has IndexOp O] [Has CmpTst Q] in
/-- One multiply–add of the sum of a row. -/
private theorem rowSumBody_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {N j r l : ℕ}
    (hj : j < N) (hr : r < j) (hl : l < r) {t sm y g : ℕ × ℕ} {L : ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {st : ℕ → ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (ctx : StCtx M T smin t sm y g L μ.store) (htL : t.1 < L) (hyL : y.1 < L)
    (hD : Fp.Disj (stSumFp L) (stProt T t sm L))
    (hy₀ : μ.store.get y.1 (y.2 + 2 * (j * N + (j - r + l))) = some (st (j - r + l)).re)
    (hy₁ : μ.store.get y.1 (y.2 + 2 * (j * N + (j - r + l)) + 1) = some (st (j - r + l)).im)
    (hs₀ : μ.store.get (L + 2) 0 = some (stSum M T st j r l).re)
    (hs₁ : μ.store.get (L + 2) 1 = some (stSum M T st j r l).im) :
    Writes .total I τ (rowSumBody (O := O) (Q := Q)) ((stEnv N j t sm y g L r).pushIdx l)
      (stSumFp L) (fun μ' => μ'.pos = μ.pos ∧ StCtx M T smin t sm y g L μ'.store ∧
        μ'.store.get (L + 2) 0 = some (stSum M T st j r (l + 1)).re ∧
        μ'.store.get (L + 2) 1 = some (stSum M T st j r (l + 1)).im) μ := by
  have hi : j - 1 - r < N := by omega
  have hk : j - r + l < N := by omega
  have hTg := ctx.T_get hi hk
  have hlen := ctx.hlen
  have l3 := ctx.hl 3 (by omega)
  have l4 := ctx.hl 4 (by omega)
  have l2 := ctx.hl 2 (by omega)
  simp only [show (3 : ℕ) ≠ 5 by omega, show (4 : ℕ) ≠ 5 by omega, show (2 : ℕ) ≠ 5 by omega,
    if_false] at l3 l4 l2
  have hw := Pair.linearCombination_writes (τ := τ) (m := μ) hS
    (a := (t.1, t.2 + 2 * ((j - r + l) * N + (j - 1 - r)))) (b := (L, 0))
    (x := (y.1, y.2 + 2 * (j * N + (j - r + l)))) (y := (L + 2, 0)) (t := (L + 3, 0))
    (z := (L + 4, 0)) (av := ((entryAt T (j - 1 - r) (j - r + l)).re,
      (entryAt T (j - 1 - r) (j - r + l)).im)) (bv := (M.lit 1, M.lit 0))
    (xv := ((st (j - r + l)).re, (st (j - r + l)).im))
    (yv := ((stSum M T st j r l).re, (stSum M T st j r l).im))
    (by simp only [Fp.blocks]; disjoint) (by simp only [Fp.blocks]; disjoint) (by disjoint)
    hTg.1 hTg.2 ctx.one0 ctx.one1 hy₀ hy₁ hs₀ hs₁ (by simp [l3]) (by simp [l4])
  have hlive : μ.Live [(t.1, t.2 + 2 * ((j - r + l) * N + (j - 1 - r))), (L, 0),
      (y.1, y.2 + 2 * (j * N + (j - r + l))), (L + 2, 0), (L + 3, 0), (L + 4, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hlen]; omega
  refine hw.frame_seq_le rfl rfl hlive (by simp only [stSumFp]; fp_sub) fun μ₁ h₁ ⟨p₁, hR⟩ => ?_
  have c₁ := ctx.keep (h₁.mono (by simp only [stSumFp]; fp_sub)) hD
  have gR₀ : μ₁.store.get (L + 4) 0 = some (linearComplex M (entryAt T (j - 1 - r) (j - r + l))
      ⟨M.lit 1, M.lit 0⟩ (st (j - r + l)) (stSum M T st j r l)).re := by
    simpa [linearComplex] using Store.get_of_readBlock hR (j := 0) (by omega) 0
  have gR₁ : μ₁.store.get (L + 4) 1 = some (linearComplex M (entryAt T (j - 1 - r) (j - r + l))
      ⟨M.lit 1, M.lit 0⟩ (st (j - r + l)) (stSum M T st j r l)).im := by
    simpa [linearComplex] using Store.get_of_readBlock hR (j := 1) (by omega) 0
  have hsucc : stSum M T st j r (l + 1) = linearComplex M (entryAt T (j - 1 - r) (j - r + l))
      ⟨M.lit 1, M.lit 0⟩ (st (j - r + l)) (stSum M T st j r l) := by
    simp only [stSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hsucc]
  refine (writes_scalar_un (a := ⟨10, .const 0⟩) (z := ⟨8, .const 0⟩) (w := (L + 2, 0)) hS .copy
    (f := id) rfl rfl rfl gR₀ (by rw [c₁.hl 2 (by omega)]; simp)).seq_le
    (by simp only [stSumFp]; fp_sub) fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
  have gR₁' := h₂.keep (Store.readsOnly_get _ _ _) (by disjoint) gR₁
  refine (writes_scalar_un (a := ⟨10, .const 1⟩) (z := ⟨8, .const 1⟩) (w := (L + 2, 1)) hS .copy
    (f := id) rfl rfl rfl gR₁' (by rw [h₂.len_eq, c₁.hl 2 (by omega)]; simp)).mono
    (by simp only [stSumFp]; fp_sub) fun μ₃ h₃ ⟨p₃, g₃⟩ => ?_
  have hfr := (h₂.mono (show Store.inBlock (L + 2) 0 1 ≤ stSumFp L by
    simp only [stSumFp]; fp_sub)).trans (h₃.mono (show Store.inBlock (L + 2) 1 1 ≤ stSumFp L by
    simp only [stSumFp]; fp_sub))
  exact ⟨p₃.trans (p₂.trans p₁), c₁.keep hfr hD,
    h₃.keep (Store.readsOnly_get _ _ _) (by disjoint) g₂, g₃⟩

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The sum of a row. -/
private theorem rowSum_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {N j r : ℕ}
    (hj : j < N) (hr : r < j) {t sm y g : ℕ × ℕ} {L : ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {st : ℕ → ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (ctx : StCtx M T smin t sm y g L μ.store) (htL : t.1 < L) (hyL : y.1 < L)
    (hD : Fp.Disj (stSumFp L) (stProt T t sm L))
    (hy : ∀ k, j - r ≤ k → k < j → μ.store.get y.1 (y.2 + 2 * (j * N + k)) = some (st k).re ∧
      μ.store.get y.1 (y.2 + 2 * (j * N + k) + 1) = some (st k).im)
    {next : Stmt O Q} {F : Fp} {P : Mem ℝ → Prop} (hF : stSumFp L ≤ F)
    (hnext : ∀ μ', μ.store.EqOff (stSumFp L) μ'.store → μ'.pos = μ.pos →
      StCtx M T smin t sm y g L μ'.store →
      μ'.store.get (L + 2) 0 = some (stSum M T st j r r).re →
      μ'.store.get (L + 2) 1 = some (stSum M T st j r r).im →
      Writes .total I τ next (stEnv N j t sm y g L r) F P μ') :
    Writes .total I τ (rowSum next) (stEnv N j t sm y g L r) F P μ := by
  have hi : j - 1 - r < N := by omega
  have hTg := ctx.T_get hi hj
  have b0 : Store.inBlock (L + 2) 0 1 ≤ stSumFp L := by simp only [stSumFp]; fp_sub
  have b1 : Store.inBlock (L + 2) 1 1 ≤ stSumFp L := by simp only [stSumFp]; fp_sub
  refine (writes_scalar_un (z := ⟨8, .const 0⟩) (w := (L + 2, 0)) hS .copy (f := id) rfl rfl rfl
    hTg.1 (by rw [ctx.hl 2 (by omega)]; simp)).seq_le (b0.trans hF) fun μ₁ h₁ ⟨p₁, g₁⟩ => ?_
  have c₁ := ctx.keep (h₁.mono b0) hD
  refine (writes_scalar_un (z := ⟨8, .const 1⟩) (w := (L + 2, 1)) hS .copy (f := id) rfl rfl rfl
    (c₁.T_get hi hj).2 (by rw [c₁.hl 2 (by omega)]; simp)).seq_le (b1.trans hF)
    fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
  have c₂ := c₁.keep (h₂.mono b1) hD
  have g₁' := h₂.keep (Store.readsOnly_get _ _ _) (by disjoint) g₁
  have hfr₂ : μ.store.EqOff (stSumFp L) μ₂.store := (h₁.mono b0).trans (h₂.mono b1)
  have hyk : ∀ {s : Store ℝ}, μ.store.EqOff (stSumFp L) s → ∀ k, j - r ≤ k → k < j →
      s.get y.1 (y.2 + 2 * (j * N + k)) = some (st k).re ∧
        s.get y.1 (y.2 + 2 * (j * N + k) + 1) = some (st k).im := fun hs k h h' => by
    have hn : ∀ o, ¬ stSumFp L y.1 o := fun o => by
      simp only [stSumFp, Fp.sup_apply, Store.inBlock]; omega
    rw [hs.2 _ _ (hn _), hs.2 _ _ (hn _)]
    exact hy k h h'
  refine Writes.seq_le (writes_loop (N := r) (F := fun _ => stSumFp L)
    (P := fun l μ' => μ.store.EqOff (stSumFp L) μ'.store ∧ μ'.pos = μ.pos ∧
      StCtx M T smin t sm y g L μ'.store ∧
      μ'.store.get (L + 2) 0 = some (stSum M T st j r l).re ∧
      μ'.store.get (L + 2) 1 = some (stSum M T st j r l).im) rfl (fun _ _ => le_rfl)
    ⟨hfr₂, p₂.trans p₁, c₂, g₁', g₂⟩ fun l hl μ' _ ⟨hf, hp, hc, a, b⟩ => ?_) hF
    fun μ' _ ⟨hf, hp, hc, a, b⟩ => hnext μ' hf hp hc a b
  have hkl := hyk hf (j - r + l) (by omega) (by omega)
  refine (rowSumBody_writes hS hj hr hl hc htL hyL hD hkl.1 hkl.2 a b).mono le_rfl
    fun μ'' h'' ⟨p'', c'', a'', b''⟩ => ⟨hf.trans h'', p''.trans hp, c'', a'', b''⟩

omit [Has IndexOp O] [Has CmpTst Q] in
/-- The quotient of a row, negated into the column. -/
private theorem rowFinish_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) {N j r : ℕ}
    (hj : j < N) (hr : r < j) {t sm y g : ℕ × ℕ} {L : ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ} {s p : ℝ × ℝ}
    (ctx : StCtx M T smin t sm y g L μ.store) (hyL : y.1 < L)
    (hs₀ : μ.store.get (L + 2) 0 = some s.1) (hs₁ : μ.store.get (L + 2) 1 = some s.2)
    (hp₀ : μ.store.get (L + 1) 0 = some p.1) (hp₁ : μ.store.get (L + 1) 1 = some p.2) :
    Writes .total I τ (rowFinish (O := O) (Q := Q)) (stEnv N j t sm y g L r)
      (Store.inBlock (L + 5) 0 4 ⊔ Store.inBlock (L + 4) 0 2 ⊔
        Store.inBlock y.1 (y.2 + 2 * (j * N + (j - 1 - r))) 2)
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.store.get y.1 (y.2 + 2 * (j * N + (j - 1 - r))) =
          some (M.neg (Pair.divideWords M s p).1) ∧
        μ'.store.get y.1 (y.2 + 2 * (j * N + (j - 1 - r)) + 1) =
          some (M.neg (Pair.divideWords M s p).2)) μ := by
  have l4 := ctx.hl 4 (by omega)
  have l5 := ctx.hl 5 (by omega)
  simp only [show (4 : ℕ) ≠ 5 by omega, if_false, if_true] at l4 l5
  have hd := ShiftedQR.complexDivideWithScratch_writes_word (Op := O) (Tst := Q) (τ := τ) (m := μ)
    hS (x := (L + 2, 0)) (y := (L + 1, 0)) (t := (L + 5, 0)) (z := (L + 4, 0)) (xv := s) (yv := p)
    (by simp) (by simp) (by simp) hs₀ hs₁ hp₀ hp₁ (by simp [l5]) (by simp [l4])
  have hlive : μ.Live [(L + 2, 0), (L + 1, 0), (L + 5, 0), (L + 4, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true, ctx.hlen]; omega
  have hN : 2 * (j * N + (j - 1 - r)) + 1 < 2 * (N * N) := by
    have : (j + 1) * N ≤ N * N := Nat.mul_le_mul_right N hj
    have e : (j + 1) * N = j * N + N := by ring
    omega
  have hry := ctx.ry
  refine hd.frame_seq_le rfl rfl hlive (by simp only [Fp.blocks]; fp_sub)
    fun μ₁ h₁ ⟨p₁, hq⟩ => ?_
  have gq₀ : μ₁.store.get (L + 4) 0 = some (Pair.divideWords M s p).1 := by
    simpa using Store.get_of_readBlock hq (j := 0) (by omega) 0
  have gq₁ : μ₁.store.get (L + 4) 1 = some (Pair.divideWords M s p).2 := by
    simpa using Store.get_of_readBlock hq (j := 1) (by omega) 0
  have rl₁ : y.2 + 2 * (j * N + (j - 1 - r)) + 1 < μ₁.store.len y.1 := by
    rw [h₁.len_eq]; omega
  refine (writes_scalar_un (a := ⟨10, .const 0⟩)
    (z := ⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + rowI)⟩)
    (w := (y.1, y.2 + 2 * (j * N + (j - 1 - r)))) hS .neg (f := M.neg) rfl rfl rfl gq₀
    (by dsimp only; omega)).seq_le (by fp_sub) fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
  have gq₁' := h₂.keep (Store.readsOnly_get _ _ _) (by disjoint) gq₁
  refine (writes_scalar_un (a := ⟨10, .const 1⟩)
    (z := ⟨2, .var 4 + .const 2 * (.var 1 * .var 0 + rowI) + .const 1⟩)
    (w := (y.1, y.2 + 2 * (j * N + (j - 1 - r)) + 1)) hS .neg (f := M.neg) rfl rfl rfl gq₁'
    (by dsimp only; rw [h₂.len_eq]; omega)).mono (by fp_sub) fun μ₃ h₃ ⟨p₃, g₃⟩ => ?_
  refine ⟨p₃.trans (p₂.trans p₁), ?_, g₃⟩
  exact h₃.keep (Store.readsOnly_get _ _ _) (by disjoint) g₂


/-- The word recursion at a row whose pivot is floored. -/
private theorem shiftedTriSolveWord_succ_of_floored {M : Machine ℝ} {N : ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {j r : ℕ} (h : stFl M T smin j r) :
    shiftedTriSolveWord M T smin j (r + 1) =
      (Function.update (shiftedTriSolveWord M T smin j r).1 (j - 1 - r)
        ⟨M.neg (Pair.divideWords M
            ((stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).re,
              (stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).im) (smin, M.lit 0)).1,
          M.neg (Pair.divideWords M
            ((stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).re,
              (stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).im) (smin, M.lit 0)).2⟩,
        true) := by
  have h' : M.add (M.mul (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).re (entryAt T j j).re)
      (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).re (entryAt T j j).re))
      (M.mul (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).im (entryAt T j j).im)
        (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).im (entryAt T j j).im)) ≤ M.mul smin smin := h
  simp only [shiftedTriSolveWord, stSum, h', if_true, decide_true, Bool.or_true]

/-- The word recursion at a row whose pivot is not floored. -/
private theorem shiftedTriSolveWord_succ_of_not_floored {M : Machine ℝ} {N : ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {j r : ℕ} (h : ¬ stFl M T smin j r) :
    shiftedTriSolveWord M T smin j (r + 1) =
      (Function.update (shiftedTriSolveWord M T smin j r).1 (j - 1 - r)
        ⟨M.neg (Pair.divideWords M
            ((stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).re,
              (stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).im)
            ((stM M T j r).re, (stM M T j r).im)).1,
          M.neg (Pair.divideWords M
            ((stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).re,
              (stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).im)
            ((stM M T j r).re, (stM M T j r).im)).2⟩,
        (shiftedTriSolveWord M T smin j r).2) := by
  have h' : ¬ M.add (M.mul (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).re (entryAt T j j).re)
      (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).re (entryAt T j j).re))
      (M.mul (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).im (entryAt T j j).im)
        (M.sub (entryAt T (j - 1 - r) (j - 1 - r)).im (entryAt T j j).im)) ≤ M.mul smin smin := h
  simp only [shiftedTriSolveWord, stSum, stM, h', decide_false, Bool.or_false,
    Bool.false_eq_true, if_false]

/-- The invariant of the rows. -/
private def StInv (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) (smin : ℝ)
    (t sm y g : ℕ × ℕ) (L j : ℕ) (g₀ : Option ℝ) (r : ℕ) (μ : Mem ℝ) : Prop :=
  StCtx M T smin t sm y g L μ.store ∧
    (∀ k, j - r ≤ k → k < j →
      μ.store.get y.1 (y.2 + 2 * (j * N + k)) =
        some ((shiftedTriSolveWord M T smin j r).1 k).re ∧
      μ.store.get y.1 (y.2 + 2 * (j * N + k) + 1) =
        some ((shiftedTriSolveWord M T smin j r).1 k).im) ∧
    ((shiftedTriSolveWord M T smin j r).2 = true → μ.store.get g.1 g.2 = some (M.lit 1)) ∧
    ((shiftedTriSolveWord M T smin j r).2 = false → μ.store.get g.1 g.2 = g₀)

/-- Closing a row: the invariant after the negated quotient is stored. -/
private theorem StInv.succ {M : Machine ℝ} {N j r : ℕ} (hr : r < j)
    {t sm y g : ℕ × ℕ} {L : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {g₀ : Option ℝ}
    {s₁ : Store ℝ} {μ : Mem ℝ} {v : ℂ} {fl : Bool} {F : Fp}
    {w : (ℕ → ℂ) × Bool} (hw : shiftedTriSolveWord M T smin j (r + 1) =
      (Function.update w.1 (j - 1 - r) v, fl))
    (c : StCtx M T smin t sm y g L μ.store)
    (hy : ∀ k, j - r ≤ k → k < j → s₁.get y.1 (y.2 + 2 * (j * N + k)) = some (w.1 k).re ∧
      s₁.get y.1 (y.2 + 2 * (j * N + k) + 1) = some (w.1 k).im)
    (hfr : s₁.EqOff F μ.store)
    (hFy : ∀ o, F y.1 o → y.2 + 2 * (j * N + (j - 1 - r)) ≤ o ∧
      o < y.2 + 2 * (j * N + (j - 1 - r)) + 2)
    (g0 : μ.store.get y.1 (y.2 + 2 * (j * N + (j - 1 - r))) = some v.re)
    (g1 : μ.store.get y.1 (y.2 + 2 * (j * N + (j - 1 - r)) + 1) = some v.im)
    (hg₁ : fl = true → μ.store.get g.1 g.2 = some (M.lit 1))
    (hg₀ : fl = false → μ.store.get g.1 g.2 = g₀) :
    StInv M T smin t sm y g L j g₀ (r + 1) μ := by
  refine ⟨c, fun k hk hkj => ?_, ?_, ?_⟩
  · rw [hw]
    by_cases hki : k = j - 1 - r
    · subst hki
      simpa only [Function.update_self] using And.intro g0 g1
    · have hk' : j - r ≤ k := by omega
      have h := hy k hk' hkj
      simp only [Function.update_of_ne hki]
      have hn : ∀ o, o = y.2 + 2 * (j * N + k) ∨ o = y.2 + 2 * (j * N + k) + 1 → ¬ F y.1 o := by
        rintro o (rfl | rfl) hf <;> have := hFy _ hf <;> omega
      rw [hfr.2 _ _ (hn _ (Or.inl rfl)), hfr.2 _ _ (hn _ (Or.inr rfl))]
      exact h
  · rw [hw]; exact hg₁
  · rw [hw]; exact hg₀

/-- An entry above the diagonal of column `j` lies in the stored block. -/
private theorem st_col_lt {N j k : ℕ} (hj : j < N) (hk : k < j) :
    2 * (j * N + k) + 1 < 2 * (N * N) := by
  have : (j + 1) * N ≤ N * N := Nat.mul_le_mul_right N hj
  have e : (j + 1) * N = j * N + N := by ring
  omega

/-- The pair of row `r` lies in the written part of column `j`. -/
private theorem st_pair_le {N j r : ℕ} {y : ℕ × ℕ} (hr : r < j) :
    Store.inBlock y.1 (y.2 + 2 * (j * N + (j - 1 - r))) 2 ≤
      Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) := by
  rintro b o ⟨rfl, h₁, h₂⟩
  exact ⟨rfl, by omega, by omega⟩

/-- The footprint of the end of a row, and its disjointness from what the rows keep. -/
private theorem stFin_facts {N j r : ℕ} {t sm y g : ℕ × ℕ} {L : ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} (hj : j < N) (hr : r < j)
    (hD : Fp.Disj (stScratch L ⊔ Store.inBlock g.1 g.2 1) (stProt T t sm L))
    (hDy : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (stProt T t sm L)) :
    Store.inBlock (L + 5) 0 4 ⊔ Store.inBlock (L + 4) 0 2 ⊔
        Store.inBlock y.1 (y.2 + 2 * (j * N + (j - 1 - r))) 2 ≤
      stScratch L ⊔ Store.inBlock g.1 g.2 1 ⊔ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ∧
    Fp.Disj (Store.inBlock (L + 5) 0 4 ⊔ Store.inBlock (L + 4) 0 2 ⊔
      Store.inBlock y.1 (y.2 + 2 * (j * N + (j - 1 - r))) 2) (stProt T t sm L) := by
  have hPair := st_pair_le (y := y) (N := N) hr
  have hYc : Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ≤
      Store.inBlock y.1 y.2 (2 * (N * N)) := by
    rintro b o ⟨rfl, h₁, h₂⟩
    have := st_col_lt (N := N) hj (show j - 1 < j by omega)
    exact ⟨rfl, by omega, by omega⟩
  exact ⟨sup_le (sup_le (le_sup_of_le_left (le_sup_of_le_left (by simp only [stScratch]; fp_sub)))
      (le_sup_of_le_left (le_sup_of_le_left (by simp only [stScratch]; fp_sub))))
      (hPair.trans le_sup_right),
    Fp.disj_sup_left.mpr ⟨hD.mono (sup_le (le_sup_of_le_left (by simp only [stScratch]; fp_sub))
      (le_sup_of_le_left (by simp only [stScratch]; fp_sub))) le_rfl,
      hDy.mono (hPair.trans hYc) le_rfl⟩⟩

/-- One row of the substitution. -/
private theorem shiftedTriSolve_row {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j r : ℕ} (hj : j < N) (hr : r < j)
    {t sm y g : ℕ × ℕ} {L : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {g₀ : Option ℝ}
    {τ : Tape ℝ} {μ : Mem ℝ} (htL : t.1 < L) (hyL : y.1 < L) (hgL : g.1 < L)
    (hD : Fp.Disj (stScratch L ⊔ Store.inBlock g.1 g.2 1) (stProt T t sm L))
    (hDy : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (stProt T t sm L))
    (hyg : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1))
    (h : StInv M T smin t sm y g L j g₀ r μ) :
    Writes .total I τ (rowPivot (rowSum rowFinish)) (stEnv N j t sm y g L r)
      (stScratch L ⊔ Store.inBlock g.1 g.2 1 ⊔ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j))
      (fun μ' => μ'.pos = μ.pos ∧ StInv M T smin t sm y g L j g₀ (r + 1) μ') μ := by
  obtain ⟨ctx, hy, hf1, hf0⟩ := h
  have hcol : ∀ k < j, 2 * (j * N + k) + 1 < 2 * (N * N) := fun k hk => st_col_lt hj hk
  have hPair := st_pair_le (y := y) (N := N) hr
  have hnS : ∀ o, ¬ (stScratch L) y.1 o := fun o => by
    simp only [stScratch, Fp.sup_apply, Store.inBlock]; omega
  have hnG : ∀ k < j, ∀ o, o = y.2 + 2 * (j * N + k) ∨ o = y.2 + 2 * (j * N + k) + 1 →
      ¬ Store.inBlock g.1 g.2 1 y.1 o := fun k hk o ho hG => by
    refine hyg y.1 o ⟨rfl, ?_, ?_⟩ hG
    · rcases ho with rfl | rfl <;> omega
    · have := hcol k hk
      rcases ho with rfl | rfl <;> omega
  have hF₁ : stScratch L ⊔ Store.inBlock g.1 g.2 1 ≤
      stScratch L ⊔ Store.inBlock g.1 g.2 1 ⊔ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) :=
    le_sup_left
  refine rowPivot_writes hS hL hC hj hr ctx hD hgL hF₁ fun μ₁ e₁ p₁ c₁ hfl hnfl => ?_
  have hy₁ : ∀ k, j - r ≤ k → k < j →
      μ₁.store.get y.1 (y.2 + 2 * (j * N + k)) =
        some ((shiftedTriSolveWord M T smin j r).1 k).re ∧
      μ₁.store.get y.1 (y.2 + 2 * (j * N + k) + 1) =
        some ((shiftedTriSolveWord M T smin j r).1 k).im := fun k h₁ h₂ => by
    rw [e₁.2 _ _ (not_or.mpr ⟨hnS _, hnG k h₂ _ (Or.inl rfl)⟩),
      e₁.2 _ _ (not_or.mpr ⟨hnS _, hnG k h₂ _ (Or.inr rfl)⟩)]
    exact hy k h₁ h₂
  have hSum : stSumFp L ≤
      stScratch L ⊔ Store.inBlock g.1 g.2 1 ⊔ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) :=
    (stSumFp_le L).trans (le_sup_left.trans le_sup_left)
  refine rowSum_writes hS hj hr c₁ htL hyL (hD.mono ((stSumFp_le L).trans le_sup_left) le_rfl)
    hy₁ hSum fun μ₂ e₂ p₂ c₂ a b => ?_
  have hnSum : ∀ o, ¬ (stSumFp L) y.1 o := fun o h => hnS o (stSumFp_le L _ _ h)
  have hy₂ : ∀ k, j - r ≤ k → k < j →
      μ₂.store.get y.1 (y.2 + 2 * (j * N + k)) =
        some ((shiftedTriSolveWord M T smin j r).1 k).re ∧
      μ₂.store.get y.1 (y.2 + 2 * (j * N + k) + 1) =
        some ((shiftedTriSolveWord M T smin j r).1 k).im := fun k h₁ h₂ => by
    rw [e₂.2 _ _ (hnSum _), e₂.2 _ _ (hnSum _)]
    exact hy₁ k h₁ h₂
  have k1 : ∀ {o v}, μ₁.store.get (L + 1) o = some v → μ₂.store.get (L + 1) o = some v :=
    fun h => by rw [e₂.2 _ _ (by simp only [stSumFp, Fp.sup_apply, Store.inBlock]; omega)]; exact h
  have kg : μ₂.store.get g.1 g.2 = μ₁.store.get g.1 g.2 :=
    e₂.2 _ _ (by simp only [stSumFp, Fp.sup_apply, Store.inBlock]; omega)
  obtain ⟨hFin, hDF⟩ := stFin_facts (g := g) hj hr hD hDy
  have hFy : ∀ o, (Store.inBlock (L + 5) 0 4 ⊔ Store.inBlock (L + 4) 0 2 ⊔
      Store.inBlock y.1 (y.2 + 2 * (j * N + (j - 1 - r))) 2) y.1 o →
      y.2 + 2 * (j * N + (j - 1 - r)) ≤ o ∧ o < y.2 + 2 * (j * N + (j - 1 - r)) + 2 := by
    intro o ho
    simp only [Fp.sup_apply, Store.inBlock] at ho
    omega
  have hg₃ : ∀ {μ₃ : Mem ℝ}, μ₂.store.EqOff (Store.inBlock (L + 5) 0 4 ⊔
      Store.inBlock (L + 4) 0 2 ⊔ Store.inBlock y.1 (y.2 + 2 * (j * N + (j - 1 - r))) 2) μ₃.store →
      μ₃.store.get g.1 g.2 = μ₁.store.get g.1 g.2 := fun {μ₃} e₃ => by
    rw [e₃.2 _ _ ?_, kg]
    rintro ((⟨h, -⟩ | ⟨h, -⟩) | hy')
    · omega
    · omega
    · have h₁ := hcol (j - 1 - r) (by omega)
      refine hyg g.1 g.2 ⟨hy'.1, ?_, ?_⟩ ⟨rfl, le_rfl, by omega⟩
      · have := hy'.2.1; omega
      · have := hy'.2.2; omega
  by_cases hfl' : stFl M T smin j r
  · obtain ⟨m0, m1, gl⟩ := hfl hfl'
    refine (rowFinish_writes (s := ((stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).re,
      (stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).im)) (p := (smin, M.lit 0))
      hS hj hr c₂ hyL a b (k1 m0) (k1 m1)).mono hFin
      fun μ₃ e₃ ⟨p₃, q0, q1⟩ => ⟨p₃.trans (p₂.trans p₁), ?_⟩
    exact StInv.succ (w := shiftedTriSolveWord M T smin j r) hr
      (shiftedTriSolveWord_succ_of_floored hfl') (c₂.keep e₃ hDF) hy₂ e₃ hFy q0 q1
      (fun _ => (hg₃ e₃).trans gl) (fun h => absurd h (by decide))
  · obtain ⟨m0, m1, gl⟩ := hnfl hfl'
    refine (rowFinish_writes (s := ((stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).re,
      (stSum M T (shiftedTriSolveWord M T smin j r).1 j r r).im))
      (p := ((stM M T j r).re, (stM M T j r).im)) hS hj hr c₂ hyL a b
      (k1 m0) (k1 m1)).mono hFin fun μ₃ e₃ ⟨p₃, q0, q1⟩ => ⟨p₃.trans (p₂.trans p₁), ?_⟩
    exact StInv.succ (w := shiftedTriSolveWord M T smin j r) hr
      (shiftedTriSolveWord_succ_of_not_floored hfl') (c₂.keep e₃ hDF) hy₂ e₃ hFy q0 q1
      (fun h => ((hg₃ e₃).trans gl).trans (hf1 h)) (fun h => ((hg₃ e₃).trans gl).trans (hf0 h))


/-- The loop over the rows. -/
private theorem shiftedTriSolve_rows {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j : ℕ} (hj : j < N)
    {t sm y g : ℕ × ℕ} {L : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ}
    {τ : Tape ℝ} {μ : Mem ℝ} (htL : t.1 < L) (hyL : y.1 < L) (hgL : g.1 < L)
    (hD : Fp.Disj (stScratch L ⊔ Store.inBlock g.1 g.2 1) (stProt T t sm L))
    (hDy : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (stProt T t sm L))
    (hyg : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1))
    (ctx : StCtx M T smin t sm y g L μ.store) :
    Writes .total I τ (.loop (.var 1) (rowPivot (O := O) (Q := Q) (rowSum rowFinish)))
      ⟨[N, j, t.2, sm.2, y.2, g.2, y.2, g.2],
        [t.1, sm.1, y.1, g.1, y.1, g.1, L, L + 1, L + 2, L + 3, L + 4, L + 5, L + 6]⟩
      (stScratch L ⊔ Store.inBlock g.1 g.2 1 ⊔ Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j))
      (fun μ' => μ'.pos = μ.pos ∧ StInv M T smin t sm y g L j (μ.store.get g.1 g.2) j μ') μ := by
  refine writes_loop (N := j) rfl (fun _ => _) (fun _ _ => le_rfl)
    (fun r μ' => μ'.pos = μ.pos ∧ StInv M T smin t sm y g L j (μ.store.get g.1 g.2) r μ')
    ⟨rfl, ctx, fun k h₁ h₂ => by omega, fun h => by simp [shiftedTriSolveWord] at h,
      fun _ => rfl⟩ fun r hr μ' _ ⟨hp, hinv⟩ => ?_
  exact (shiftedTriSolve_row (r := r) hS hL hC hj hr htL hyL hgL hD hDy hyg hinv).mono le_rfl
    fun μ'' _ ⟨hp', h'⟩ => ⟨hp'.trans hp, h'⟩

/-- The disjointness facts of the rows, from the apartness of the operands. -/
private theorem stDisj {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {t sm y g : ℕ × ℕ} {L : ℕ}
    (htL : t.1 < L) (hsL : sm.1 < L) (hyL : y.1 < L) (hgL : g.1 < L)
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Fp.Disj (stScratch L ⊔ Store.inBlock g.1 g.2 1) (stProt T t sm L) ∧
      Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (stProt T t sm L) ∧
      Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) := by
  have hty : Fp.Disj (Store.inBlock t.1 t.2 (2 * (N * N))) (Store.inBlock y.1 y.2 (2 * (N * N))) :=
    hap.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  have htg : Fp.Disj (Store.inBlock t.1 t.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) :=
    hap.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  have hsy : Fp.Disj (Store.inBlock sm.1 sm.2 1) (Store.inBlock y.1 y.2 (2 * (N * N))) :=
    hap.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  have hsg : Fp.Disj (Store.inBlock sm.1 sm.2 1) (Store.inBlock g.1 g.2 1) :=
    hap.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  have hyg : Fp.Disj (Store.inBlock y.1 y.2 (2 * (N * N))) (Store.inBlock g.1 g.2 1) :=
    hap.2.2.1.mono le_rfl (by simp only [Fp.blocks]; fp_sub)
  refine ⟨?_, ?_, hyg⟩
  · rintro b i (hs | hG) (((ht | hs') | hL') | h6)
    · simp only [stScratch, Fp.sup_apply, Store.inBlock] at hs ht; omega
    · simp only [stScratch, Fp.sup_apply, Store.inBlock] at hs hs'; omega
    · simp only [stScratch, Fp.sup_apply, Store.inBlock] at hs hL'; omega
    · simp only [stScratch, Fp.sup_apply, Store.inBlock] at hs h6; omega
    · exact htg b i ht hG
    · exact hsg b i hs' hG
    · have := hG.1; have := hL'.1; omega
    · have := hG.1; have := h6.1; omega
  · rintro b i hy (((ht | hs') | hL') | h6)
    · exact hty b i ht hy
    · exact hsy b i hs' hy
    · have := hy.1; have := hL'.1; omega
    · have := hy.1; have := h6.1; omega

/-- **The program stores the computed words**: on a scalar machine with index literals and exact
comparisons, from a memory holding $\mathbf{T}$ of order $N$ at `t`, the floor $s_{\min}$ at `sm`,
room for `Y` and a flag word at `g`, the four blocks live and apart, and $j < N$, the run writes
only the first $j$ entries of column $j$ of `Y` and the flag: they hold the words of
`NLAlib.shiftedTriSolveWord`, and the flag is the literal $1$ if a pivot was floored and unchanged
otherwise. -/
theorem shiftedTriSolve_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j : ℕ} (hj : j < N) {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (shiftedTriSolve (O := O) (Q := Q))
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => (∀ i < j, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) =
            some ((shiftedTriSolveWord M T smin j j).1 i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) =
            some ((shiftedTriSolveWord M T smin j j).1 i).im) ∧
        (shiftedTriSolveFlag M T smin j = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (shiftedTriSolveFlag M T smin j = false →
          μ'.store.get g.1 g.2 = μ.store.get g.1 g.2)) μ := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  obtain ⟨htl, hsl, hyl, hgl⟩ := hl
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  obtain ⟨hyr, hgr⟩ := hroom
  rw [shiftedTriSolve_eq]
  refine writes_allocs_preserving_post (ns := [2, 2, 2, 2, 2, 4, 2]) rfl
    (fun {s s' p} hB ⟨h₁, h₂, h₃⟩ => ⟨fun i hi => ?_, fun h => ?_, fun h => ?_⟩) ?_
  · have := h₁ i hi
    exact ⟨hB.get_of hyl this.1, hB.get_of hyl this.2⟩
  · exact hB.get_of hgl (h₂ h)
  · exact ((hB g.1 hgl).2 g.2).trans (h₃ h)
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hl7 : ∀ k < 7, s₁.len (L + k) = if k = 5 then 4 else 2 := fun k hk => by
    have := hlens k (by simpa using hk)
    interval_cases k <;> simpa using this
  have hb0 : ∀ L', Store.inBlock L' 0 1 ≤ Fp.above L' := fun _ _ _ h => h.1 ▸ le_rfl
  have hb1 : ∀ L', Store.inBlock L' 1 1 ≤ Fp.above L' := fun _ _ _ h => h.1 ▸ le_rfl
  have hb6 : ∀ L', Store.inBlock (L' + 6) 1 1 ≤ Fp.above L' := fun L' b _ h => by
    have := h.1; change L' ≤ b; omega
  have hAbove : ∀ {b o n}, L ≤ b → Store.inBlock b o n ≤ (Store.inBlock y.1 (y.2 + 2 * (j * N))
      (2 * j) ⊔ Store.inBlock g.1 g.2 1) ⊔ Fp.above L := fun hb _ _ h =>
    Or.inr (show L ≤ _ from h.1 ▸ hb)
  refine (writes_call_const (hS (.lit 1)) (out := ⟨6, .const 0⟩) (z := (L, 0)) rfl trivial
    (by have := hl7 0 (by omega); simp only [Nat.add_zero] at this; simp [this])).seq_le
    (hAbove le_rfl) fun μ₁ h₁ ⟨p₁, g₁⟩ => ?_
  refine (writes_call_const (hS (.lit 0)) (out := ⟨6, .const 1⟩) (z := (L, 1)) rfl trivial
    (by have := hl7 0 (by omega); simp only [Nat.add_zero] at this; simp [h₁.len_eq, this])).seq_le
    (hAbove le_rfl) fun μ₂ h₂ ⟨p₂, g₂⟩ => ?_
  have hsm₂ : μ₂.store.get sm.1 sm.2 = some smin := by
    rw [h₂.2 _ _ (by simp only [Store.inBlock]; omega), h₁.2 _ _ (by
      simp only [Store.inBlock]; omega), (hBelow sm.1 hsl).2]
    exact hsm
  refine (writes_scalar_bin (a := ⟨1, .var 3⟩) (b := ⟨1, .var 3⟩) (z := ⟨12, .const 1⟩)
    (w := (L + 6, 1)) hS .mul (f := M.mul) rfl rfl rfl rfl hsm₂ hsm₂ (by
      have := hl7 6 (by omega); simp [h₂.len_eq, h₁.len_eq, this])).seq_le
    (hAbove (by omega)) fun μ₃ h₃ ⟨p₃, g₃⟩ => ?_
  have hkA : ∀ {b o v}, b < L → s₁.get b o = some v → μ₃.store.get b o = some v := by
    intro b o v hb hv
    rw [h₃.2 _ _ (by simp only [Store.inBlock]; omega), h₂.2 _ _ (by
      simp only [Store.inBlock]; omega), h₁.2 _ _ (by simp only [Store.inBlock]; omega)]
    exact hv
  have hfrA : s₁.EqOff (Fp.above L) μ₃.store :=
    ((h₁.mono (hb0 L)).trans (h₂.mono (hb1 L))).trans (h₃.mono (hb6 L))
  have ctx : StCtx M T smin t sm y g L μ₃.store :=
    { hT := (hT.of_below hBelow htl).of_eqOff hfrA fun b i hb hG => by
        have := hG.1; have : L ≤ b := hb; omega
      hsm := hkA hsl ((hBelow sm.1 hsl).2 _ ▸ hsm)
      hlen := by rw [h₃.length_eq, h₂.length_eq, h₁.length_eq]; simpa using hlen
      hl := fun k hk => by rw [h₃.len_eq, h₂.len_eq, h₁.len_eq]; exact hl7 k hk
      one0 := by
        rw [h₃.2 _ _ (by simp only [Store.inBlock]; omega), h₂.2 _ _ (by
          simp only [Store.inBlock]; omega)]
        exact g₁
      one1 := by rw [h₃.2 _ _ (by simp only [Store.inBlock]; omega)]; exact g₂
      sq := g₃
      ry := by rw [h₃.len_eq, h₂.len_eq, h₁.len_eq, (hBelow y.1 hyl).1]; exact hyr
      rg := by rw [h₃.len_eq, h₂.len_eq, h₁.len_eq, (hBelow g.1 hgl).1]; exact hgr }
  have hgk : μ₃.store.get g.1 g.2 = μ.store.get g.1 g.2 := by
    rw [hfrA.2 _ _ (by change ¬ L ≤ g.1; omega), (hBelow g.1 hgl).2]
  obtain ⟨hD, hDy, hyg⟩ := stDisj (T := T) htl hsl hyl hgl hap
  refine (shiftedTriSolve_rows hS hL hC hj htl hyl hgl hD hDy hyg ctx).mono ?_ ?_
  · refine sup_le (sup_le ?_ (le_sup_of_le_left le_sup_right))
      (le_sup_of_le_left le_sup_left)
    intro b o h
    refine Or.inr (show L ≤ b from ?_)
    simp only [stScratch, Fp.sup_apply, Store.inBlock] at h
    omega
  · rintro μ' - ⟨-, -, hy', h1, h0⟩
    refine ⟨fun i hi => hy' i (by omega) hi, h1, fun h => (h0 h).trans hgk⟩

/-- **Rounded shifted back substitution under the standard model**: on a scalar machine with the
standard model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact
comparisons, from the memory of `NLAlib.shiftedTriSolve_writes_word` with $\mathbf{T}$ upper
triangular, $s_{\min} \ge 0$ and $j < N$, the run stores the first $j$ entries of a column
$\mathbf{y}$ with $y_j = 1$, $y_i = 0$ for $i > j$, that is a componentwise backward solution of
$(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with $16(N + 1)\boldsymbol{u}$ and the
floor $3s_{\min}$ if the flag was set, $0$ if the flag is unchanged; the flag is unchanged when
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i < j$. -/
theorem shiftedTriSolve_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 < smin) (j : Fin N) {τ : Tape ℝ}
    {μ : Mem ℝ} (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (shiftedTriSolve (O := O) (Q := Q))
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (yv : Fin N → ℂ) (fl : Bool),
        (∀ i : Fin N, (i : ℕ) < j → μ'.store.get y.1 (y.2 + 2 * (j * N + i)) = some (yv i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) = some (yv i).im) ∧
        yv j = 1 ∧ (∀ i : Fin N, j < i → yv i = 0) ∧
        IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u) (if fl then 3 * smin else 0)
          (T - T j j • 1) 0 yv ∧
        (fl = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (fl = false → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) ∧
        ((∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) → fl = false)) μ := by
  have hu32 : u ≤ 1 / 32 := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hu0 : 0 ≤ u := by
      have := hM.lit 1
      simp only [Rat.cast_one, abs_one, mul_one, id] at this
      exact (abs_nonneg _).trans this
    nlinarith
  refine (shiftedTriSolve_writes_word hS hL hC j.isLt hT hsm hl hroom hap).mono le_rfl
    fun μ' _ ⟨hy, h1, h0⟩ => ⟨shiftedTriSolveColumn M T smin j, shiftedTriSolveFlag M T smin j,
      fun i hi => by simpa only [shiftedTriSolveColumn, hi, if_true] using hy i hi,
      by simp [shiftedTriSolveColumn],
      fun i hi => by simp [shiftedTriSolveColumn, not_lt.mpr hi.le, (Fin.val_ne_of_ne hi.ne')],
      shiftedTriSolve_isComponentwiseBackwardSolution hM hu hTu hsmin j, h1, h0,
      fun hgap => shiftedTriSolve_flag hM hu32 hsmin.le j hgap⟩

end Writes

end NLAlib
