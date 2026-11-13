/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.SpatialScalar

/-!
# Actual arithmetic of the next bisection level

The radius and tolerance use the stored constants and the actual rounded dimension literal.
A shared straight-line scalar-block rule accounts for all six arithmetic calls; separation of
bounded scalar addresses follows from the operand regions, including shared-buffer views.

## Main results

* `NLAlib.SpectralBisection.writes_levelParameters` computes the next stored level parameters.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] {M : Machine K}

private def levelIns : List (ScalarIns ScalarOp) :=
  let c (i : ℕ) : Operand := ⟨0, if i = 0 then .var 2 else .var 2 + .const i⟩
  let t (i : ℕ) : Operand := ⟨2, if i = 0 then .var 4 else .var 4 + .const i⟩
  let prev (i : ℕ) : Operand :=
    ⟨1, .var 3 + if i = 0 then .const 2 * .var 1 else .const 2 * .var 1 + .const i⟩
  let next (i : ℕ) : Operand :=
    ⟨1, .var 3 + if i = 0 then .const 2 * (.var 1 + .const 1)
      else .const 2 * (.var 1 + .const 1) + .const i⟩
  [⟨.div, [c 1, t 0], t 2⟩, ⟨.add, [c 2, t 2], t 3⟩,
    ⟨.mul, [t 3, prev 0], next 0⟩, ⟨.div, [c 0, t 0], t 1⟩,
    ⟨.sub, [c 0, t 1], t 3⟩, ⟨.mul, [t 3, prev 1], next 1⟩]

private def levelTail : Impl Op Tst := opsImpl% [L, d] (c, Lv, t) → (Lv, t) {
  call (Has.inj ScalarOp.div) [] (c[1], t) → (t[2]);
  call (Has.inj ScalarOp.add) [] (c[2], t[2]) → (t[3]);
  call (Has.inj ScalarOp.mul) [] (t[3], Lv[2 * d]) → (Lv[2 * (d + 1)]);
  call (Has.inj ScalarOp.div) [] (c, t) → (t[1]);
  call (Has.inj ScalarOp.sub) [] (c, t[1]) → (t[3]);
  call (Has.inj ScalarOp.mul) [] (t[3], Lv[2 * d + 1]) → (Lv[2 * (d + 1) + 1])
}

private theorem eval_levelRadius {L d : ℕ} {c lv t : ℕ × ℕ}
    (f : ℕ × ℕ → Option K) (two half R den : K)
    (hc1 : f (c.1, c.2 + 1) = some two) (hc2 : f (c.1, c.2 + 2) = some half)
    (hR : f (lv.1, lv.2 + 2 * d) = some R) (hden : f t = some den)
    (hC22 : (c.1, c.2 + 2) ≠ (t.1, t.2 + 2))
    (hR02 : (lv.1, lv.2 + 2 * d) ≠ (t.1, t.2 + 2))
    (hR03 : (lv.1, lv.2 + 2 * d) ≠ (t.1, t.2 + 3)) :
    ScalarIns.evalBlock M.eval (Env.frame [L, d] [c, lv, t, lv, t]) (levelIns.take 3) f =
      some [((t.1, t.2 + 2), M.div two den),
        ((t.1, t.2 + 3), M.add half (M.div two den)),
        ((lv.1, lv.2 + 2 * (d + 1)), M.mul (M.add half (M.div two den)) R)] := by
  simp [levelIns, ScalarIns.evalBlock, Operand.evalList, Operand.eval, IExp.eval, Env.frame,
    Machine.eval, hc1, hc2, hR, hden, hC22, hR02, hR03]

private theorem eval_levelTolerance {L d : ℕ} {c lv t : ℕ × ℕ}
    (f : ℕ × ℕ → Option K) (one eps den : K)
    (hc0 : f c = some one) (hE : f (lv.1, lv.2 + (2 * d + 1)) = some eps)
    (hden : f t = some den) (hC01 : c ≠ (t.1, t.2 + 1))
    (hR11 : (lv.1, lv.2 + (2 * d + 1)) ≠ (t.1, t.2 + 1))
    (hR13 : (lv.1, lv.2 + (2 * d + 1)) ≠ (t.1, t.2 + 3)) :
    ScalarIns.evalBlock M.eval (Env.frame [L, d] [c, lv, t, lv, t]) (levelIns.drop 3) f =
      some [((t.1, t.2 + 1), M.div one den), ((t.1, t.2 + 3), M.sub one (M.div one den)),
        ((lv.1, lv.2 + (2 * (d + 1) + 1)), M.mul (M.sub one (M.div one den)) eps)] := by
  simp [levelIns, ScalarIns.evalBlock, Operand.evalList, Operand.eval, IExp.eval, Env.frame,
    Machine.eval, hc0, hE, hden, hC01, hR11, hR13]

omit [Has IndexOp Op] in
private theorem eval_levelIns {L d : ℕ} {c lv t : ℕ × ℕ} {m : Mem K}
    (one two half R eps den : K)
    (hAP : Fp.Apart [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), t]
      [3, 2, 2, 4])
    (hc : m.store.readBlock c.1 c.2 3 = some [one, two, half])
    (hLv : m.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hden : m.store.get t.1 t.2 = some den) :
    ScalarIns.evalBlock M.eval (Env.frame [L, d] [c, lv, t, lv, t]) levelIns
      m.store.cellFn = some
      [((t.1, t.2 + 2), M.div two den), ((t.1, t.2 + 3), M.add half (M.div two den)),
        ((lv.1, lv.2 + 2 * (d + 1)), M.mul (M.add half (M.div two den)) R),
        ((t.1, t.2 + 1), M.div one den), ((t.1, t.2 + 3), M.sub one (M.div one den)),
        ((lv.1, lv.2 + (2 * (d + 1) + 1)), M.mul (M.sub one (M.div one den)) eps)] := by
  have hc0 : m.store.get c.1 c.2 = some one := by
    simpa using Store.get_of_readBlock hc (j := 0) (by simp) one
  have hc1 : m.store.get c.1 (c.2 + 1) = some two := by
    simpa using Store.get_of_readBlock hc (j := 1) (by simp) one
  have hc2 : m.store.get c.1 (c.2 + 2) = some half := by
    simpa using Store.get_of_readBlock hc (j := 2) (by simp) one
  have hR : m.store.get lv.1 (lv.2 + 2 * d) = some R := by
    simpa using Store.get_of_readBlock hLv (j := 0) (by simp) one
  have hE : m.store.get lv.1 (lv.2 + (2 * d + 1)) = some eps := by
    simpa [Nat.add_assoc] using Store.get_of_readBlock hLv (j := 1) (by simp) one
  have hd (i j : Fin 4) (hij : i ≠ j) :=
    hAP.disj_getD i.isLt j.isLt (fun he => hij (Fin.ext he))
  have hct : Fp.Disj (Store.inBlock c.1 c.2 3) (Store.inBlock t.1 t.2 4) := by
    simpa using hd 0 3 (by simp)
  have hcn : Fp.Disj (Store.inBlock c.1 c.2 3)
      (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2) := by simpa using hd 0 2 (by simp)
  have hrt : Fp.Disj (Store.inBlock lv.1 (lv.2 + 2 * d) 2)
      (Store.inBlock t.1 t.2 4) := by simpa using hd 1 3 (by simp)
  have hrn : Fp.Disj (Store.inBlock lv.1 (lv.2 + 2 * d) 2)
      (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2) := by simpa using hd 1 2 (by simp)
  have htn : Fp.Disj (Store.inBlock t.1 t.2 4)
      (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2) := by simpa using hd 3 2 (by simp)
  have hC02 := hct.ne_offsets (i := 0) (j := 2) (by simp) (by simp)
  have hC03 := hct.ne_offsets (i := 0) (j := 3) (by simp) (by simp)
  have hC01 := hct.ne_offsets (i := 0) (j := 1) (by simp) (by simp)
  have hC22 := hct.ne_offsets (i := 2) (j := 2) (by simp) (by simp)
  have hCN := hcn.ne_offsets (i := 0) (j := 0) (by simp) (by simp)
  have hR02 := hrt.ne_offsets (i := 0) (j := 2) (by simp) (by simp)
  have hR03 := hrt.ne_offsets (i := 0) (j := 3) (by simp) (by simp)
  have hR12 := hrt.ne_offsets (i := 1) (j := 2) (by simp) (by simp)
  have hR13 := hrt.ne_offsets (i := 1) (j := 3) (by simp) (by simp)
  have hR11 := hrt.ne_offsets (i := 1) (j := 1) (by simp) (by simp)
  have hRN := hrn.ne_offsets (i := 1) (j := 0) (by simp) (by simp)
  have hTN := htn.ne_offsets (i := 0) (j := 0) (by simp) (by simp)
  simp only [Nat.add_zero] at hC02 hC03 hC01 hC22 hCN hR02 hR03
  simp only [Nat.add_zero, Nat.add_assoc] at hR12 hR13 hR11 hRN hTN
  have hfirst := eval_levelRadius (M := M) (L := L) (d := d) (c := c) (lv := lv) (t := t)
    m.store.cellFn two half R den
    hc1 hc2 hR hden hC22 hR02 hR03
  let f3 := ScalarIns.applyWrites m.store.cellFn
    [((t.1, t.2 + 2), M.div two den), ((t.1, t.2 + 3), M.add half (M.div two den)),
      ((lv.1, lv.2 + 2 * (d + 1)), M.mul (M.add half (M.div two den)) R)]
  have hfC : f3 c = some one := by
    simp [f3, ScalarIns.applyWrites, hc0, Store.cellFn, hC02, hC03, hCN]
  have hfT : f3 t = some den := by
    rcases t with ⟨tb, off⟩
    simp [f3, ScalarIns.applyWrites, hden, Store.cellFn, hTN, Prod.mk.injEq]
  have hfE : f3 (lv.1, lv.2 + (2 * d + 1)) = some eps := by
    simp [f3, ScalarIns.applyWrites, hE, Store.cellFn, hR12, hR13, hRN]
  have hsecond := eval_levelTolerance (M := M) (L := L) (d := d) (c := c) (lv := lv) (t := t)
    f3 one eps den hfC hfE hfT
    hC01 hR11 hR13
  rw [← List.take_append_drop 3 levelIns, ScalarIns.evalBlock_append_some hfirst, hsecond]
  rfl


omit [Has IndexOp Op] in
private theorem writes_levelTail {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K}
    {L d : ℕ} {c lv t : ℕ × ℕ} {m : Mem K} (one two half R eps den : K)
    (hAP : Fp.Apart [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), t]
      [3, 2, 2, 4])
    (hc : m.store.readBlock c.1 c.2 3 = some [one, two, half])
    (hLv : m.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hden : m.store.get t.1 t.2 = some den)
    (hroom : lv.2 + 2 * (d + 1) + 2 ≤ m.store.len lv.1)
    (ht : t.2 + 4 ≤ m.store.len t.1) :
    Writes .total I τ levelTail.body (Env.frame [L, d] [c, lv, t, lv, t])
      (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2 ⊔ Store.inBlock t.1 t.2 4)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
        some [M.mul (M.add half (M.div two den)) R,
          M.mul (M.sub one (M.div one den)) eps]) m := by
  let r := M.mul (M.add half (M.div two den)) R
  let e := M.mul (M.sub one (M.div one den)) eps
  let pre := [((t.1, t.2 + 2), M.div two den),
    ((t.1, t.2 + 3), M.add half (M.div two den))]
  let post := [((t.1, t.2 + 1), M.div one den),
    ((t.1, t.2 + 3), M.sub one (M.div one den)),
    ((lv.1, lv.2 + 2 * (d + 1) + 1), e)]
  let ws := pre ++ ((lv.1, lv.2 + 2 * (d + 1)), r) :: post
  have hev : ScalarIns.evalBlock M.eval (Env.frame [L, d] [c, lv, t, lv, t]) levelIns
      m.store.cellFn = some ws := by
    simpa [ws, pre, post, r, e, Nat.add_assoc] using
      (eval_levelIns (M := M) one two half R eps den hAP hc hLv hden)
  have hroomWs : ∀ z ∈ ws, z.1.2 < m.store.len z.1.1 := by
    intro z hz
    simp only [ws, pre, post, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  have hw := writes_machineScalarBlock (τ := τ) hS hev hroomWs
  change Writes .total I τ levelTail.body _ _ _ m at hw
  refine hw.mono ?_ ?_
  · intro b i hi
    rcases lv with ⟨lb, lo⟩; rcases t with ⟨tb, off⟩
    simp only [ws, pre, post, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Fp.cells, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact Or.inl ⟨rfl, by omega, by omega⟩
            | exact Or.inr ⟨rfl, by omega, by omega⟩
  · rintro μ _ rfl
    have hnt : Fp.Disj (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2)
        (Store.inBlock t.1 t.2 4) := by
      simpa using hAP.disj_getD (i := 2) (j := 3) (by simp) (by simp) (by simp)
    have hN1 := hnt.ne_offsets (i := 0) (j := 1) (by simp) (by simp)
    have hN3 := hnt.ne_offsets (i := 0) (j := 3) (by simp) (by simp)
    simp only [Nat.add_zero] at hN1 hN3
    have h0 := get_updCells (m := m) (ws₁ := pre) (ws₂ := post)
      (z := (lv.1, lv.2 + 2 * (d + 1))) (v := r) (by dsimp; omega)
      (by simp [post, hN1, hN3, Prod.mk.injEq])
    have h1 := get_updCells (m := m)
      (ws₁ := pre ++ [((lv.1, lv.2 + 2 * (d + 1)), r),
        ((t.1, t.2 + 1), M.div one den), ((t.1, t.2 + 3), M.sub one (M.div one den))])
      (ws₂ := []) (z := (lv.1, lv.2 + 2 * (d + 1) + 1)) (v := e)
      (by dsimp; omega) (by simp)
    refine ⟨by simp [ws, pre, post, Mem.updCells], ?_⟩
    rw [Store.readBlock_succ, h0, Option.bind_some, Store.readBlock_succ]
    have h1' : (m.updCells ws).store.get lv.1 (lv.2 + 2 * (d + 1) + 1) = some e := by
      simpa [ws, pre, post, List.append_assoc] using h1
    rw [h1', Option.bind_some]
    rfl

/-- The level program writes the rounded next radius and tolerance from the actual stored
constants, current parameters and dimension literal. Separation is spatial; the two adjacent
parameter pairs occupy disjoint regions of the same level arena. No nonzero-denominator or
successful-execution hypothesis is needed for the functional word computation. -/
theorem writes_levelParameters {I : Interp Op Tst K} (hS : IsScalar M I)
    (hIndex : IsIndexLit M I) {τ : Tape K} {L d : ℕ} {c lv t : ℕ × ℕ} {m : Mem K}
    (one two half R eps : K)
    (hAP : Fp.Apart [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), t]
      [3, 2, 2, 4])
    (hc : m.store.readBlock c.1 c.2 3 = some [one, two, half])
    (hLv : m.store.readBlock lv.1 (lv.2 + 2 * d) 2 = some [R, eps])
    (hroom : lv.2 + 2 * (d + 1) + 2 ≤ m.store.len lv.1)
    (ht : t.2 + 4 ≤ m.store.len t.1) :
    Writes .total I τ levelParameters.body (Env.frame [L, d] [c, lv, t, lv, t])
      (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2 ⊔ Store.inBlock t.1 t.2 4)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
        some [M.mul (M.add half (M.div two (M.lit (L + d : ℕ)))) R,
          M.mul (M.sub one (M.div one (M.lit (L + d : ℕ)))) eps]) m := by
  have hi := writes_indexLit (m := m) (τ := τ)
    (ρ := Env.frame [L, d] [c, lv, t, lv, t]) hIndex
    (e := .var 0 + .var 1) (out := ⟨2, .var 4⟩) rfl rfl (by dsimp; omega)
  refine hi.seq_le ((Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_right)
    fun μ hfr hden => ?_
  have hct : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock c.1 c.2 3) := by
    exact (hAP.disj_getD (i := 3) (j := 0) (by simp) (by simp) (by simp)).mono
      (Fp.inBlock_le_inBlock (by simp) (by simp)) le_rfl
  have hrt : Fp.Disj (Store.inBlock t.1 t.2 1)
      (Store.inBlock lv.1 (lv.2 + 2 * d) 2) := by
    exact (hAP.disj_getD (i := 3) (j := 1) (by simp) (by simp) (by simp)).mono
      (Fp.inBlock_le_inBlock (by simp) (by simp)) le_rfl
  have hc' := hfr.keep (Store.readsOnly_readBlock c.1 c.2 3 _) hct hc
  have hLv' := hfr.keep (Store.readsOnly_readBlock lv.1 (lv.2 + 2 * d) 2 _) hrt hLv
  exact (writes_levelTail (τ := τ) hS one two half R eps _ hAP hc' hLv' hden.2
    (by rw [hfr.len_eq]; exact hroom) (by rw [hfr.len_eq]; exact ht)).mono le_rfl
    fun _ _ h => ⟨h.1.trans hden.1, h.2⟩

end NLAlib.SpectralBisection
