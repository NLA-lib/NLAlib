/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Sparse

/-!
# Compiling coordinate-format oracle substitution

A sparse oracle implementation compiles independently of the algorithm whose oracle calls
it replaces. The matrix size is index variable zero; the remaining bound variables retain
their scopes through allocations, loops and dynamic binders.

## Main results

* `NLAlib.Computation.exists_compile_substOracle_cooImpl`: compilation and instantiation
  commute with coordinate-format oracle substitution.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι : Type}

/-- One entry of the COO kernel (`NLAlib.Computation.cooImpl`): read value $e$, multiply it by
source entry $j$, add it into destination entry $i$. -/
private def cooEntry {VB VI : Type} (p : P) (t dst src : VB) (a b m : IExp VI) :
    (ℕ × ℕ) × ℕ → Builder P ι VB VI Unit := fun ((i, j), e) => do
  Builder.stmt (.rom p ⟨t, 0⟩ (.const e))
  Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, b + .const j + m⟩)
  Builder.ins (.bin p .add ⟨dst, a + .const i + m⟩ ⟨dst, a + .const i + m⟩ ⟨t, 0⟩)

/-- The compilation of `cooImpl`, one step: its named node and the final `skip`. -/
private theorem compile_cooImpl_eq {nb ni : ℕ} (N : IExp ℕ) (pattern : List (ℕ × ℕ)) (o : ι) (p : P)
    (dst : ℕ) (dOff : IExp ℕ) (src : ℕ) (sOff cols : IExp ℕ) :
    (cooImpl N pattern o p dst dOff src sOff cols).compile nb ni =
      (do
        let x ← (do
          let a ← [Arg.idx N, .buf dst, .idx dOff, .buf src, .idx sOff, .idx cols].mapM
            (Arg.scope? nb ni)
          let b ← Stmt.compile (.alloc p 1 fun t => .seq (.loop cols fun c =>
            .seq (.loop N fun i => .seq (.instr (.lit p ⟨dst, dOff + .var i + N * .var c⟩ 0)) .skip)
              (ContT.run (pattern.zipIdx.forM
                (cooEntry (ι := ι) p t dst src dOff sOff (N * .var c))) fun _ => .skip))
            .skip) nb ni
          pure (FStmt.named "coo_apply" a b))
        let y ← some FStmt.skip
        pure (FStmt.seq x y)) := rfl

private theorem scope?_succ : ∀ {ni : ℕ} {e : IExp ℕ} {e' : IExp (Fin ni)}, e.scope? ni = some e' →
    e.scope? (ni + 1) = some (e'.subst fun v => .var v.castSucc) := by
  intro ni e
  induction e with
  | var v =>
    intro e' h
    unfold IExp.scope? at h ⊢
    by_cases hv : v < ni
    · rw [dif_pos hv] at h; cases h; rw [dif_pos (by omega)]; rfl
    · rw [dif_neg hv] at h; cases h
  | const n => intro e' h; cases h; rfl
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | mod a b iha ihb =>
    intro e' h
    simp only [IExp.scope?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    simp [IExp.scope?, iha ha, ihb hb, IExp.subst]

private theorem subst_castSucc_snoc {ni : ℕ} (e : IExp (Fin ni)) (σ : Fin ni → IExp ℕ)
    (x : IExp ℕ) :
    (e.subst fun v => .var v.castSucc).subst (Fin.snoc (α := fun _ => IExp ℕ) σ x) = e.subst σ := by
  induction e <;> simp [IExp.subst, *]

private theorem finScope?_succ {nb d : ℕ} {d' : Fin nb} (h : finScope? nb d = some d') :
    finScope? (nb + 1) d = some d'.castSucc := by
  unfold finScope? at h ⊢
  by_cases hd : d < nb
  · rw [dif_pos hd] at h; cases h; rw [dif_pos (by omega)]; rfl
  · rw [dif_neg hd] at h; cases h

private theorem scope?_zero {ni : ℕ} : (0 : IExp ℕ).scope? ni = some 0 := rfl

private theorem scope?_one {ni : ℕ} : (1 : IExp ℕ).scope? ni = some 1 := rfl

private theorem scope?_const {ni : ℕ} (n : ℕ) : (IExp.const n).scope? ni = some (.const n) := rfl

private theorem scope?_add {ni : ℕ} {a b : IExp ℕ} {a' b' : IExp (Fin ni)}
    (ha : a.scope? ni = some a') (hb : b.scope? ni = some b') :
    (a + b).scope? ni = some (a' + b') := by
  change (do let x ← a.scope? ni; let y ← b.scope? ni; pure (IExp.add x y)) = _
  rw [ha, hb]; rfl

private theorem compile_cooEntries {nb ni : ℕ} (p : P) {t dst src : ℕ} {t' d' s' : Fin nb}
    (ht : finScope? nb t = some t') (hd : finScope? nb dst = some d')
    (hs : finScope? nb src = some s') {a b m : IExp ℕ} {a' b' m' : IExp (Fin ni)}
    (ha : a.scope? ni = some a') (hb : b.scope? ni = some b') (hm : m.scope? ni = some m') :
    ∀ l : List ((ℕ × ℕ) × ℕ), ∃ c : FStmt P ι nb ni,
      Stmt.compile (ContT.run (l.forM (cooEntry (ι := ι) p t dst src a b m)) fun _ => .skip)
        nb ni = some c ∧
      ∀ ρB σ, c.toStmt ρB σ = ContT.run (l.forM (cooEntry p (ρB t') (ρB d') (ρB s') (a'.subst σ)
        (b'.subst σ) (m'.subst σ))) fun _ => .skip
  | [] => ⟨.skip, rfl, fun _ _ => rfl⟩
  | ((i, j), e) :: l => by
    obtain ⟨c, hc, hc'⟩ := compile_cooEntries p ht hd hs ha hb hm l
    refine ⟨.seq (.rom p ⟨t', 0⟩ (.const e)) (.seq (.instr (.bin p .mul ⟨t', 0⟩ ⟨t', 0⟩
      ⟨s', b' + .const j + m'⟩)) (.seq (.instr (.bin p .add ⟨d', a' + .const i + m'⟩
        ⟨d', a' + .const i + m'⟩ ⟨t', 0⟩)) c)), ?_, fun ρB σ => ?_⟩
    · change Stmt.compile (.seq (.rom p ⟨t, 0⟩ (.const e)) (.seq (.instr (.bin p .mul ⟨t, 0⟩
        ⟨t, 0⟩ ⟨src, b + .const j + m⟩)) (.seq (.instr (.bin p .add ⟨dst, a + .const i + m⟩
        ⟨dst, a + .const i + m⟩ ⟨t, 0⟩)) (ContT.run (l.forM (cooEntry (ι := ι) p t dst src a b m))
          fun _ => .skip)))) nb ni = _
      simp only [Stmt.compile, Instr.scope?, Cell.scope?, hc, ht, hd, hs, scope?_zero,
        scope?_const, scope?_add (scope?_add ha (scope?_const _)) hm,
        scope?_add (scope?_add hb (scope?_const _)) hm, Option.bind_eq_bind, Option.pure_def]
      rfl
    · simp only [FStmt.toStmt, hc']
      rfl

private theorem scope?_mul {ni : ℕ} {a b : IExp ℕ} {a' b' : IExp (Fin ni)}
    (ha : a.scope? ni = some a') (hb : b.scope? ni = some b') :
    (a * b).scope? ni = some (a' * b') := by
  change (do let x ← a.scope? ni; let y ← b.scope? ni; pure (IExp.mul x y)) = _
  rw [ha, hb]; rfl

private theorem scope?_var {ni v : ℕ} (h : v < ni) :
    (IExp.var v).scope? ni = some (.var ⟨v, h⟩) := by
  simp [IExp.scope?, h]

private theorem finScope?_eq {nb v : ℕ} (h : v < nb) : finScope? nb v = some ⟨v, h⟩ := by
  simp [finScope?, h]

private theorem scope?_var_last {n : ℕ} :
    (IExp.var n).scope? (n + 1) = some (.var (Fin.last n)) := by
  simp [IExp.scope?, Fin.last]

private theorem finScope?_last {n : ℕ} : finScope? (n + 1) n = some (Fin.last n) := by
  simp [finScope?, Fin.last]

private theorem compile_cooImpl {nb ni : ℕ} (hni : 0 < ni) (pattern : List (ℕ × ℕ)) (o : ι) (p : P)
    {d s : ℕ} {d' s' : Fin nb} (hd : finScope? nb d = some d') (hs : finScope? nb s = some s')
    {dOff sOff cols : IExp ℕ} {dOff' sOff' cols' : IExp (Fin ni)}
    (h₁ : dOff.scope? ni = some dOff') (h₂ : sOff.scope? ni = some sOff')
    (h₃ : cols.scope? ni = some cols') :
    ∃ c : FStmt P ι nb ni,
      (cooImpl (.var 0) pattern o p d dOff s sOff cols).compile nb ni = some c ∧
      ∀ ρB σ M, σ ⟨0, hni⟩ = .const M → c.toStmt ρB σ =
        cooImpl (.const M) pattern o p (ρB d') (dOff'.subst σ) (ρB s') (sOff'.subst σ)
          (cols'.subst σ) := by
  have v0 : (IExp.var 0).scope? ni = some (.var ⟨0, hni⟩) := scope?_var hni
  have v1 := scope?_succ v0
  have v2 := scope?_succ v1
  have vn := scope?_succ (scope?_var_last (n := ni))
  obtain ⟨cE, hcE, hcE'⟩ := compile_cooEntries (ι := ι) p finScope?_last
    (finScope?_succ hd) (finScope?_succ hs) (scope?_succ h₁) (scope?_succ h₂)
    (scope?_mul v1 scope?_var_last) pattern.zipIdx
  rw [compile_cooImpl_eq]
  simp only [Stmt.compile, List.mapM_cons, List.mapM_nil, Arg.scope?, Instr.scope?, Cell.scope?,
    hcE, hd, hs, h₁, h₂, h₃, finScope?_succ hd, scope?_one, v0, v1,
    scope?_add (scope?_add (scope?_succ (scope?_succ h₁)) scope?_var_last) (scope?_mul v2 vn),
    Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.some.injEq, exists_eq_left']
  intro ρB σ M hM
  simp only [FStmt.toStmt, hcE', List.map_cons, List.map_nil, Arg.subst, Instr.subst, Cell.subst,
    IExp.subst, subst_castSucc_snoc, Fin.snoc_castSucc, Fin.snoc_last, hM]
  rfl

/-- The kernel-call case of the sparse compile lemma: a kernel call becomes `skip`. -/
private theorem compile_substOracle_kcall (pattern : List (ℕ × ℕ)) {o : ι} {p : P}
    {dims : List (IExp ℕ)} {ins outs : List (ℕ × IExp ℕ)} {nb ni : ℕ} (hni : 0 < ni)
    {c : FStmt P ι nb ni} (h : (Stmt.kcall o p dims ins outs).compile nb ni = some c) :
    ∃ c' : FStmt P ι nb ni,
      ((Stmt.kcall o p dims ins outs).subst .instr (cooImpl (.var 0) pattern)
        fun _ _ _ _ _ => .skip).compile nb ni = some c' ∧
      ∀ ρB σ M, σ ⟨0, hni⟩ = .const M →
        c'.toStmt ρB σ = (c.toStmt ρB σ).subst .instr (cooImpl (.const M) pattern)
          fun _ _ _ _ _ => .skip := by
  simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨dims', -, ins', -, outs', -, rfl⟩ := h
  exact ⟨.skip, rfl, fun _ _ _ _ => rfl⟩

/-- The index-binder case of the sparse compile lemma: the binder is kept, its body substituted. -/
private theorem compile_substOracle_bindIdx (pattern : List (ℕ × ℕ)) {p : P} {x : Cell ℕ ℕ}
    {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    (ih : ∀ v {nb ni : ℕ} (hni : 0 < ni) (c : FStmt P ι nb ni), (body v).compile nb ni = some c →
      ∃ c' : FStmt P ι nb ni,
        ((body v).subst .instr (cooImpl (.var 0) pattern) fun _ _ _ _ _ => .skip).compile nb ni =
          some c' ∧
        ∀ ρB σ M, σ ⟨0, hni⟩ = .const M →
          c'.toStmt ρB σ = (c.toStmt ρB σ).subst .instr (cooImpl (.const M) pattern)
            fun _ _ _ _ _ => .skip)
    {nb ni : ℕ} (hni : 0 < ni) {c : FStmt P ι nb ni}
    (h : (Stmt.bindIdx p x bound body).compile nb ni = some c) :
    ∃ c' : FStmt P ι nb ni,
      ((Stmt.bindIdx p x bound body).subst .instr (cooImpl (.var 0) pattern)
        fun _ _ _ _ _ => .skip).compile nb ni = some c' ∧
      ∀ ρB σ M, σ ⟨0, hni⟩ = .const M →
        c'.toStmt ρB σ = (c.toStmt ρB σ).subst .instr (cooImpl (.const M) pattern)
          fun _ _ _ _ _ => .skip := by
  simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨x', hx, n', hn, b', hb, rfl⟩ := h
  obtain ⟨cb, hcb, hcb'⟩ := ih ni (Nat.succ_pos ni) b' hb
  refine ⟨.bindIdx p x' n' cb, ?_, fun ρB σ M hM => ?_⟩
  · simp [Stmt.subst, Stmt.compile, hx, hn, hcb]
  · simp [Stmt.subst, FStmt.toStmt, hcb' _ _ M ((Fin.snoc_castSucc (i := ⟨0, hni⟩) ..).trans hM)]

/-- A compilable statement remains compilable after replacing its oracle calls by the
coordinate-format implementation, and instantiation commutes with that substitution when
index variable zero is the matrix size. The index scope must contain that variable.
No printed source. -/
theorem exists_compile_substOracle_cooImpl (pattern : List (ℕ × ℕ)) (s : Stmt P ι ℕ ℕ) :
    ∀ {nb ni : ℕ} (hni : 0 < ni) (c : FStmt P ι nb ni), s.compile nb ni = some c →
      ∃ c' : FStmt P ι nb ni,
        (s.substOracle (cooImpl (.var 0) pattern)).compile nb ni = some c' ∧
        ∀ ρB σ M, σ ⟨0, hni⟩ = .const M →
          c'.toStmt ρB σ = (c.toStmt ρB σ).substOracle (cooImpl (.const M) pattern) := by
  simp only [Stmt.substOracle]
  induction s with
  | skip => intro nb ni hni c h; cases h; exact ⟨.skip, rfl, fun _ _ _ _ => rfl⟩
  | seq s t ihs iht =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s', hs, t', ht, rfl⟩ := h
    obtain ⟨cs, hcs, hcs'⟩ := ihs hni s' hs
    obtain ⟨ct, hct, hct'⟩ := iht hni t' ht
    refine ⟨.seq cs ct, ?_, fun ρB σ M hM => ?_⟩
    · simp [Stmt.subst, Stmt.compile, hcs, hct]
    · simp [Stmt.subst, FStmt.toStmt, hcs' ρB σ M hM, hct' ρB σ M hM]
  | instr i =>
    intro nb ni hni c h
    exact ⟨c, h, fun _ _ _ _ => by
      simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨i', -, rfl⟩ := h; rfl⟩
  | apply o p d dOff s sOff cols =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨d', hd, dOff', h₁, s', hs, sOff', h₂, cols', h₃, rfl⟩ := h
    exact compile_cooImpl hni pattern o p hd hs h₁ h₂ h₃
  | rom p d i =>
    intro nb ni hni c h
    exact ⟨c, h, fun _ _ _ _ => by
      simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨d', -, i', -, rfl⟩ := h
      rfl⟩
  | alloc p len body ih =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨len', hlen, b', hb, rfl⟩ := h
    obtain ⟨cb, hcb, hcb'⟩ := ih nb hni b' hb
    refine ⟨.alloc p len' cb, ?_, fun ρB σ M hM => ?_⟩
    · simp [Stmt.subst, Stmt.compile, hlen, hcb]
    · simp [Stmt.subst, FStmt.toStmt, hcb' _ σ M hM]
  | loop n body ih =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨n', hn, b', hb, rfl⟩ := h
    obtain ⟨cb, hcb, hcb'⟩ := ih ni (Nat.succ_pos ni) b' hb
    refine ⟨.loop n' cb, ?_, fun ρB σ M hM => ?_⟩
    · simp [Stmt.subst, Stmt.compile, hn, hcb]
    · simp [Stmt.subst, FStmt.toStmt, hcb' _ _ M ((Fin.snoc_castSucc (i := ⟨0, hni⟩) ..).trans hM)]
  | whileFuel fuel p cmp x y body ih =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨f', hf, x', hx, y', hy, b', hb, rfl⟩ := h
    obtain ⟨cb, hcb, hcb'⟩ := ih hni b' hb
    refine ⟨.whileFuel f' p cmp x' y' cb, ?_, fun ρB σ M hM => ?_⟩
    · simp [Stmt.subst, Stmt.compile, hf, hx, hy, hcb]
    · simp [Stmt.subst, FStmt.toStmt, hcb' ρB σ M hM]
  | ite p cmp x y t e iht ihe =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x', hx, y', hy, t', ht, e', he, rfl⟩ := h
    obtain ⟨ct, hct, hct'⟩ := iht hni t' ht
    obtain ⟨ce, hce, hce'⟩ := ihe hni e' he
    refine ⟨.ite p cmp x' y' ct ce, ?_, fun ρB σ M hM => ?_⟩
    · simp [Stmt.subst, Stmt.compile, hx, hy, hct, hce]
    · simp [Stmt.subst, FStmt.toStmt, hct' ρB σ M hM, hce' ρB σ M hM]
  | named name args body ih =>
    intro nb ni hni c h
    simp only [Stmt.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨args', ha, b', hb, rfl⟩ := h
    obtain ⟨cb, hcb, hcb'⟩ := ih hni b' hb
    refine ⟨FStmt.named name args' cb, ?_, fun ρB σ M hM => ?_⟩
    · simp [Stmt.subst, Stmt.compile, ha, hcb]
    · simp [Stmt.subst, FStmt.toStmt, hcb' ρB σ M hM]
  | kcall o p dims ins outs => exact fun hni c h => compile_substOracle_kcall pattern hni h
  | bindIdx p x bound body ih => exact fun hni c h => compile_substOracle_bindIdx pattern ih hni h

end NLAlib.Computation
