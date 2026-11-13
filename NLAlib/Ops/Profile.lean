/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Transfer
public import NLAlib.Ops.Tape

/-!
# Signatures made of groups, and profiles

**Groups.** The operations of the library come in small groups (scalar arithmetic, level-1
vector operations, …). A signature `Op` contains a group `G` through `NLAlib.Ops.Has G Op`: an
injection with a partial inverse. An algorithm, an implementation or a table is written for any
`Op` with the groups it uses; `NLAlib.Ops.Apart G H Op` says two groups do not overlap in `Op`.

**Profiles.** A profile `NLAlib.Ops.Profile Op Lo Tst` is a table with the cost of each
implementation and the workspaces. Its certificate `NLAlib.Ops.Profile.Refines Base Ck` says:
over every lower interpretation meeting `Base` the linked interpretation meets `Ck`, and a run
within a budget under the linked interpretation is a run of the linked program within the
pushed-forward budget. So a theorem about an algorithm for every interpretation meeting `Ck`
gives the theorem about the linked program in one application
(`NLAlib.Ops.Profile.Refines.runs`).

Profiles stack (`NLAlib.Ops.Profile.over`), and a profile of a signature over itself is iterated
(`NLAlib.Ops.Profile.iter`): this is how an operation implemented by calls of itself at smaller
dimensions is linked, with the number of iterations a bound on the depth.

## Main results

* `NLAlib.Ops.Profile.Refines.of_accounts`: a certificate from the contracts of the induced
  interpretation and the accounting certificate of the table.
* `NLAlib.Ops.Profile.Refines.over`: certificates compose along a tower.
* `NLAlib.Ops.Profile.Refines.iter`: **recursion**; correctness and cost transfer for the
  `k`-fold iterate of a profile, from one step.
* `NLAlib.Ops.Profile.Refines.runs`: the corollary for any algorithm.
-/

@[expose] public section

namespace NLAlib.Ops

/-- **The signature `Op` contains the group of operations `G`.** -/
class Has (G Op : Type) where
  /-- The operation of `Op` named by an operation of the group. -/
  inj : G → Op
  /-- The operation of the group that names an operation of `Op`, if there is one. -/
  proj : Op → Option G
  /-- `proj` inverts `inj`. -/
  proj_inj : ∀ g, proj (inj g) = some g
  /-- `inj` inverts `proj`. -/
  inj_of_proj : ∀ o g, proj o = some g → inj g = o

attribute [simp] Has.proj_inj

/-- **The groups `G` and `H` do not overlap in `Op`.** -/
class Apart (G H Op : Type) [Has G Op] [Has H Op] : Prop where
  /-- An operation of `H` is not one of `G`. -/
  proj_inj : ∀ h : H, Has.proj (G := G) (Has.inj h : Op) = none

attribute [simp] Apart.proj_inj

instance (G : Type) : Has G G := ⟨id, some, fun _ => rfl, fun _ _ h => (Option.some.inj h).symm⟩

instance (G H : Type) : Has G (G ⊕ H) :=
  ⟨.inl, fun o => o.elim some fun _ => none, fun _ => rfl, fun o g h => by
    cases o with
    | inl a => exact congrArg Sum.inl (Option.some.inj h).symm
    | inr b => cases h⟩

instance (G H : Type) : Has H (G ⊕ H) :=
  ⟨.inr, fun o => o.elim (fun _ => none) some, fun _ => rfl, fun o g h => by
    cases o with
    | inl a => cases h
    | inr b => exact congrArg Sum.inr (Option.some.inj h).symm⟩

instance (G H : Type) : Apart G H (G ⊕ H) := ⟨fun _ => rfl⟩

instance (G H : Type) : Apart H G (G ⊕ H) := ⟨fun _ => rfl⟩

theorem Has.inj_injective (G Op : Type) [Has G Op] : Function.Injective (Has.inj : G → Op) :=
  fun a b h => by
    have := Has.proj_inj (Op := Op) a
    rw [h, Has.proj_inj] at this
    exact (Option.some.inj this).symm

/-- Embed an existing operation group through the left branch of a larger sum signature.
The projection/injection laws are preserved by construction. -/
@[reducible] def Has.sumLeft (G A B : Type) (h : Has G A) : Has G (A ⊕ B) where
  inj g := .inl (h.inj g)
  proj o := match o with | .inl a => h.proj a | .inr _ => none
  proj_inj g := h.proj_inj g
  inj_of_proj o g ho := by
    cases o with
    | inl a => exact congrArg Sum.inl (h.inj_of_proj a g ho)
    | inr _ => cases ho

/-- Embed an existing operation group through the right branch of a larger sum signature.
This is explicit rather than a recursive instance search over arbitrary group embeddings. -/
@[reducible] def Has.sumRight (G A B : Type) (h : Has G B) : Has G (A ⊕ B) where
  inj g := .inr (h.inj g)
  proj o := match o with | .inl _ => none | .inr b => h.proj b
  proj_inj g := h.proj_inj g
  inj_of_proj o g ho := by
    cases o with
    | inl _ => cases ho
    | inr b => exact congrArg Sum.inr (h.inj_of_proj b g ho)

variable {Op Mid Lo Tst K : Type}

/-- **A profile**: a table from the operations `Op` to the lower operations `Lo`, with the cost
of each operation in lower operations and the workspaces of both levels. -/
structure Profile (Op Lo Tst : Type) where
  /-- The table. -/
  table : Table Op Lo Tst
  /-- The cost of one call, in lower operations. -/
  cost : Op → List ℕ → Count Lo Tst
  /-- The workspace of each operation. -/
  ws : Op → List ℕ → ℕ
  /-- The workspace of each lower operation. -/
  wsLo : Lo → List ℕ → ℕ
  /-- The tape window of each operation: the number of positions a call may read. -/
  win : Op → List ℕ → ℕ := fun _ _ => 0
  /-- The tape window of each lower operation. -/
  winLo : Lo → List ℕ → ℕ := fun _ _ => 0

namespace Profile

/-- **The certificate of a profile.** -/
structure Refines (P : Profile Op Lo Tst) (Base : Interp Lo Tst K → Prop)
    (Ck : Interp Op Tst K → Prop) : Prop where
  /-- Over a lower interpretation meeting `Base`, the linked interpretation meets `Ck`. -/
  meets : ∀ I, Base I → Ck (I.link P.table)
  /-- A run within a budget under the linked interpretation is a run of the linked program
  within the pushed-forward budget. -/
  transfer : ∀ (I : Interp Lo Tst K) (τ : Tape K) (s : Stmt Op Tst) (ρ : Env) (m : Mem K)
    (B : Count Op Tst) (M : ℕ) (Q : Mem K → Prop), ConditionalRuns (I.link P.table) P.ws τ s ρ m B
      M Q →
      ConditionalRuns I P.wsLo τ (s.link P.table) ρ m (Count.push P.cost B) M Q
  /-- Over lower operations that read the tape only in their windows, the linked operations read
  it only in theirs: the draws of an implementation are those the law of the tape assigns to it. -/
  tapeLocal : ∀ I : Interp Lo Tst K, Base I → (∀ o, I.TapeLocal o (P.winLo o)) →
    ∀ o, (I.link P.table).TapeLocal o (P.win o)

/-- The tape clause of a profile that does not draw: over tape-independent operations every linked
operation is tape-independent, whatever its implementation. -/
theorem tapeLocal_noDraw {P : Profile Op Lo Tst} (hw : P.win = fun _ _ => 0)
    (hl : P.winLo = fun _ _ => 0) (I : Interp Lo Tst K)
    (hI : ∀ o, I.TapeLocal o (P.winLo o)) (o : Op) : (I.link P.table).TapeLocal o (P.win o) := by
  rw [hw]
  exact Interp.TapeLocal.link_zero (fun o => by simpa [hl] using hI o) P.table o

/-- A certificate from the contracts of the induced interpretation and the accounting certificate
of the table. -/
theorem Refines.of_accounts {P : Profile Op Lo Tst} {Base : Interp Lo Tst K → Prop}
    {Ck : Interp Op Tst K → Prop} (hm : ∀ I, Base I → Ck (I.link P.table))
    (hacc : ∀ I : Interp Lo Tst K, P.table.Accounts I P.wsLo P.cost P.ws)
    (htl : ∀ I : Interp Lo Tst K, Base I → (∀ o, I.TapeLocal o (P.winLo o)) →
      ∀ o, (I.link P.table).TapeLocal o (P.win o)) : P.Refines Base Ck :=
  ⟨hm, fun I _ _ _ _ _ _ _ h => h.link (hacc I), htl⟩

/-- A certificate serves a stronger base and weaker contracts. -/
theorem Refines.mono {P : Profile Op Lo Tst} {Base Base' : Interp Lo Tst K → Prop}
    {Ck Ck' : Interp Op Tst K → Prop} (h : P.Refines Base Ck) (hB : ∀ I, Base' I → Base I)
    (hC : ∀ J, Ck J → Ck' J) : P.Refines Base' Ck' :=
  ⟨fun I hI => hC _ (h.meets I (hB I hI)), h.transfer, fun I hI => h.tapeLocal I (hB I hI)⟩

/-- **The corollary for any algorithm and any certified profile**: a theorem proved for every
interpretation meeting `Ck` holds for the linked program over every interpretation meeting
`Base`, with the counts pushed forward and the same workspace. -/
theorem Refines.runs {P : Profile Op Lo Tst} {Base : Interp Lo Tst K → Prop}
    {Ck : Interp Op Tst K → Prop} (h : P.Refines Base Ck) {τ : Tape K} {s : Stmt Op Tst}
    {ρ : Env} {m : Mem K} {B : Count Op Tst} {M : ℕ} {Q : Mem K → Prop}
    (hT : ∀ J, Ck J → ConditionalRuns J P.ws τ s ρ m B M Q) {I : Interp Lo Tst K} (hI : Base I) :
    ConditionalRuns I P.wsLo τ (s.link P.table) ρ m (Count.push P.cost B) M Q :=
  h.transfer I τ s ρ m B M Q (hT _ (h.meets I hI))

/-- **A profile on a profile**: the trees of `P` linked through `Q`. -/
noncomputable def over (P : Profile Op Mid Tst) (Q : Profile Mid Lo Tst) : Profile Op Lo Tst where
  table := P.table.comp Q.table
  cost o d := Count.push Q.cost (P.cost o d)
  ws := P.ws
  wsLo := Q.wsLo
  win := P.win
  winLo := Q.winLo

/-- **Certificates compose along a tower.** -/
theorem Refines.over {P : Profile Op Mid Tst} {Q : Profile Mid Lo Tst}
    {C₀ : Interp Lo Tst K → Prop} {C₁ : Interp Mid Tst K → Prop} {C₂ : Interp Op Tst K → Prop}
    (hP : P.Refines C₁ C₂) (hQ : Q.Refines C₀ C₁) (hws : P.wsLo = Q.ws)
    (hwin : P.winLo = Q.win) : (P.over Q).Refines C₀ C₂ where
  tapeLocal I hI hloc o := by
    have := hP.tapeLocal _ (hQ.meets I hI) (hwin ▸ hQ.tapeLocal I hI hloc) o
    rwa [Interp.link_comp] at this
  meets I hI := by
    have := hP.meets _ (hQ.meets I hI)
    rwa [Interp.link_comp] at this
  transfer I τ s ρ m B M Post h := by
    have h1 : ConditionalRuns ((I.link Q.table).link P.table) P.ws τ s ρ m B M Post := by
      rw [Interp.link_comp]
      exact h
    have h2 := hP.transfer _ τ s ρ m B M Post h1
    rw [hws] at h2
    have h3 := hQ.transfer I τ _ ρ m _ M Post h2
    rw [Stmt.link_comp, Count.push_comp] at h3
    exact h3

/-- The profile that keeps every operation. -/
noncomputable def id (W : Op → List ℕ → ℕ) (V : Op → List ℕ → ℕ := fun _ _ => 0) :
    Profile Op Op Tst where
  table := Table.id
  cost := Count.one
  ws := W
  wsLo := W
  win := V
  winLo := V

theorem certifies_id (W V : Op → List ℕ → ℕ) (C : Interp Op Tst K → Prop) :
    (Profile.id (Tst := Tst) W V).Refines C C where
  meets I hI := hI
  tapeLocal I _ hloc o := Interp.TapeLocal.link_kept rfl (hloc o)
  transfer I τ s ρ m B M Q h := by
    simpa [Profile.id] using h

/-- **The `k`-fold iterate of a profile of a signature over itself.** -/
noncomputable def iter (P : Profile Op Op Tst) : ℕ → Profile Op Op Tst
  | 0 => Profile.id P.ws P.win
  | k + 1 => P.over (P.iter k)

@[simp] theorem iter_ws (P : Profile Op Op Tst) (k : ℕ) : (P.iter k).ws = P.ws := by
  cases k <;> rfl

theorem iter_wsLo (P : Profile Op Op Tst) (k : ℕ) :
    (P.iter k).wsLo = P.ws := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

@[simp] theorem iter_win (P : Profile Op Op Tst) (k : ℕ) : (P.iter k).win = P.win := by
  cases k <;> rfl

@[simp] theorem iter_table (P : Profile Op Op Tst) (k : ℕ) :
    (P.iter k).table = P.table.iter k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iter, over, Table.iter, ih]

theorem iter_cost_zero (P : Profile Op Op Tst) : (P.iter 0).cost = Count.one := rfl

theorem iter_cost_succ (P : Profile Op Op Tst) (k : ℕ) (o : Op) (d : List ℕ) :
    (P.iter (k + 1)).cost o d = Count.push (P.iter k).cost (P.cost o d) := rfl

/-- **Recursion.** If one application of the profile takes the contracts of depth `k` to those of
depth `k + 1`, its `k`-fold iterate takes the contracts of depth `0` to those of depth `k`, with
the counts pushed forward `k` times. -/
theorem Refines.iter {P : Profile Op Op Tst} {C : ℕ → Interp Op Tst K → Prop}
    (h : ∀ k, P.Refines (C k) (C (k + 1))) (hws : P.wsLo = P.ws) (hwin : P.winLo = P.win)
    (k : ℕ) :
    (P.iter k).Refines (C 0) (C k) := by
  induction k with
  | zero => exact certifies_id _ _ _
  | succ k ih => exact (h k).over ih (by rw [hws, iter_ws]) (by rw [hwin, iter_win])

end Profile

end NLAlib.Ops
