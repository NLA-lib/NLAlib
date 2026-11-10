/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Transfer

/-!
# Signatures made of groups, and profiles

**Groups.** The operations of the library come in small groups (scalar arithmetic, level-1
vector operations, …). A signature `Op` contains a group `G` through `NLAlib.Ops.Has G Op`: an
injection with a partial inverse. An algorithm, an implementation or a table is written for any
`Op` with the groups it uses; `NLAlib.Ops.Apart G H Op` says two groups do not overlap in `Op`.

**Profiles.** A profile `NLAlib.Ops.Profile Op Lo Tst` is a table with the cost of each
implementation and the workspaces. Its certificate `NLAlib.Ops.Profile.Certifies Base Ck` says:
over every lower interpretation meeting `Base` the linked interpretation meets `Ck`, and a run
within a budget under the linked interpretation is a run of the linked program within the
pushed-forward budget. So a theorem about an algorithm for every interpretation meeting `Ck`
gives the theorem about the linked program in one application
(`NLAlib.Ops.Profile.Certifies.runs`).

Profiles stack (`NLAlib.Ops.Profile.over`), and a profile of a signature over itself is iterated
(`NLAlib.Ops.Profile.iter`): this is how an operation implemented by calls of itself at smaller
dimensions is linked, with the number of iterations a bound on the depth.

## Main results

* `NLAlib.Ops.Profile.Certifies.of_accounts`: a certificate from the contracts of the induced
  interpretation and the accounting certificate of the table.
* `NLAlib.Ops.Profile.Certifies.over`: certificates compose along a tower.
* `NLAlib.Ops.Profile.Certifies.iter`: **recursion**; correctness and cost transfer for the
  `k`-fold iterate of a profile, from one step.
* `NLAlib.Ops.Profile.Certifies.runs`: the corollary for any algorithm.
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

namespace Profile

/-- **The certificate of a profile.** -/
structure Certifies (P : Profile Op Lo Tst) (Base : Interp Lo Tst K → Prop)
    (Ck : Interp Op Tst K → Prop) : Prop where
  /-- Over a lower interpretation meeting `Base`, the linked interpretation meets `Ck`. -/
  meets : ∀ I, Base I → Ck (I.link P.table)
  /-- A run within a budget under the linked interpretation is a run of the linked program
  within the pushed-forward budget. -/
  transfer : ∀ (I : Interp Lo Tst K) (τ : ℕ → K) (s : Stmt Op Tst) (ρ : Env) (m : Mem K)
    (B : Count Op Tst) (M : ℕ) (Q : Mem K → Prop), Runs (I.link P.table) P.ws τ s ρ m B M Q →
      Runs I P.wsLo τ (s.link P.table) ρ m (Count.push P.cost B) M Q

/-- A certificate from the contracts of the induced interpretation and the accounting certificate
of the table. -/
theorem Certifies.of_accounts {P : Profile Op Lo Tst} {Base : Interp Lo Tst K → Prop}
    {Ck : Interp Op Tst K → Prop} (hm : ∀ I, Base I → Ck (I.link P.table))
    (hacc : ∀ I : Interp Lo Tst K, P.table.Accounts I P.wsLo P.cost P.ws) : P.Certifies Base Ck :=
  ⟨hm, fun I _ _ _ _ _ _ _ h => h.link (hacc I)⟩

/-- **The corollary for any algorithm and any certified profile**: a theorem proved for every
interpretation meeting `Ck` holds for the linked program over every interpretation meeting
`Base`, with the counts pushed forward and the same workspace. -/
theorem Certifies.runs {P : Profile Op Lo Tst} {Base : Interp Lo Tst K → Prop}
    {Ck : Interp Op Tst K → Prop} (h : P.Certifies Base Ck) {τ : ℕ → K} {s : Stmt Op Tst}
    {ρ : Env} {m : Mem K} {B : Count Op Tst} {M : ℕ} {Q : Mem K → Prop}
    (hT : ∀ J, Ck J → Runs J P.ws τ s ρ m B M Q) {I : Interp Lo Tst K} (hI : Base I) :
    Runs I P.wsLo τ (s.link P.table) ρ m (Count.push P.cost B) M Q :=
  h.transfer I τ s ρ m B M Q (hT _ (h.meets I hI))

/-- **A profile on a profile**: the trees of `P` linked through `Q`. -/
noncomputable def over (P : Profile Op Mid Tst) (Q : Profile Mid Lo Tst) : Profile Op Lo Tst where
  table := P.table.comp Q.table
  cost o d := Count.push Q.cost (P.cost o d)
  ws := P.ws
  wsLo := Q.wsLo

/-- **Certificates compose along a tower.** -/
theorem Certifies.over {P : Profile Op Mid Tst} {Q : Profile Mid Lo Tst}
    {C₀ : Interp Lo Tst K → Prop} {C₁ : Interp Mid Tst K → Prop} {C₂ : Interp Op Tst K → Prop}
    (hP : P.Certifies C₁ C₂) (hQ : Q.Certifies C₀ C₁) (hws : P.wsLo = Q.ws) :
    (P.over Q).Certifies C₀ C₂ where
  meets I hI := by
    have := hP.meets _ (hQ.meets I hI)
    rwa [Interp.link_comp] at this
  transfer I τ s ρ m B M Post h := by
    have h1 : Runs ((I.link Q.table).link P.table) P.ws τ s ρ m B M Post := by
      rw [Interp.link_comp]
      exact h
    have h2 := hP.transfer _ τ s ρ m B M Post h1
    rw [hws] at h2
    have h3 := hQ.transfer I τ _ ρ m _ M Post h2
    rw [Stmt.link_comp, Count.push_comp] at h3
    exact h3

/-- The profile that keeps every operation. -/
noncomputable def id (W : Op → List ℕ → ℕ) : Profile Op Op Tst where
  table := Table.id
  cost := Count.one
  ws := W
  wsLo := W

theorem certifies_id (W : Op → List ℕ → ℕ) (C : Interp Op Tst K → Prop) :
    (Profile.id (Tst := Tst) W).Certifies C C where
  meets I hI := hI
  transfer I τ s ρ m B M Q h := by
    simpa [Profile.id] using h

/-- **The `k`-fold iterate of a profile of a signature over itself.** -/
noncomputable def iter (P : Profile Op Op Tst) : ℕ → Profile Op Op Tst
  | 0 => Profile.id P.ws
  | k + 1 => P.over (P.iter k)

@[simp] theorem iter_ws (P : Profile Op Op Tst) (k : ℕ) : (P.iter k).ws = P.ws := by
  cases k <;> rfl

theorem iter_wsLo (P : Profile Op Op Tst) (k : ℕ) :
    (P.iter k).wsLo = P.ws := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

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
theorem Certifies.iter {P : Profile Op Op Tst} {C : ℕ → Interp Op Tst K → Prop}
    (h : ∀ k, P.Certifies (C k) (C (k + 1))) (hws : P.wsLo = P.ws) (k : ℕ) :
    (P.iter k).Certifies (C 0) (C k) := by
  induction k with
  | zero => exact certifies_id _ _
  | succ k ih => exact (h k).over ih (by rw [hws, iter_ws])

end Profile

end NLAlib.Ops
