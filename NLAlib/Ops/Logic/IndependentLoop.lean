/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop

/-!
# Independent output regions of a counted loop

Each iteration initializes its own region. Pairwise disjointness and local read footprints
preserve all completed mathematical outputs, including variable-size and empty regions.

## Main results

* `NLAlib.Ops.writes_loop_disjoint`: collect one stored output predicate per iteration.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The regions written by the completed rounds of a loop. -/
def Fp.loopPrefix (region : ℕ → Fp) (i : ℕ) : Fp :=
  fun b x => ∃ j < i, region j b x

/-- Componentwise inclusion of completed-round regions includes their prefix unions. -/
theorem Fp.loopPrefix_mono {region region' : ℕ → Fp} {i : ℕ}
    (h : ∀ j < i, region j ≤ region' j) : Fp.loopPrefix region i ≤ Fp.loopPrefix region' i :=
  fun b x ⟨j, hj, hx⟩ => ⟨j, hj, h j hj b x hx⟩

/-- Independent output initialization with a precise completed-round frame. This permits a
round to read its own original output region, as when an already-computed leaf is retained. -/
theorem writes_loop_disjoint_prefix {K Op Tst : Type} {md : Mode} {I : Interp Op Tst K}
    {τ : Tape K} {ρ : Env} {m : Mem K} {n : IExp} {N : ℕ} {body : Stmt Op Tst}
    {F : Fp} (region : ℕ → Fp) (result : ℕ → Store K → Prop)
    (hn : n.eval ρ.idx = some N) (hsub : ∀ i < N, region i ≤ F)
    (hdisj : ∀ i < N, ∀ j < N, i ≠ j → Fp.Disj (region i) (region j))
    (hread : ∀ i < N, Store.ReadsOnly (region i) (result i))
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (Fp.loopPrefix region i) m'.store →
      Writes md I τ body (ρ.pushIdx i) (region i)
        (fun m'' => m''.pos = m'.pos ∧ result i m''.store) m') :
    Writes md I τ (.loop n body) ρ F
      (fun m' => m'.pos = m.pos ∧ ∀ i < N, result i m'.store) m := by
  refine (writes_loop hn (Fp.loopPrefix region) (fun i _ _ _ h => ?_)
    (fun i m' => m'.pos = m.pos ∧ ∀ j < i, result j m'.store)
    ⟨rfl, by simp⟩ ?_).mono ?_ (fun _ _ h => h)
  · rcases h with ⟨j, hj, hjx⟩
    exact ⟨j, by omega, hjx⟩
  · intro i hi m' hfr ⟨hp, hr⟩
    refine (hstep i hi m' hfr).mono (fun b x hx => ⟨i, by omega, hx⟩) ?_
    intro m'' hfr' ⟨hp', hnew⟩
    refine ⟨hp'.trans hp, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hfr'.keep (hread j (by omega))
        (hdisj i hi j (by omega) (by omega)) (hr j hj)
    · exact hnew
  · rintro b x ⟨i, hi, hx⟩
    exact hsub i hi b x hx

/-- A loop initializes independent regions. The caller supplies each local mathematical
output and its read footprint; the shared rule retains all previously initialized regions. -/
theorem writes_loop_disjoint {K Op Tst : Type} {md : Mode} {I : Interp Op Tst K}
    {τ : Tape K} {ρ : Env} {m : Mem K} {n : IExp} {N : ℕ} {body : Stmt Op Tst}
    {F : Fp} (region : ℕ → Fp) (result : ℕ → Store K → Prop)
    (hn : n.eval ρ.idx = some N) (hsub : ∀ i < N, region i ≤ F)
    (hdisj : ∀ i < N, ∀ j < N, i ≠ j → Fp.Disj (region i) (region j))
    (hread : ∀ i < N, Store.ReadsOnly (region i) (result i))
    (hstep : ∀ i < N, ∀ m', m.store.EqOff F m'.store →
      Writes md I τ body (ρ.pushIdx i) (region i)
        (fun m'' => m''.pos = m'.pos ∧ result i m''.store) m') :
    Writes md I τ (.loop n body) ρ F
      (fun m' => m'.pos = m.pos ∧ ∀ i < N, result i m'.store) m := by
  refine writes_loop hn (fun _ => F) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ ∀ j < i, result j m'.store)
    ⟨rfl, by simp⟩ fun i hi m' hfr ⟨hp, hr⟩ => ?_
  refine (hstep i hi m' hfr).mono (hsub i hi) ?_
  intro m'' hfr' ⟨hp', hnew⟩
  refine ⟨hp'.trans hp, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact hfr'.keep (hread j (by omega)) (hdisj i hi j (by omega) (by omega)) (hr j hj)
  · exact hnew

/-- Independent output regions may share reusable scratch. The scratch can change every
iteration but is disjoint from every retained result region. The body receives the actual
prefix frame plus scratch, so future source values can be retained through this same geometry. -/
theorem writes_loop_disjoint_prefix_scratch {K Op Tst : Type} {md : Mode}
    {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}
    {n : IExp} {N : ℕ} {body : Stmt Op Tst} {F scratch : Fp}
    (region : ℕ → Fp) (result : ℕ → Store K → Prop)
    (hn : n.eval ρ.idx = some N) (hsub : ∀ i < N, region i ≤ F)
    (hscratch : scratch ≤ F)
    (hdisj : ∀ i < N, ∀ j < N, i ≠ j → Fp.Disj (region i) (region j))
    (hprotect : ∀ i < N, Fp.Disj scratch (region i))
    (hread : ∀ i < N, Store.ReadsOnly (region i) (result i))
    (hstep : ∀ i < N, ∀ m', m.store.EqOff (Fp.loopPrefix region i ⊔ scratch) m'.store →
      Writes md I τ body (ρ.pushIdx i) (region i ⊔ scratch)
        (fun m'' => m''.pos = m'.pos ∧ result i m''.store) m') :
    Writes md I τ (.loop n body) ρ F
      (fun m' => m'.pos = m.pos ∧ ∀ i < N, result i m'.store) m := by
  refine (writes_loop hn (fun i => Fp.loopPrefix region i ⊔ scratch) ?_
    (fun i m' => m'.pos = m.pos ∧ ∀ j < i, result j m'.store)
    ⟨rfl, by simp⟩ ?_).mono ?_ (fun _ _ h => h)
  · intro i hi
    exact sup_le (fun b x ⟨j, hj, hx⟩ => Or.inl ⟨j, by omega, hx⟩) le_sup_right
  · intro i hi m' hfr ⟨hp, hr⟩
    refine (hstep i hi m' hfr).mono
      (sup_le (fun b x hx => Or.inl ⟨i, by omega, hx⟩) le_sup_right) ?_
    intro m'' hfr' ⟨hp', hnew⟩
    refine ⟨hp'.trans hp, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hfr'.keep (hread j (by omega))
        (Fp.disj_sup_left.mpr ⟨hdisj i hi j (by omega) (by omega), hprotect j (by omega)⟩)
        (hr j hj)
    · exact hnew
  · exact sup_le (fun b x ⟨i, hi, hx⟩ => hsub i hi b x hx) hscratch

end NLAlib.Ops
