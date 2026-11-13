/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Slots

/-!
# Mathematical recursion of spectral bisection by levels

The nodes reached at one depth have its radius, tolerance and depth counter. Their slot ranges
lie inside the root range and are pairwise disjoint. Sample trees restrict to the same subtrees
as path traversal. These facts depend only on the pure matrix algorithm and its slot geometry.

## Main results

* `NLAlib.eighNodeAt_eighSlotTree`, `NLAlib.eighSlotTree_append_of_eighLoc`: sample subtrees.
* `NLAlib.eighLoc_params`, `NLAlib.eighLoc_bounds`, `NLAlib.eighLoc_disjoint`:
  level parameters and slot geometry.
* `NLAlib.eighLoc_append_singleton`: child traversal along an extended path.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-! ### The recursion by levels -/

section Levels

variable {F : Type*} {M : FloatMachine F ℕ ℕ} {N signFuel : ℕ} {R₀ β : F}

/-- The nodes at the slots are the nodes of the tree of samples at the slots: at every path,
`NLAlib.eighNodeAt` with the samples `NLAlib.eighSlotTree` (from the node $x$ at slot $lo$ of depth
$d$) reaches the node that `NLAlib.eighLoc` reaches. No printed source. -/
theorem eighNodeAt_eighSlotTree :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode F),
      eighNodeAt M N signFuel R₀ β a x (eighSlotTree M N signFuel R₀ β d lo x) =
        (eighLoc M N signFuel R₀ β d lo x a).map Prod.snd := by
  intro a
  induction a with
  | nil => intro d lo x; rfl
  | cons b a ih =>
    intro d lo x
    cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | leaf U e => simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs]
    | shift b' A' σ =>
      by_cases hb : b = b'
      · subst hb; simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs, ih]
      · simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs, hb]
    | split kp h Qp Qm Ap Am σ =>
      cases b <;> simp [eighNodeAt, eighChild, eighLoc, eighSlotTree, hs, ih]

/-- The tree of samples at the slots restricts to subtrees: below a path that reaches the node
$y$ at slot $lo'$, the tree of samples is the tree from $y$ at slot $lo'$ of the depth of the path.
No printed source. -/
theorem eighSlotTree_append_of_eighLoc :
    ∀ {a : List Bool} {d lo lo' : ℕ} {x y : EighNode F},
      eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
        (fun a' => eighSlotTree M N signFuel R₀ β d lo x (a ++ a')) =
          eighSlotTree M N signFuel R₀ β (d + a.length) lo' y := by
  intro a
  induction a with
  | nil =>
    intro d lo lo' x y h
    simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    funext a'
    simp
  | cons b a ih =>
    intro d lo lo' x y h
    funext a'
    cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | leaf U e => simp [eighLoc, hs] at h
    | shift b' A' σ =>
      by_cases hb : b = b'
      · subst hb
        simp only [eighLoc, hs, if_true] at h
        have h2 := congrFun (ih h) a'
        simp only [List.cons_append, eighSlotTree, hs, List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
        exact h2
      · simp [eighLoc, hs, hb] at h
    | split kp h' Qp Qm Ap Am σ =>
      cases b
      · simp only [eighLoc, hs, Bool.false_eq_true, if_false] at h
        have h2 := congrFun (ih h) a'
        simp only [List.cons_append, eighSlotTree, hs, Bool.false_eq_true, if_false,
          List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
        exact h2
      · simp only [eighLoc, hs, if_true] at h
        have h2 := congrFun (ih h) a'
        simp only [List.cons_append, eighSlotTree, hs, if_true, List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
        exact h2

/-- The nodes at a depth have the parameters of the depth: a node that `NLAlib.eighLoc` reaches
from the root $(N, \mathbf{A}, R_0, \varepsilon, \ell_0)$ at a path of length $d$ has the window and
tolerance `NLAlib.eighLevelParams` at $d$ and the depth counter $\ell_0 + d$. No printed source. -/
theorem eighLoc_params {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ} {a : List Bool}
    {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    y.R = (eighLevelParams M R₀ ε ℓ₀ a.length).1 ∧ y.ε = (eighLevelParams M R₀ ε ℓ₀ a.length).2 ∧
      y.ℓ = ℓ₀ + a.length := by
  have key : ∀ (a : List Bool) (d lo : ℕ) (x y : EighNode F) (lo' : ℕ),
      x.R = (eighLevelParams M R₀ ε ℓ₀ d).1 → x.ε = (eighLevelParams M R₀ ε ℓ₀ d).2 →
      x.ℓ = ℓ₀ + d → eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
      y.R = (eighLevelParams M R₀ ε ℓ₀ (d + a.length)).1 ∧
        y.ε = (eighLevelParams M R₀ ε ℓ₀ (d + a.length)).2 ∧
        y.ℓ = ℓ₀ + (d + a.length) := by
    intro a
    induction a with
    | nil =>
      intro d lo x y lo' hR hε hℓ h
      simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [List.length_nil, Nat.add_zero]
      exact ⟨hR, hε, hℓ⟩
    | cons b a ih =>
      intro d lo x y lo' hR hε hℓ h
      have e : d + (b :: a).length = d + 1 + a.length := by simp only [List.length_cons]; omega
      have hq : eighNextParams M x.R x.ε x.ℓ = eighLevelParams M R₀ ε ℓ₀ (d + 1) := by
        rw [eighLevelParams, hR, hε, hℓ]
      cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
      | leaf U e' => simp [eighLoc, hs] at h
      | shift b' A' σ =>
        by_cases hb : b = b'
        · subst hb
          simp only [eighLoc, hs, if_true] at h
          obtain ⟨h1, h2, h3⟩ := ih (d + 1) lo _ y lo'
            (by exact congrArg Prod.fst hq) (by exact congrArg Prod.snd hq)
            (by change x.ℓ + 1 = ℓ₀ + (d + 1); omega) h
          rw [e]; exact ⟨h1, h2, h3⟩
        · simp [eighLoc, hs, hb] at h
      | split kp h' Qp Qm Ap Am σ =>
        cases b
        · simp only [eighLoc, hs, Bool.false_eq_true, if_false] at h
          obtain ⟨h1, h2, h3⟩ := ih (d + 1) (lo + kp) _ y lo'
            (by exact congrArg Prod.fst hq) (by exact congrArg Prod.snd hq)
            (by change x.ℓ + 1 = ℓ₀ + (d + 1); omega) h
          rw [e]; exact ⟨h1, h2, h3⟩
        · simp only [eighLoc, hs, if_true] at h
          obtain ⟨h1, h2, h3⟩ := ih (d + 1) lo _ y lo'
            (by exact congrArg Prod.fst hq) (by exact congrArg Prod.snd hq)
            (by change x.ℓ + 1 = ℓ₀ + (d + 1); omega) h
          rw [e]; exact ⟨h1, h2, h3⟩
  obtain ⟨h1, h2, h3⟩ := key a 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ y lo rfl rfl rfl h
  rw [Nat.zero_add] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- A child's slot: the slot and node at the path $a ++ [b]$ are those of the child on side $b$
of the node at $a$, at the slot $lo$ (one child, or the positive side of a split) or $lo + k_+$
(the negative side of a split). No printed source. -/
theorem eighLoc_append_singleton :
    ∀ (a : List Bool) (b : Bool) (d lo : ℕ) (x : EighNode F),
      eighLoc M N signFuel R₀ β d lo x (a ++ [b]) =
        (eighLoc M N signFuel R₀ β d lo x a).bind fun z =>
          eighLoc M N signFuel R₀ β (d + a.length) z.1 z.2 [b] := by
  intro a
  induction a with
  | nil => intro b d lo x; simp [eighLoc]
  | cons c a ih =>
    intro b d lo x
    cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | leaf U e => simp [eighLoc, hs]
    | shift b' A' σ =>
      by_cases hc : c = b'
      · subst hc
        simp only [List.cons_append, eighLoc, hs, if_true, ih,
          List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
      · simp [eighLoc, hs, hc]
    | split kp h' Qp Qm Ap Am σ =>
      cases c
      · simp only [List.cons_append, eighLoc, hs, Bool.false_eq_true, if_false, ih,
          List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]
      · simp only [List.cons_append, eighLoc, hs, if_true, ih, List.length_cons]
        rw [show d + (a.length + 1) = d + 1 + a.length by omega]

/-- The nodes at a depth lie in $[0, N)$ and are not empty: a node that `NLAlib.eighLoc` reaches
from a root of size $N \ge 1$ at slot $0$ has size at least $1$ and its range $[lo, lo + k)$ inside
$[0, N)$. No printed source. -/
theorem eighLoc_bounds {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ} (hN : 1 ≤ N)
    {a : List Bool} {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    1 ≤ y.k ∧ lo + y.k ≤ N := by
  have key : ∀ (a : List Bool) (d lo : ℕ) (x y : EighNode F) (lo' : ℕ), 1 ≤ x.k →
      lo + x.k ≤ N → eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
      1 ≤ y.k ∧ lo' + y.k ≤ N := by
    intro a
    induction a with
    | nil =>
      intro d lo x y lo' hk hN' h
      simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hk, hN'⟩
    | cons b a ih =>
      intro d lo x y lo' hk hN' h
      cases hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
      | leaf U e => simp [eighLoc, hs] at h
      | shift b' A' σ =>
        by_cases hb : b = b'
        · subst hb
          simp only [eighLoc, hs, if_true] at h
          exact ih (d + 1) lo _ y lo' (by exact hk) (by exact hN') h
        · simp [eighLoc, hs, hb] at h
      | split kp h' Qp Qm Ap Am σ =>
        have hb : 0 < kp ∧ kp < x.k := by
          unfold eighStep at hs
          dsimp only at hs
          split_ifs at hs; (try cases hs); omega
        cases b
        · simp only [eighLoc, hs, Bool.false_eq_true, if_false] at h
          exact ih (d + 1) (lo + kp) _ y lo' (by change 1 ≤ x.k - kp; omega)
            (by change lo + kp + (x.k - kp) ≤ N; omega) h
        · simp only [eighLoc, hs, if_true] at h
          exact ih (d + 1) lo _ y lo' (by change 1 ≤ kp; omega)
            (by change lo + kp ≤ N; omega) h
  exact key a 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ y lo hN (Nat.zero_add N).le h

/-- The nodes at a depth lie in $[0, N]$, for every $N$: a node that `NLAlib.eighLoc` reaches from
the root of size $N$ at slot $0$ has its range $[lo, lo + k)$ inside $[0, N)$, and size at least
$1$ when $N \ge 1$. No printed source. -/
theorem add_k_le_and_of_eighLoc {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ}
    {a : List Bool} {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    lo + y.k ≤ N ∧ (1 ≤ N → 1 ≤ y.k) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, fun h => absurd h (by omega)⟩
    cases a with
    | nil => cases h; rfl
    | cons b a => simp [eighLoc, eighStep] at h
  · exact ⟨(eighLoc_bounds hN h).2, fun _ => (eighLoc_bounds hN h).1⟩

/-- The slot ranges of the nodes that `NLAlib.eighLoc` reaches lie inside the range of their
start. -/
private theorem eighLoc_range_aux :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode F) {l : ℕ} {y : EighNode F},
      eighLoc M N signFuel R₀ β d lo x a = some (l, y) → lo ≤ l ∧ l + y.k ≤ lo + x.k
  | [], d, lo, x, l, y, h => by
    simp only [eighLoc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨le_rfl, le_rfl⟩
  | b :: a, d, lo, x, l, y, h => by
    simp only [eighLoc] at h
    split at h
    · simp at h
    · rename_i b' A' σ
      split_ifs at h with hb
      · obtain ⟨h1, h2⟩ := eighLoc_range_aux a (d + 1) lo _ h
        exact ⟨h1, by simpa using h2⟩
    · rename_i kp hkp _ _ _ Ap Am _
      split_ifs at h with hb
      · obtain ⟨h1, h2⟩ := eighLoc_range_aux a (d + 1) lo _ h
        exact ⟨h1, by simp only at h2; omega⟩
      · obtain ⟨h1, h2⟩ := eighLoc_range_aux a (d + 1) (lo + kp) _ h
        exact ⟨by omega, by simp only at h2; omega⟩

/-- Two distinct paths of one length from one node reach nodes with disjoint slot ranges. -/
private theorem eighLoc_disjoint_aux :
    ∀ (a a' : List Bool) (d lo : ℕ) (x : EighNode F) (l l' : ℕ) (y y' : EighNode F),
      a.length = a'.length → a ≠ a' →
      eighLoc M N signFuel R₀ β d lo x a = some (l, y) →
      eighLoc M N signFuel R₀ β d lo x a' = some (l', y') →
      l + y.k ≤ l' ∨ l' + y'.k ≤ l
  | [], a', _, _, _, _, _, _, _, hlen, hne, _, _ => by
    cases a' with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hlen
  | b :: a, a', d, lo, x, l, l', y, y', hlen, hne, h, h' => by
    cases a' with
    | nil => simp at hlen
    | cons b' a' =>
    simp only [eighLoc] at h h'
    generalize eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) = s at h h'
    cases s with
    | leaf U dd => simp at h
    | shift c A' σ =>
      by_cases hb : b = c <;> by_cases hb' : b' = c
      · subst hb; subst hb'
        have hne' : a ≠ a' := fun e => hne (by rw [e])
        simp only [if_true] at h h'
        exact eighLoc_disjoint_aux a a' (d + 1) lo _ l l' y y' (by simpa using hlen) hne' h h'
      all_goals (simp only [if_pos, *] at h h'; simp at h h')
    | split kp hkp Qp Qm Ap Am σ =>
      cases b <;> cases b' <;>
        simp only [Bool.false_eq_true, if_true, if_false] at h h'
      · have hne' : a ≠ a' := fun e => hne (by rw [e])
        exact eighLoc_disjoint_aux a a' (d + 1) (lo + kp) _ l l' y y' (by simpa using hlen) hne'
          h h'
      · have h1 := eighLoc_range_aux a (d + 1) (lo + kp) _ h
        have h2 := eighLoc_range_aux a' (d + 1) lo _ h'
        dsimp only at h1 h2
        omega
      · have h1 := eighLoc_range_aux a (d + 1) lo _ h
        have h2 := eighLoc_range_aux a' (d + 1) (lo + kp) _ h'
        dsimp only at h1 h2
        omega
      · have hne' : a ≠ a' := fun e => hne (by rw [e])
        exact eighLoc_disjoint_aux a a' (d + 1) lo _ l l' y y' (by simpa using hlen) hne' h h'

/-- The nodes at one depth have disjoint ranges: two distinct paths of the same length that
`NLAlib.eighLoc` follows from the root reach nodes whose ranges $[lo, lo + k)$ do not meet. So the
nodes of one level partition a part of $[0, N)$, and their packed blocks in the arenas are disjoint.
No printed source. -/
theorem eighLoc_disjoint {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ}
    {a a' : List Bool} (hlen : a.length = a'.length) (hne : a ≠ a') {lo lo' : ℕ}
    {y y' : EighNode F} (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) :
    lo + y.k ≤ lo' ∨ lo' + y'.k ≤ lo :=
  eighLoc_disjoint_aux a a' 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ lo lo' y y' hlen hne h h'

end Levels

end NLAlib
