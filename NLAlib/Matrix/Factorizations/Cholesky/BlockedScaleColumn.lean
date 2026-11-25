/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.Logic.ScalarLoop

/-!
# Actual square-root scaling of a stored LU column

Blocked Cholesky scales a canonical unit lower LU column by the square root of its upper
pivot. This scalar routine explicitly zeroes the upper prefix and multiplies every diagonal
and lower word. Its word statement uses the actual machine root and products, with no exact
arithmetic assumption. The multiplication loop reuses the shared scalar-loop judgment.

## Main results

* `NLAlib.Cholesky.scaleLuColumn_meets`: actual zero prefix and square-root-scaled suffix.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Square-root one upper pivot, write literal upper zeros, and multiply the diagonal-inclusive
lower suffix in place. The root temporary is scoped. -/
def scaleLuColumn : Routine Op Tst := routine% [n, k] (d : 1, x : n) → (x) {
  let t ← alloc 1;
  call (Has.inj ScalarOp.sqrt) [] (d) → (t);
  run (fillRoutine (Has.inj (ScalarOp.lit 0))) [k] (x);
  for i < n - k {
    call (Has.inj ScalarOp.mul) [] (x[k + i], t) → (x[k + i])
  }
}

variable [Inhabited K]

/-- The actual words of a zeroed upper prefix and diagonal-inclusive scaled lower suffix. -/
def scaleLuColumnWords (M : Machine K) (p : K) (xs : List K) (n k : ℕ) : List K :=
  (List.range n).map fun i => if i < k then M.lit 0 else M.mul (vec xs i) (M.sqrt p)

/-- Only the split bound is required. The root and products are actual machine values. -/
def scaleLuColumnSpec (M : Machine K) : Routine.Spec K :=
  spec% [n, k] ([p], xs) → (ys) requires k ≤ n ensures ys = scaleLuColumnWords M p xs n k

omit [Has ScalarOp Op] in
private theorem readBlock_scaleLuColumnWords (M : Machine K) (p : K) (xs : List K)
    {s s' : Store K} {b off n k : ℕ} (hk : k ≤ n)
    (hprefix : s.readBlock b off k = some (List.replicate k (M.lit 0)))
    (htail : s.readBlock b (off + k) (n - k) = some ((xs.drop k).take (n - k)))
    (hfr : s.EqOff (Store.inBlock b (off + k) (n - k)) s')
    (hscale : ∀ i < n - k, ∀ w, s.get b (off + k + i) = some w →
      s'.get b (off + k + i) = some (M.mul w (M.sqrt p))) :
    s'.readBlock b off n = some (scaleLuColumnWords M p xs n k) := by
  apply Store.readBlock_eq_some_iff.mpr
  refine ⟨by simp only [scaleLuColumnWords, List.length_map, List.length_range], ?_⟩
  intro i hi
  simp only [scaleLuColumnWords, List.getElem?_map, List.getElem?_range hi, Option.map_some]
  by_cases hik : i < k
  · rw [if_pos hik, hfr.get_eq ?_]
    · have hg := Store.get_of_readBlock hprefix hik default
      have hz : vec (List.replicate k (M.lit 0)) i = M.lit 0 := by
        simp [vec, List.getD_eq_getElem?_getD, hik]
      simpa only [hz] using hg
    · rintro ⟨_, hlo, _⟩
      omega
  · rw [if_neg hik]
    have hii : i - k < n - k := by omega
    have haddr : off + k + (i - k) = off + i := by omega
    have hg := Store.get_of_readBlock htail hii default
    have he : vec ((xs.drop k).take (n - k)) (i - k) = vec xs i := by
      rw [vec_drop_take hii, Nat.add_sub_of_le (Nat.le_of_not_gt hik)]
    have hg' : s.get b (off + k + (i - k)) = some (vec xs i) := by
      simpa only [he] using hg
    simpa only [haddr] using hscale (i - k) hii (vec xs i) hg'

/-- The complete scalar root, fill and multiply-loop tree meets its machine-word
specification. The numerical sign and accuracy of the root are separate consumer obligations. -/
theorem scaleLuColumn_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (scaleLuColumn (Op := Op) (Tst := Tst)).Meets I (scaleLuColumnSpec M) := by
  routine_intro [n, k] (d, x) reads (ds, xs)
  obtain ⟨p, hp, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  change k ≤ n at hpre
  have hlx : x.1 < m.store.length := hlive x (by simp)
  change Writes .total I τ _ (Env.frame [n, k] [d, x, x]) (Fp.blocks [x] [n]) _ m
  alloc as t
  have hxt : x.1 ≠ t := by change x.1 ≠ m.store.length + 0; omega
  have hxs₀ := Store.Below.readBlock_of hbelow_t hlx hxs
  step (hI .sqrt) as m₁ hfr₁ ⟨hpos₁, root, hroot, rfl⟩
  have hxs₁ : m₁.store.readBlock x.1 x.2 n = some xs := by keep
  have htail₁ : m₁.store.readBlock x.1 (x.2 + k) (n - k) =
      some ((xs.drop k).take (n - k)) := Store.readBlock_sub hxs₁ (by omega)
  call (fillRoutine_meets (hI (.lit 0))) [k] (x)
    as m₂ hfr₂ hpos₂ (zs) hfill
  have hfilled : zs = List.replicate k (M.lit 0) := hfill
  have hprefix : m₂.store.readBlock x.1 x.2 k = some (List.replicate k (M.lit 0)) := by
    simpa only [hfilled] using hzs
  have htail₂ : m₂.store.readBlock x.1 (x.2 + k) (n - k) =
      some ((xs.drop k).take (n - k)) := by keep
  have hroot₂ : m₂.store.get t 0 = some (M.sqrt p) := by keep
  have hLive : m₂.Live [(x.1, x.2 + k), (t, 0)] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    have hlen : m₂.store.length = s_t.length := hfr₂.length_eq.trans hfr₁.length_eq
    simp only [List.length_singleton] at hlen_t
    change x.1 < m₂.store.length ∧ m.store.length + 0 < m₂.store.length
    exact ⟨by omega, by omega⟩
  refine (writes_loop_mul_cell hI rfl (fun _ _ => rfl) (fun _ _ => rfl) hLive
    (fun i hi => ⟨vec ((xs.drop k).take (n - k)) i, Store.get_of_readBlock htail₂ hi default⟩)
    hroot₂ (by rintro ⟨he, _⟩; exact hxt he.symm)).mono (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hpos₃, hscaled⟩
  have hread := readBlock_scaleLuColumnWords M p xs hpre hprefix htail₂ hfr₃ hscaled
  intro s₂ hs₂ hB₂
  exact ⟨hpos₃.trans (hpos₂.trans hpos₁), [scaleLuColumnWords M p xs n k],
    Mem.readBlocks_of_cons (Store.Below.readBlock_of hB₂ hlx hread) rfl, rfl⟩

end NLAlib.Cholesky
