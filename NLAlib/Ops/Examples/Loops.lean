/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Nat.Size
public import NLAlib.Ops.Counted

/-!
# Example: a loop whose length comes from the data, and a hundred buffers

**Halving.** `NLAlib.Ops.Examples.halve` halves a word while it is not zero, with a fuel given as
a size. The number of rounds is not a size: it is the bit length of the number the word decodes
to.

## Main results

* `NLAlib.Ops.Examples.wp_halve`: total correctness by `wp_whileFuel`, with an invariant on the
  decoded state (`dec a = v / 2 ^ i` after `i` rounds) and the bound `Nat.size v` from the
  mathematics; the fuel only has to be at least that.
* `NLAlib.Ops.Examples.runs_halve`: the same with counts that depend on the data,
  `Nat.size v` calls of `half` and `Nat.size v + 1` tests, by `RunsFrom.whileFuel`. The loop
  leaves before the fuel is used up, and the fuel does not appear in the bound.
* `NLAlib.Ops.Examples.wpL_halve`: partial correctness with no bound at all.
* `NLAlib.Ops.Examples.exists_isHalving`: the contracts can be met.

**A hundred buffers.** `NLAlib.Ops.Examples.read_of_hundred`: reads through writes to other
buffers of an injective family of a hundred handles, with one disjointness hypothesis.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

/-- The operation of the halving loop. -/
inductive HOp where
  /-- `half [] [x] [x]`: halve a word. -/
  | half
  deriving DecidableEq

/-- The query of the halving loop. -/
inductive HTst where
  /-- The word is not zero. -/
  | nz
  deriving DecidableEq

variable {K : Type}

/-- **The contracts of the halving loop**: `half` is a function that halves the decoded number,
and the test `nz` is exact. -/
structure IsHalving (dec : K → ℕ) (h : K → K) (I : Interp HOp HTst K) : Prop where
  /-- `half` is the function `h`. -/
  half : I.IsFn .total .half (.un fun a => some (h a)) fun _ _ _ => True
  /-- `h` halves. -/
  dec_half : ∀ a, dec (h a) = dec a / 2
  /-- The test is exact on a readable cell. -/
  nz : ∀ d x m a, m.store.get x.1 x.2 = some a → I.test .nz d [x] m = some (decide (dec a ≠ 0))

/-- **Witness**: the contracts of the halving loop can be met, on natural numbers. -/
theorem exists_isHalving : ∃ (K : Type) (dec : K → ℕ) (h : K → K) (I : Interp HOp HTst K),
    IsHalving dec h I :=
  ⟨ℕ, id, fun a => a / 2,
    { Interp.ofFns (fun _ => .un fun a => some (a / 2)) with
      test := fun _ _ a m => match a with
        | [x] => (m.store.get x.1 x.2).map fun v => decide (v ≠ 0)
        | _ => none },
    { half := Interp.ofFns_isFn (Tst := HTst) (fun _ : HOp => .un fun a : ℕ => some (a / 2))
        .total .half _
      dec_half := fun _ => rfl
      nz := fun _ _ _ _ hx => by simp [hx] }⟩

/-- Halve the word `x` while it is not zero. Index variables: the fuel, the offset of `x`. -/
def halve : Stmt HOp HTst :=
  .whileFuel (.var 0) .nz [] [⟨0, .var 1⟩] (.call .half [] [⟨0, .var 1⟩] [⟨0, .var 1⟩])

/-- The invariant after `i` rounds: the cell holds a word that decodes to `v / 2 ^ i`. -/
def HalveInv (dec : K → ℕ) (m : Mem K) (x : ℕ × ℕ) (v : ℕ) (i : ℕ) (m' : Mem K) : Prop :=
  ∃ a, m' = m.upd x a ∧ dec a = v / 2 ^ i

theorem halveInv_test {dec : K → ℕ} {h : K → K} {I : Interp HOp HTst K}
    (hI : IsHalving dec h I) {m : Mem K} {x : ℕ × ℕ} {v : ℕ} (hx : x.2 < m.store.len x.1)
    (i : ℕ) (m' : Mem K) (hinv : HalveInv dec m x v i m') :
    ∃ b, I.test .nz [] [x] m' = some b ∧ (b = true → i < Nat.size v) := by
  obtain ⟨a, rfl, ha⟩ := hinv
  refine ⟨_, hI.nz [] x _ a (by store_simp), fun hb => ?_⟩
  rw [decide_eq_true_eq, ha, Nat.div_ne_zero_iff] at hb
  exact Nat.lt_size.mpr hb.2

theorem halveInv_step {dec : K → ℕ} {h : K → K} {I : Interp HOp HTst K}
    (hI : IsHalving dec h I) {τ : Tape K} {k : ℕ} {m : Mem K} {x : ℕ × ℕ} {v : ℕ}
    (hx : x.2 < m.store.len x.1) (i : ℕ) (m' : Mem K) (hinv : HalveInv dec m x v i m') :
    Wp .total I τ (.call .half [] [⟨0, .var 1⟩] [⟨0, .var 1⟩]) ⟨[k, x.2], [x.1]⟩
      (HalveInv dec m x v (i + 1)) m' := by
  obtain ⟨a, rfl, ha⟩ := hinv
  refine wp_call_un hI.half rfl rfl rfl trivial (a := a) (by store_simp) rfl (by store_simp)
    ⟨h a, by simp, ?_⟩
  rw [hI.dec_half, ha, Nat.div_div_eq_div_mul, pow_succ]

/-- **Total correctness of the halving loop**, with the bound on the rounds from the
mathematics: if the fuel is at least the bit length of the decoded number, the run ends with a
word that decodes to zero. -/
theorem wp_halve {dec : K → ℕ} {h : K → K} {I : Interp HOp HTst K} (hI : IsHalving dec h I)
    {τ : Tape K} {k : ℕ} {m : Mem K} {x : ℕ × ℕ} {a : K} (hx : m.store.get x.1 x.2 = some a)
    (hk : Nat.size (dec a) ≤ k) :
    Wp .total I τ halve ⟨[k, x.2], [x.1]⟩ (fun m' => ∃ a', m' = m.upd x a' ∧ dec a' = 0) m := by
  have hlt := Store.lt_len_of_get hx
  refine wp_whileFuel rfl rfl rfl (HalveInv dec m x (dec a)) (Nat.size (dec a)) hk
    ⟨a, by simp [Mem.upd, Store.upd_of_get hx], by simp⟩ (halveInv_test hI hlt)
    (fun i m' hinv _ => halveInv_step hI hlt i m' hinv) ?_
  rintro i m' - ⟨a', rfl, ha'⟩ hf
  rw [hI.nz [] x _ a' (by store_simp)] at hf
  exact ⟨a', rfl, by simpa using hf⟩

/-- **The halving loop with counts that depend on the data**: `Nat.size v` calls of `half` and
`Nat.size v + 1` tests, where `v` is the number the word decodes to; the fuel is not in the
bound. -/
theorem runs_halve {dec : K → ℕ} {h : K → K} {I : Interp HOp HTst K} (hI : IsHalving dec h I)
    (W : HOp → List ℕ → ℕ) {τ : Tape K} {k : ℕ} {m : Mem K} {x : ℕ × ℕ} {a : K}
    (hx : m.store.get x.1 x.2 = some a) (hk : Nat.size (dec a) ≤ k) :
    Runs I W τ halve ⟨[k, x.2], [x.1]⟩ m
      (Nat.size (dec a) • (Count.test .nz [] + Count.one .half []) + Count.test .nz [])
      (W .half []) (fun m' => ∃ a', m' = m.upd x a' ∧ dec a' = 0) := by
  have hlt := Store.lt_len_of_get hx
  refine ((RunsFrom.whileFuel rfl rfl rfl (HalveInv dec m x (dec a)) (Nat.size (dec a)) hk
    ⟨a, by simp [St.init, Mem.upd, Store.upd_of_get hx], by simp⟩ (halveInv_test hI hlt)
    fun i st hinv _ => (RunsFrom.of_wp (halveInv_step hI hlt i st.mem hinv)).mono
      (by simp [staticCost, useCost]) (by simp [staticPeak]) fun _ h => h).mono le_rfl le_rfl
    ?_).runs
  rintro m' ⟨i, -, ⟨a', rfl, ha'⟩, hf⟩
  rw [hI.nz [] x _ a' (by store_simp)] at hf
  exact ⟨a', rfl, by simpa using hf⟩

/-- **Partial correctness of the halving loop**, with no bound: if the run succeeds, whatever
the fuel, the word decodes to zero. -/
theorem wpL_halve {dec : K → ℕ} {h : K → K} {I : Interp HOp HTst K} (hI : IsHalving dec h I)
    {τ : Tape K} {k : ℕ} {m : Mem K} {x : ℕ × ℕ} {a : K} (hx : m.store.get x.1 x.2 = some a) :
    Wp .liberal I τ halve ⟨[k, x.2], [x.1]⟩ (fun m' => ∃ a', m' = m.upd x a' ∧ dec a' = 0) m := by
  have hlt := Store.lt_len_of_get hx
  refine wp_whileFuel_liberal rfl rfl (fun m' => ∃ a', m' = m.upd x a')
    ⟨a, by simp [Mem.upd, Store.upd_of_get hx]⟩ ?_ ?_
  · rintro m' ⟨a', rfl⟩ -
    exact Mode.Holds.of_total (wp_call_un hI.half rfl rfl rfl trivial (a := a') (by store_simp)
      rfl (by store_simp) ⟨h a', by simp⟩)
  · rintro m' ⟨a', rfl⟩ hf
    rw [hI.nz [] x _ a' (by store_simp)] at hf
    exact ⟨a', rfl, by simpa using hf⟩

/-- **A hundred buffers, one disjointness hypothesis**: reads after writes to other buffers of
an injective family, a scratch buffer included. -/
theorem read_of_hundred (s : Store K) (B : Fin 100 → ℕ) (hB : Function.Injective B)
    (hl : ∀ i, B i < s.length) (xs ys : List K) (v : K) (n : ℕ) (hx : xs.length = n)
    (hlen : 5 + n ≤ s.len (B 3)) (hq : s.readBlock (B 57) 0 n = some ys) :
    ((((s.push 2).updBlock (B 3) 5 xs).upd s.length 1 v).upd (B 99) 0 v).readBlock (B 57) 0 n =
        some ys ∧
      ((((s.push 2).updBlock (B 3) 5 xs).upd s.length 1 v).upd (B 99) 0 v).readBlock (B 3) 5 n =
        some xs ∧
      ((((s.push 2).updBlock (B 3) 5 xs).upd s.length 1 v).upd (B 99) 0 v).get s.length 1 =
        some v := by
  refine ⟨?_, ?_, ?_⟩ <;> store_simp

end NLAlib.Ops.Examples
