/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Deflation
public import NLAlib.Matrix.QRIteration.DeflationRanges

/-!
# Persistent output ranges of the deflation worklist

Only finished ranges have initialized output words. Ordinary spatial frames retain these
words while active blocks are processed; when every range is finished, their partition gives
one complete packed output column.

## Main results

* `NLAlib.ShiftedQR.FinishedHolds`: actual stored roots on the finished ranges.
* `NLAlib.ShiftedQR.FinishedHolds.of_eqOff`: preservation through disjoint writes.
* `NLAlib.ShiftedQR.FinishedHolds.holdsMatrix_of_partition`: completed packed output.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The actual word cells belonging to the listed finished ranges. -/
def finishedFp (b : ℕ × ℕ) (done : List (ℕ × ℕ)) : Fp :=
  fun c x => ∃ r ∈ done, Store.inBlock b.1 (b.2 + 2 * r.1) (2 * r.2) c x

/-- The finished ranges hold their corresponding roots; unfinished output words may be absent. -/
def FinishedHolds {n : ℕ} (b : ℕ × ℕ) (done : List (ℕ × ℕ))
    (roots : Fin (n + 1) → ℂ) (st : Store ℝ) : Prop :=
  ∀ r ∈ done, HoldsMatrix (b.1, b.2 + 2 * r.1)
    (Matrix.of fun i (_ : Fin 1) => subVec roots r i) st

/-- A finished output column is preserved by any write outside its actual range cells. -/
theorem FinishedHolds.of_eqOff {n : ℕ} {b : ℕ × ℕ} {done : List (ℕ × ℕ)}
    {roots : Fin (n + 1) → ℂ} {st st' : Store ℝ} {F : Fp}
    (h : FinishedHolds b done roots st) (hfr : st.EqOff F st')
    (hd : Fp.Disj F (finishedFp b done)) : FinishedHolds b done roots st' := by
  intro r hr
  exact (h r hr).of_eqOff hfr (fun c x hc hx =>
    hd c x hc ⟨r, hr, by simpa only [Nat.one_mul] using hx⟩)

/-- Finished cells lie in the persistent global output capacity whenever their ranges do. -/
theorem finishedFp_le {N : ℕ} {b : ℕ × ℕ} {done : List (ℕ × ℕ)}
    (hr : ∀ r ∈ done, r.1 + r.2 ≤ N) :
    finishedFp b done ≤ Store.inBlock b.1 b.2 (2 * N) := by
  rintro c x ⟨r, hrmem, hx⟩
  have hb := hr r hrmem
  exact ⟨hx.1, by have := hx.2.1; omega, by have := hx.2.2; omega⟩

/-- Pairwise disjoint mathematical ranges occupy disjoint output word blocks. -/
theorem disj_outputRanges (b : ℕ × ℕ) (r r' : ℕ × ℕ)
    (hd : r.1 + r.2 ≤ r'.1 ∨ r'.1 + r'.2 ≤ r.1) :
    Fp.Disj (Store.inBlock b.1 (b.2 + 2 * r.1) (2 * r.2))
      (Store.inBlock b.1 (b.2 + 2 * r'.1) (2 * r'.2)) := by
  rcases hd with hd | hd
  · exact Fp.disj_inBlock_of_le (by omega)
  · exact (Fp.disj_inBlock_of_le (by omega)).symm

/-- Finished ranges covering all indices give the actual complete output column.
No initialized words outside finished ranges are assumed. -/
theorem FinishedHolds.holdsMatrix_of_partition {n : ℕ} {b : ℕ × ℕ}
    {done : List (ℕ × ℕ)} {roots : Fin (n + 1) → ℂ} {st : Store ℝ}
    (h : FinishedHolds b done roots st) (hpart : IsRangePartition (n + 1) done) :
    HoldsMatrix b (Matrix.of fun i (_ : Fin 1) => roots i) st := by
  have hentry (i : Fin (n + 1)) :
      st.get b.1 (b.2 + 2 * i) = some (roots i).re ∧
      st.get b.1 (b.2 + 2 * i + 1) = some (roots i).im := by
    obtain ⟨r, ⟨hr, hlo, hhi⟩, _⟩ := hpart.2.2 i i.isLt
    have hi : (i : ℕ) - r.1 < r.2 := by omega
    have hidx : blockIndex n r ⟨i - r.1, hi⟩ = i := by
      apply Fin.ext
      simp only [blockIndex, Nat.add_sub_of_le hlo]
      exact min_eq_left (by omega)
    have hRe := (h r hr).get_re ⟨i - r.1, hi⟩ 0
    have hIm := (h r hr).get_im ⟨i - r.1, hi⟩ 0
    have he : b.2 + 2 * r.1 + 2 * ((i : ℕ) - r.1) = b.2 + 2 * i := by omega
    simpa only [Matrix.of_apply, subVec, Function.comp_apply, hidx,
      Fin.val_zero, Nat.zero_mul, Nat.zero_add, he] using And.intro hRe hIm
  apply HoldsMatrix.of_get
  · intro i j
    fin_cases j
    simpa using (hentry i).1
  · intro i j
    fin_cases j
    simpa using (hentry i).2

/-- The local eigenvalue kernel lists characteristic-polynomial roots with multiplicity. -/
theorem KernelRoutines.roots_smallEig {θ : ℝ} (K : KernelRoutines θ) (d : ℕ)
    (B : Matrix (Fin d) (Fin d) ℂ) :
    B.charpoly.roots = (List.ofFn (K.smallEig d B) : Multiset ℂ) := by
  rw [K.listing d B]
  simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
    List.prod_ofFn, Function.comp_def] using
    Polynomial.roots_multiset_prod_X_sub_C (List.ofFn (K.smallEig d B) : Multiset ℂ)

/-- Adding one finished range preserves all earlier output columns when their roots agree
and their cells are outside the actual newly written range. -/
theorem FinishedHolds.cons {n : ℕ} {b : ℕ × ℕ} {done : List (ℕ × ℕ)} {r : ℕ × ℕ}
    {roots roots' : Fin (n + 1) → ℂ} {st st' : Store ℝ}
    (h : FinishedHolds b done roots st)
    (hfr : st.EqOff (Store.inBlock b.1 (b.2 + 2 * r.1) (2 * r.2)) st')
    (hd : ∀ q ∈ done, q.1 + q.2 ≤ r.1 ∨ r.1 + r.2 ≤ q.1)
    (hagree : ∀ q ∈ done, subVec roots' q = subVec roots q)
    (hnew : HoldsMatrix (b.1, b.2 + 2 * r.1)
      (Matrix.of fun i (_ : Fin 1) => subVec roots' r i) st') :
    FinishedHolds b (r :: done) roots' st' := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hnew
  · have hkeep := (h q hq).of_eqOff hfr (by
      simpa only [Nat.one_mul] using (disj_outputRanges b r q (hd q hq).symm))
    simpa only [hagree q hq] using hkeep

end NLAlib.ShiftedQR
