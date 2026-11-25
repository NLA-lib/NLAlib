/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RankOneRounding
public import NLAlib.Computation.Underflow

/-!
# Rank-one updates with finite range and mixed rounding errors

Input magnitude bounds control each exact instruction result before its arithmetic success
law is invoked. Gradual underflow remains an additive error allowance.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_ger`: actual successful rank-one execution from numeric
  input and range bounds, with its local mixed-error witnesses and full matrix block write.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

omit [DecidableEq P] [AddMonoid C] in
private theorem exists_ger_scalars {u τ : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem)
    (p : P) {m n : ℕ} (aw : K) (xw : Fin m → K) (yw : Fin n → K)
    (Mw : Matrix (Fin m) (Fin n) K) {H D Ω : ℝ} (hu : 0 ≤ u p)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (ha : 0 < n → |dec p aw| ≤ D)
    (hx : 0 < n → ∀ i, |dec p (xw i)| ≤ H) (hy : ∀ j, |dec p (yw j)| ≤ H)
    (hM : ∀ i j, |dec p (Mw i j)| ≤ H) (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hct : D * H ≤ Ω) (hcq : H * ((1 + u p) * D * H + τ p) ≤ Ω)
    (hcz : H + ((1 + u p) * H * ((1 + u p) * D * H + τ p) + τ p) ≤ Ω) :
    ∃ (cy tv : Fin n → K) (qv zv : Matrix (Fin m) (Fin n) K),
      (∀ j, I.sem.un p .conj (yw j) = some (cy j) ∧ dec p (cy j) = dec p (yw j)) ∧
      (∀ j, I.sem.bin p .mul aw (cy j) = some (tv j)) ∧
      (∀ i j, I.sem.bin p .mul (xw i) (tv j) = some (qv i j)) ∧
      ∀ i j, I.sem.bin p .add (Mw i j) (qv i j) = some (zv i j) := by
  classical
  choose cy hcy hdcy using fun j => h.conj p (yw j)
  have hsafeT : ∀ j, safe p (dec p aw * dec p (cy j)) := by
    intro j
    apply hrange
    rw [abs_mul, hdcy]
    exact (mul_le_mul (ha (Nat.zero_lt_of_lt j.isLt)) (hy j) (abs_nonneg _) hD).trans hct
  choose tv htv using fun j => h.bin_ok p .mul aw (cy j) trivial (by simp) (hsafeT j)
  have ht : ∀ j, |dec p (tv j)| ≤ (1 + u p) * D * H + τ p := by
    intro j
    have hh := (h.bin_err p .mul aw (cy j) (tv j) trivial (htv j)).abs_le
    dsimp only [BinOp.realOp] at hh
    rw [abs_mul, hdcy] at hh
    calc |dec p (tv j)| ≤ (1 + u p) * (|dec p aw| * |dec p (yw j)|) + τ p := hh
         _ ≤ (1 + u p) * (D * H) + τ p := by
           gcongr
           · exact ha (Nat.zero_lt_of_lt j.isLt)
           · exact hy j
         _ = (1 + u p) * D * H + τ p := by ring
  have hsafeQ : ∀ i j, safe p (dec p (xw i) * dec p (tv j)) := by
    intro i j
    apply hrange
    rw [abs_mul]
    exact (mul_le_mul (hx (Nat.zero_lt_of_lt j.isLt) i) (ht j) (abs_nonneg _) hH).trans hcq
  choose qv hqv using fun i j => h.bin_ok p .mul (xw i) (tv j) trivial (by simp) (hsafeQ i j)
  have hq : ∀ i j, |dec p (qv i j)| ≤
      (1 + u p) * H * ((1 + u p) * D * H + τ p) + τ p := by
    intro i j
    have hh := (h.bin_err p .mul (xw i) (tv j) (qv i j) trivial (hqv i j)).abs_le
    dsimp only [BinOp.realOp] at hh
    rw [abs_mul] at hh
    calc |dec p (qv i j)| ≤ (1 + u p) * (|dec p (xw i)| * |dec p (tv j)|) + τ p := hh
         _ ≤ (1 + u p) * (H * ((1 + u p) * D * H + τ p)) + τ p := by
           gcongr
           · exact hx (Nat.zero_lt_of_lt j.isLt) i
           · exact ht j
         _ = (1 + u p) * H * ((1 + u p) * D * H + τ p) + τ p := by ring
  have hsafeZ : ∀ i j, safe p (dec p (Mw i j) + dec p (qv i j)) := by
    intro i j
    exact hrange _ ((abs_add_le _ _).trans ((add_le_add (hM i j) (hq i j)).trans hcz))
  choose zv hzv using fun i j => h.bin_ok p .add (Mw i j) (qv i j) trivial (by simp) (hsafeZ i j)
  exact ⟨cy, tv, qv, zv, fun j => ⟨hcy j, hdcy j⟩, htv, hqv, hzv⟩

/-- Numeric input envelopes imply successful execution of the actual rank-one update under
mixed absolute-relative errors and finite range. All three exact arithmetic result envelopes
are checked before running their instructions. Conjugation has exact real decoding. Sources
must be block-disjoint from the matrix output, while arbitrary carriers and charges and empty
dimensions are supported. The output has the actual two multiply and one add error witnesses.
[Higham2002, §2.2; §3.2]. -/
theorem IsArithErrSem.exec_ger {u τ : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem)
    (p : P) (st : St P K C) (m n : IExp ℕ) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (av : ℝ) (xs : Fin m.eval → ℝ) (ys : Fin n.eval → ℝ)
    (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) {H D Ω : ℝ}
    (hu : 0 ≤ u p) (hH : 0 ≤ H) (hD : 0 ≤ D) (hav : |av| ≤ D)
    (hxs : ∀ i, |xs i| ≤ H) (hys : ∀ j, |ys j| ≤ H) (hMs : ∀ i j, |M i j| ≤ H)
    (hrange : ∀ b, |b| ≤ Ω → safe p b)
    (hct : D * H ≤ Ω) (hcq : H * ((1 + u p) * D * H + τ p) ≤ Ω)
    (hcz : H + ((1 + u p) * H * ((1 + u p) * D * H + τ p) + τ p) ≤ Ω)
    (ha : 0 < n.eval → ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : 0 < n.eval → ReadsDecoded st.store dec p x xo.eval xs)
    (hy : ReadsDecoded st.store dec p y yo.eval ys) (hM : HoldsDecoded st.store dec p A ao.eval M)
    (haA : blockDisjoint (a.buf, a.idx.eval, 1) (A, ao.eval, m.eval * n.eval) = true)
    (hxA : blockDisjoint (x, xo.eval, m.eval) (A, ao.eval, m.eval * n.eval) = true)
    (hyA : blockDisjoint (y, yo.eval, n.eval) (A, ao.eval, m.eval * n.eval) = true) :
    ∃ (out : St P K C) (W : Array K) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin m.eval) (Fin n.eval) ℝ),
      W.size = m.eval * n.eval ∧ exec I (ger p m n a x xo y yo A ao).run st = some out ∧
      st.store.writeBlock p A ao.eval W = some out.store ∧
      (∀ j, AbsRelErr (u p) (τ p) (av * ys j) (t j)) ∧
      ∀ i j, AbsRelErr (u p) (τ p) (xs i * t j) (q i j) ∧
        AbsRelErr (u p) (τ p) (M i j + q i j)
          (unflatten m.eval n.eval (W.map (dec p)) i j) := by
  classical
  obtain ⟨w₀, _, _⟩ := h.lit_zero p
  have ha' : ∃ w, ∀ hn : 0 < n.eval,
      st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av := by
    by_cases hn : 0 < n.eval
    · obtain ⟨w, hw⟩ := ha hn
      exact ⟨w, fun _ => hw⟩
    · exact ⟨w₀, fun hh => (hn hh).elim⟩
  obtain ⟨aw, haw⟩ := ha'
  have hx' : ∀ i : Fin m.eval, ∃ w, ∀ hn : 0 < n.eval,
      st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i := by
    intro i
    by_cases hn : 0 < n.eval
    · obtain ⟨w, hw⟩ := hx hn i
      exact ⟨w, fun _ => hw⟩
    · exact ⟨w₀, fun hh => (hn hh).elim⟩
  choose xw hxw using hx'
  choose yw hyw hdyw using hy
  choose Mw hMw hdMw using hM
  change Matrix (Fin m.eval) (Fin n.eval) K at Mw
  obtain ⟨cy, tv, qv, zv, hcy, htv, hqv, hzv⟩ := exists_ger_scalars I h p aw xw yw Mw
    hu hH hD (fun hn => by simpa only [(haw hn).2] using hav)
    (fun hn i => by simpa only [(hxw i hn).2] using hxs i)
    (fun j => by simpa only [hdyw] using hys j) (fun i j => by simpa only [hdMw] using hMs i j)
    hrange hct hcq hcz
  let xv (i : ℕ) := if hi : i < m.eval then xw ⟨i, hi⟩ else w₀
  let yv (j : ℕ) := if hj : j < n.eval then yw ⟨j, hj⟩ else w₀
  let cv (j : ℕ) := if hj : j < n.eval then cy ⟨j, hj⟩ else w₀
  let vt (j : ℕ) := if hj : j < n.eval then tv ⟨j, hj⟩ else w₀
  let Mv (i j : ℕ) := if hij : i < m.eval ∧ j < n.eval then Mw ⟨i, hij.1⟩ ⟨j, hij.2⟩ else w₀
  let vq (i j : ℕ) := if hij : i < m.eval ∧ j < n.eval then qv ⟨i, hij.1⟩ ⟨j, hij.2⟩ else w₀
  let vz (i j : ℕ) := if hij : i < m.eval ∧ j < n.eval then zv ⟨i, hij.1⟩ ⟨j, hij.2⟩ else w₀
  obtain ⟨out, W, hWs, hr, hw, hW⟩ := RankOneRounding.exec_ger_words I p st m n a x xo y yo A ao
    aw xv yv cv vt Mv vq vz (fun hn => (haw hn).1)
    (fun hn i hi => by simpa only [xv, dif_pos hi] using (hxw ⟨i, hi⟩ hn).1)
    (fun j hj => by simpa only [yv, dif_pos hj] using hyw ⟨j, hj⟩)
    (fun i hi j hj => by simpa only [Mv, dif_pos (And.intro hi hj)] using hMw ⟨i, hi⟩ ⟨j, hj⟩)
    haA hxA hyA (fun j hj => by simpa only [yv, cv, dif_pos hj] using (hcy ⟨j, hj⟩).1)
    (fun j hj => by simpa only [cv, vt, dif_pos hj] using htv ⟨j, hj⟩)
    (fun i hi j hj => by
      simpa only [xv, vt, vq, dif_pos hi, dif_pos hj, dif_pos (And.intro hi hj)] using
        hqv ⟨i, hi⟩ ⟨j, hj⟩)
    (fun i hi j hj => by
      simpa only [Mv, vq, vz, dif_pos (And.intro hi hj)] using hzv ⟨i, hi⟩ ⟨j, hj⟩)
  refine ⟨out, W, fun j => dec p (tv j), fun i j => dec p (qv i j), hWs, hr, hw, ?_, ?_⟩
  · intro j
    have hh := h.bin_err p .mul aw (cy j) (tv j) trivial (htv j)
    simpa only [BinOp.realOp, (haw (Nat.zero_lt_of_lt j.isLt)).2, (hcy j).2, hdyw] using hh
  · intro i j
    have hout : unflatten m.eval n.eval (W.map (dec p)) i j = dec p (zv i j) := by
      simp only [unflatten, Matrix.of_apply, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        hW i i.isLt j j.isLt, vz, dif_pos (And.intro i.isLt j.isLt), Option.map_some,
        Option.getD_some]
    constructor
    · simpa only [BinOp.realOp, (hxw i (Nat.zero_lt_of_lt j.isLt)).2] using
        h.bin_err p .mul (xw i) (tv j) (qv i j) trivial (hqv i j)
    · simpa only [BinOp.realOp, hout, hdMw] using
        h.bin_err p .add (Mw i j) (qv i j) (zv i j) trivial (hzv i j)

end NLAlib.Computation
