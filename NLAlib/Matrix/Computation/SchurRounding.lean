/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.CopyStride
public import NLAlib.Matrix.Computation.SchurUpdate
public import NLAlib.Computation.BLAS.RankOneRounding

/-!
# Rounded execution of the saved-pivot Schur update

The actual routine copies its pivot row and column before updating the matrix. Its coefficient
is obtained by rounding the literal minus one and dividing by the original pivot. The rounded
rank-one theorem then records each multiply and addition, with successful execution and the
complete output block frame. This is a local instruction trace, not a full factorization bound.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_schurStep`: success, matrix write and scalar witnesses.
* `NLAlib.Computation.IsRelErrSem.exec_schurStep_abs_sub_le`: the five-factor local defect bound.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

namespace SchurRounding

private structure SchurPrepared {n : ℕ} (p : P) (initial : Store P K) (work : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (k : Fin n) (c : K) (final : Store P K) : Prop where
  shape : final.shape = initial.shape
  frame : ∀ q b i, b ≠ work → final.read q b i = initial.read q b i
  col : ∀ i : Fin n, final.read p work i = some (M i k)
  row : ∀ j : Fin n, final.read p work (n + j) = some (M k j)
  coeff : final.read p work (2 * n) = some c

private theorem exec_prepareSchur (I : Interp P ι K C) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (p : P) (st : St P K C) (n : IExp ℕ) (R work : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) K) (hk : pivot.eval < n.eval)
    (hM : Holds st.store p R off.eval M) (hne : R ≠ work)
    (hw : st.store.shape[work]? = some (p, 2 * n.eval + 1))
    (hp : dec p (M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) ≠ 0) :
    ∃ (out : St P K C) (ell c : K), exec I (prepareSchur p n R work off pivot).run st = some out ∧
      SchurPrepared p st.store work M ⟨pivot.eval, hk⟩ c out.store ∧
      RelErr (u p) (-1) (dec p ell) ∧
      RelErr (u p) (dec p ell / dec p (M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩)) (dec p c) := by
  obtain ⟨ell, hell⟩ := h.lit_ok p (-1) trivial
  obtain ⟨c, hc⟩ := h.bin_ok p .div ell (M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩)
    trivial (fun _ => hp) trivial
  obtain ⟨out, hr, hsh, hfr, hcol, hrow, hcoeff⟩ :=
    exec_prepareSchur_of_scalar_results I p st n R work off pivot M hk hM hne hw ell c hell hc
  refine ⟨out, ell, c, hr, ⟨hsh, hfr, hcol, hrow, hcoeff⟩, ?_, ?_⟩
  · simpa only [RelErr, Rat.cast_neg, Rat.cast_one] using h.lit_err p (-1) ell hell
  · exact h.bin_err p .div ell (M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c trivial hc

/-- The actual saved-pivot body, with its local scalar error witnesses and popped frame. -/
private theorem exec_schurBody (I : Interp P ι K C) {u : P → ℝ} {dec : P → K → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (initial : Store P K) (st : St P K C) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : HoldsDecoded initial dec p R off.eval M)
    (hp : M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩ ≠ 0)
    (hst : st.store = initial.push (p, Array.replicate (2 * n.eval + 1) none)) :
    ∃ (out : St P K C) (W : Array K) (ell c : ℝ) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
      exec I (do
        prepareSchur p n R initial.size off pivot
        ger p n n ⟨initial.size, 2 * n⟩ initial.size 0 initial.size n R off).run st = some out ∧
      W.size = n.eval * n.eval ∧ initial.writeBlock p R off.eval W = some out.store.pop ∧
      RelErr (u p) (-1) ell ∧ RelErr (u p) (ell / M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c ∧
      (∀ j, RelErr (u p) (c * M ⟨pivot.eval, hk⟩ j) (t j)) ∧
      ∀ i j, RelErr (u p) (M i ⟨pivot.eval, hk⟩ * t j) (q i j) ∧
        RelErr (u p) (M i j + q i j)
          (unflatten n.eval n.eval (W.map (dec p)) i j) := by
  classical
  let k : Fin n.eval := ⟨pivot.eval, hk⟩
  choose Mw hMw hdMw using hM
  have hraw : Holds initial p R off.eval Mw := hMw
  have hR : R < initial.size := Store.lt_size_of_read_eq_some (hMw k k)
  have hMp : Holds st.store p R off.eval Mw := fun i j => by
    rw [hst, Store.read_push_of_lt hR]
    exact hMw i j
  obtain ⟨mid, ell, c, hr₁, hprep, hell, hc⟩ := exec_prepareSchur I h p st n R initial.size
    off pivot Mw hk hMp (Nat.ne_of_lt hR)
    (hst ▸ Store.getElem?_shape_push_size initial p (2 * n.eval + 1)) (by rwa [hdMw])
  have hMm : HoldsDecoded mid.store dec p R off.eval M := fun i j =>
    ⟨Mw i j, (hprep.frame p R _ (Nat.ne_of_lt hR)).trans (hMp i j), hdMw i j⟩
  obtain ⟨out, W, t, q, hWs, hr₂, hw₂, ht, hq⟩ := h.exec_ger I p mid n n
    ⟨initial.size, 2 * n⟩ initial.size 0 initial.size n R off (dec p c)
    (fun i => M i k) (M k) M (fun _ => ⟨c, by
      simpa only [IExp.eval_mul, IExp.eval_ofNat] using hprep.coeff, rfl⟩)
    (fun _ i => ⟨Mw i k, by
      simpa only [IExp.eval_zero, Nat.zero_add] using hprep.col i, hdMw i k⟩)
    (fun j => ⟨Mw k j, hprep.row j, hdMw k j⟩) hMm
    (by simp only [blockDisjoint_iff]; exact Or.inl (Nat.ne_of_gt hR))
    (by simp only [blockDisjoint_iff]; exact Or.inl (Nat.ne_of_gt hR))
    (by simp only [blockDisjoint_iff]; exact Or.inl (Nat.ne_of_gt hR))
  have hF : Store.BlockFrame st.store p initial.size R off.eval (n.eval * n.eval)
      mid.store (fun i => mid.store.read p R (off.eval + i)) :=
    ⟨hprep.shape, fun q b i hb _ => hprep.frame q b i hb, fun _ _ => rfl⟩
  have hF' := hF.writeBlock (off := 0) (by simpa only [Nat.add_zero] using hw₂)
    (by rw [Nat.zero_add, hWs])
  obtain ⟨goal, hgoal⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := initial) (xs := W) (by intro i hi; exact hraw.writable i (hWs ▸ hi))
  have hFout : Store.BlockFrame
      (initial.push (p, Array.replicate (2 * n.eval + 1) none)) p initial.size R off.eval
      (n.eval * n.eval) out.store (fun i => W[i]?) := by
    exact (hst ▸ hF').congr (fun i hi => by simp only [hWs, Nat.zero_le,
      Nat.zero_add, true_and, if_pos hi, Nat.sub_zero])
  have hpop : out.store.pop = goal := hFout.pop_eq hgoal hWs (fun _ _ => rfl)
  refine ⟨out, W, dec p ell, dec p c, t, q, ?_, hWs, hpop ▸ hgoal, hell, ?_, ht, hq⟩
  · rw [executionComposable_prepareSchur I p n R initial.size off pivot, hr₁, Option.bind_some]
    exact hr₂
  · simpa only [hdMw] using hc

end SchurRounding

/-- A nonzero decoded pivot suffices for the actual saved-pivot Schur update to succeed
in the standard model with every scalar result in range. The coefficient includes the error
of the literal minus one and division by the original pivot; the remaining witnesses follow
the actual `ger` instruction order. The scoped saved operands are released and the only net
store effect is one full packed matrix write. [Higham2002, §2.2; GolubVanLoan2013, §3.2]. -/
theorem IsRelErrSem.exec_schurStep {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : HoldsDecoded st.store dec p R off.eval M)
    (hp : M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩ ≠ 0) :
    ∃ (out : St P K C) (W : Array K) (ell c : ℝ) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
      exec I (schurStep p n R off pivot).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some out.store ∧
      RelErr (u p) (-1) ell ∧ RelErr (u p) (ell / M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c ∧
      (∀ j, RelErr (u p) (c * M ⟨pivot.eval, hk⟩ j) (t j)) ∧
      ∀ i j, RelErr (u p) (M i ⟨pivot.eval, hk⟩ * t j) (q i j) ∧
        RelErr (u p) (M i j + q i j)
          (unflatten n.eval n.eval (W.map (dec p)) i j) := by
  obtain ⟨out, hr, W, ell, c, t, q, hWs, hw, hell, hc, ht, hq⟩ := exists_exec_alloc I p
    (2 * n + 1) (fun work => (do
      prepareSchur p n R work off pivot
      ger p n n ⟨work, 2 * n⟩ work 0 work n R off).run) st
    (fun s => ∃ (W : Array K) (ell c : ℝ) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin n.eval) (Fin n.eval) ℝ),
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some s ∧
      RelErr (u p) (-1) ell ∧ RelErr (u p) (ell / M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) c ∧
      (∀ j, RelErr (u p) (c * M ⟨pivot.eval, hk⟩ j) (t j)) ∧
      ∀ i j, RelErr (u p) (M i ⟨pivot.eval, hk⟩ * t j) (q i j) ∧
        RelErr (u p) (M i j + q i j) (unflatten n.eval n.eval (W.map (dec p)) i j))
    (fun σ hσ => by
      obtain ⟨out, W, ell, c, t, q, hr, hs⟩ := SchurRounding.exec_schurBody I h p st.store
        σ n R off pivot M hk hM hp
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat] using hσ)
      exact ⟨out, hr, W, ell, c, t, q, hs⟩)
  refine ⟨out, W, ell, c, t, q, ?_, hWs, hw, hell, hc, ht, hq⟩
  change exec I (.seq (.alloc p (2 * n + 1) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The five actual local Schur instructions give a componentwise defect bound. The error on
an untouched entry is charged once, and the rank-one term is charged for the rounded literal,
division, two multiplications and final addition. The product estimate is
[Higham2002, Lemma 3.3; CarsonMaShao2026, Lemma 2]. -/
theorem abs_sub_schurUpdate_le_of_relErr {u a x y pivot ell c t q z : ℝ}
    (hu : u < 1) (hell : RelErr u (-1) ell) (hc : RelErr u (ell / pivot) c)
    (ht : RelErr u (c * y) t) (hq : RelErr u (x * t) q) (hz : RelErr u (a + q) z) :
    |z - (a - x * y / pivot)| ≤ u * |a| + roundingFactor 5 u * |x * y / pivot| := by
  obtain ⟨δ₀, hδ₀, he₀⟩ := hell
  obtain ⟨δ₁, hδ₁, he₁⟩ := hc
  obtain ⟨δ₂, hδ₂, he₂⟩ := ht
  obtain ⟨δ₃, hδ₃, he₃⟩ := hq
  obtain ⟨δ₄, hδ₄, he₄⟩ := hz
  let θ := (1 + δ₀) * (1 + δ₁) * (1 + δ₂) * (1 + δ₃) * (1 + δ₄) - 1
  have hθ : IsRoundingProduct u 5 θ := by
    convert ((((isRoundingProduct_one_of_abs_le hδ₀).mul
      (isRoundingProduct_one_of_abs_le hδ₁)).mul
      (isRoundingProduct_one_of_abs_le hδ₂)).mul
      (isRoundingProduct_one_of_abs_le hδ₃)).mul
      (isRoundingProduct_one_of_abs_le hδ₄) using 1
    dsimp [θ]
    ring
  have he : z - (a - x * y / pivot) = a * δ₄ - (x * y / pivot) * θ := by
    rw [he₄, he₃, he₂, he₁, he₀]
    dsimp [θ]
    ring
  calc
    |z - (a - x * y / pivot)| = |a * δ₄ - (x * y / pivot) * θ| := congrArg abs he
    _ ≤ |a * δ₄| + |(x * y / pivot) * θ| := abs_sub _ _
    _ = |a| * |δ₄| + |x * y / pivot| * |θ| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * u + |x * y / pivot| * roundingFactor 5 u :=
      add_le_add (mul_le_mul_of_nonneg_left hδ₄ (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hθ.abs_le hu) (abs_nonneg _))
    _ = u * |a| + roundingFactor 5 u * |x * y / pivot| := by ring

/-- The actual rounded saved-pivot update succeeds and differs entrywise from the exact
elimination step by the original-entry error and the five-factor rank-one error. No condition
on $5u_p$ is needed; $u_p<1$ suffices. The bound concerns one update, not the accumulated
factorization error. [Higham2002, §3.2; CarsonMaShao2026, Lemma 2]. -/
theorem IsRelErrSem.exec_schurStep_abs_sub_le {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : HoldsDecoded st.store dec p R off.eval M)
    (hp : M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩ ≠ 0) (hu : u p < 1) :
    ∃ (out : St P K C) (W : Array K),
      exec I (schurStep p n R off pivot).run st = some out ∧
      W.size = n.eval * n.eval ∧ st.store.writeBlock p R off.eval W = some out.store ∧
      ∀ i j, |unflatten n.eval n.eval (W.map (dec p)) i j -
        eliminationStep M ⟨pivot.eval, hk⟩ i j| ≤ u p * |M i j| +
          roundingFactor 5 (u p) *
            |M i ⟨pivot.eval, hk⟩ * M ⟨pivot.eval, hk⟩ j /
              M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩| := by
  obtain ⟨out, W, ell, c, t, q, hr, hWs, hw, hell, hc, ht, hq⟩ :=
    h.exec_schurStep I p st n R off pivot M hk hM hp
  refine ⟨out, W, hr, hWs, hw, fun i j => ?_⟩
  have hb := abs_sub_schurUpdate_le_of_relErr hu hell hc (ht j) (hq i j).1 (hq i j).2
  simpa only [eliminationStep_apply, div_eq_mul_inv, mul_comm] using hb

end NLAlib.Computation
