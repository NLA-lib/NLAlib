/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import NLAlib.Computation.BLAS.RoundingErrors

/-!
# Triangular solve

The kernel `NLAlib.Computation.trsvLower` (forward substitution in place) under exact arithmetic
and under an error contract. Every theorem asserts that the run succeeds under hypotheses on the
inputs alone: the stored diagonal is nonzero. Under the standard model the computed solution
solves a nearby triangular system exactly, with a componentwise relative perturbation of size
$\gamma_n = (1 - u)^{-n} - 1$ for $u < 1$ [Higham2002, Theorem 8.5], [CarsonMaShao2026].

## Main results

* `NLAlib.Computation.exec_trsvLower`: under exact arithmetic it computes
  $\mathbf{T}^{-1}\mathbf{b}$.
* `NLAlib.Computation.IsArithErrSem.exec_trsvLower`: the run lemma, for any error relation.
* `NLAlib.Computation.IsRelErrSem.exec_trsvLower_add_mulVec_eq`: backward error,
  [Higham2002, Theorem 8.5].
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

/-! ### The run of `trsvLower`, for any value semantics -/

namespace TrsvLower

variable {P ι K C : Type} [DecidableEq P]

/-- The counts of the first `i` rows: row `k` charges `k` multiplications and subtractions and
one division. -/
private def trsvCnt [AddMonoid C] (a b d : C) : ℕ → C
  | 0 => 0
  | i + 1 => trsvCnt a b d i + (i • (a + b) + d)

private theorem trsvCnt_eq {C : Type} [AddCommMonoid C] (a b d : C) (n : ℕ) :
    trsvCnt a b d n = (n * (n - 1) / 2) • (a + b) + n • d := by
  rw [← Finset.sum_range_id]
  induction n with
  | zero => simp [trsvCnt]
  | succ n ih =>
    rw [trsvCnt, ih, Finset.sum_range_succ, add_nsmul, succ_nsmul]
    abel

/-- The data of a run of `trsvLower` from the store `s₀` with the scratch buffer `Tb` pushed. -/
private structure Ctx (s₀ : Store P K) (p : P) (Tb A x n tOff xo : ℕ) (tw : ℕ → ℕ → K) :
    Prop where
  scratch : s₀.shape[Tb]? = some (p, 1)
  x_ne : 0 < n → x ≠ Tb
  x_shape : ∀ i < n, ∃ k, s₀.shape[x]? = some (p, k) ∧ xo + i < k
  T_read : ∀ i < n, ∀ j ≤ i, s₀.read p A (tOff + i + n * j) = some (tw i j)
  T_out : ∀ i < n, ∀ j ≤ i, A ≠ Tb ∧
    ¬(p = p ∧ A = x ∧ xo ≤ tOff + i + n * j ∧ tOff + i + n * j < xo + n)

variable [AddMonoid C] {I : Interp P ι K C} {s₀ : Store P K} {p : P} {Tb A x : ℕ}
  {n tOff xo : IExp ℕ} {tw : ℕ → ℕ → K}

/-- One step of row `i`: the product $t_{ij} x_j$ into the scratch cell, subtracted from
$x_i$. -/
private theorem exec_step (hC : Ctx s₀ p Tb A x n.eval tOff.eval xo.eval tw)
    {σ : St P K C} {c : ℕ → K} {i j : ℕ} (hi : i < n.eval) (hj : j < i)
    (h : Store.BlockFrame s₀ p Tb x xo.eval n.eval σ.store (fun m => some (c m)))
    {q v : K} (hq : I.sem.bin p .mul (tw i j) (c j) = some q)
    (hv : I.sem.bin p .sub (c i) q = some v) :
    ∃ s', exec I (.seq (.instr (.bin p .mul ⟨Tb, 0⟩ ⟨A, tOff + .var i + n * .var j⟩
        ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .sub ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩
          ⟨Tb, 0⟩)) .skip)) σ = some { σ with store := s', cnt := σ.cnt +
            (I.charge (.bin p .mul) + I.charge (.bin p .sub)) } ∧
      Store.BlockFrame s₀ p Tb x xo.eval n.eval s' (fun m => some (Function.update c i v m)) := by
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some q hC.scratch one_pos
  have h₁' := h.write_scratch (fun _ => hC.x_ne (by omega)) h₁
  obtain ⟨k, hxsh, hxlt⟩ := hC.x_shape i hi
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some v hxsh hxlt
  refine ⟨s₂, ?_, (h₁'.write_of_lt hi h₂).congr fun m _ => ?_⟩
  · obtain ⟨hAT, hAout⟩ := hC.T_out i hi j hj.le
    have hA : σ.store.read p A (tOff.eval + i + n.eval * j) = some (tw i j) :=
      (h.read_of_ne hAT hAout).trans (hC.T_read i hi j hj.le)
    have hx : σ.store.read p x (xo.eval + j) = some (c j) := h.2.2 j (by omega)
    have rw₁ : s₁.read p x (xo.eval + i) = some (c i) := h₁'.2.2 i hi
    simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
      IExp.eval_zero, hA, hx, hq, h₁, Option.bind_some, Option.map_some,
      Store.read_of_write_eq_some h₁, rw₁, hv, h₂]
    simp only [add_assoc]
  · by_cases hm : m = i
    · subst hm; simp
    · simp [Function.update_of_ne hm]

/-- The division that ends row `i`. -/
private theorem exec_div (hC : Ctx s₀ p Tb A x n.eval tOff.eval xo.eval tw)
    {σ : St P K C} {c : ℕ → K} {i : ℕ} (hi : i < n.eval)
    (h : Store.BlockFrame s₀ p Tb x xo.eval n.eval σ.store (fun m => some (c m)))
    {v : K} (hv : I.sem.bin p .div (c i) (tw i i) = some v) :
    ∃ s', exec I (.seq (.instr (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩
          ⟨A, tOff + .var i + n * .var i⟩)) .skip) σ =
        some { σ with store := s', cnt := σ.cnt + I.charge (.bin p .div) } ∧
      Store.BlockFrame s₀ p Tb x xo.eval n.eval s' (fun m => some (Function.update c i v m)) := by
  obtain ⟨k, hxsh, hxlt⟩ := hC.x_shape i hi
  obtain ⟨s₂, h₂⟩ := h.exists_write_eq_some v hxsh hxlt
  refine ⟨s₂, ?_, (h.write_of_lt hi h₂).congr fun m _ => ?_⟩
  · obtain ⟨hAT, hAout⟩ := hC.T_out i hi i le_rfl
    have hA : σ.store.read p A (tOff.eval + i + n.eval * i) = some (tw i i) :=
      (h.read_of_ne hAT hAout).trans (hC.T_read i hi i le_rfl)
    have hx : σ.store.read p x (xo.eval + i) = some (c i) := h.2.2 i hi
    simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
      hA, hx, hv, Option.bind_some, Option.map_some, h₂]
  · by_cases hm : m = i
    · subst hm; simp
    · simp [Function.update_of_ne hm]

/-- Row `i`: the inner loop, under a row invariant `R` that each step keeps. -/
private theorem exec_row (hC : Ctx s₀ p Tb A x n.eval tOff.eval xo.eval tw)
    {σ : St P K C} {c : ℕ → K} {i : ℕ} (hi : i < n.eval)
    (h : Store.BlockFrame s₀ p Tb x xo.eval n.eval σ.store (fun m => some (c m)))
    (R : ℕ → (ℕ → K) → Prop) (hR : R 0 c)
    (hmul : ∀ j < i, ∀ c, R j c → ∃ q v, I.sem.bin p .mul (tw i j) (c j) = some q ∧
      I.sem.bin p .sub (c i) q = some v ∧ R (j + 1) (Function.update c i v)) :
    ∃ σ', exec I (.loop (.var i) fun j =>
        .seq (.instr (.bin p .mul ⟨Tb, 0⟩ ⟨A, tOff + .var i + n * .var j⟩ ⟨x, xo + .var j⟩))
          (.seq (.instr (.bin p .sub ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨Tb, 0⟩)) .skip)) σ =
        some σ' ∧
      ∃ s' c', σ' = { σ with store := s', cnt := σ.cnt +
          i • (I.charge (.bin p .mul) + I.charge (.bin p .sub)) } ∧
        Store.BlockFrame s₀ p Tb x xo.eval n.eval s' (fun m => some (c' m)) ∧ R i c' ∧
        ∀ m ≠ i, c' m = c m := by
  refine exists_exec_loop_eq_some_of_forall I (n := .var i) (st := σ) (fun j σ' =>
    ∃ s' c', σ' = { σ with
      store := s', cnt := σ.cnt + j • (I.charge (.bin p .mul) + I.charge (.bin p .sub)) } ∧
      Store.BlockFrame s₀ p Tb x xo.eval n.eval s' (fun m => some (c' m)) ∧ R j c' ∧
      ∀ m ≠ i, c' m = c m) ⟨σ.store, c, by simp, h, hR, fun _ _ => rfl⟩ ?_
  rintro j hj σ' ⟨s, c', hσ, hF, hRj, hc'⟩
  replace hF : Store.BlockFrame s₀ p Tb x xo.eval n.eval σ'.store (fun m => some (c' m)) :=
    hσ ▸ hF
  obtain ⟨q, v, hq, hv, hR'⟩ := hmul j hj c' hRj
  obtain ⟨s'', hrun, hF'⟩ := exec_step hC hi hj hF hq hv
  refine ⟨_, hrun, s'', _, ?_, hF', hR', fun m hm => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · rw [Function.update_of_ne hm, hc' m hm]

/-- The rows: the outer loop, under a row-start invariant `G` and a row invariant `R`. -/
private theorem exec_rows (hC : Ctx s₀ p Tb A x n.eval tOff.eval xo.eval tw)
    {σ : St P K C} (xw : ℕ → K)
    (h : Store.BlockFrame s₀ p Tb x xo.eval n.eval σ.store (fun m => some (xw m)))
    (G : ℕ → (ℕ → K) → Prop) (R : ℕ → ℕ → (ℕ → K) → Prop) (h0 : G 0 xw)
    (hrow : ∀ i < n.eval, ∀ c, G i c → c i = xw i → R i 0 c)
    (hmul : ∀ i < n.eval, ∀ j < i, ∀ c, R i j c → ∃ q v,
      I.sem.bin p .mul (tw i j) (c j) = some q ∧ I.sem.bin p .sub (c i) q = some v ∧
        R i (j + 1) (Function.update c i v))
    (hdiv : ∀ i < n.eval, ∀ c, R i i c → ∃ v, I.sem.bin p .div (c i) (tw i i) = some v ∧
      G (i + 1) (Function.update c i v)) :
    ∃ σ', exec I (.loop n fun i => .seq (.loop (.var i) fun j =>
        .seq (.instr (.bin p .mul ⟨Tb, 0⟩ ⟨A, tOff + .var i + n * .var j⟩ ⟨x, xo + .var j⟩))
          (.seq (.instr (.bin p .sub ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ ⟨Tb, 0⟩)) .skip))
        (.seq (.instr (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩
          ⟨A, tOff + .var i + n * .var i⟩)) .skip)) σ = some σ' ∧
      ∃ s' c, σ' = { σ with store := s', cnt := σ.cnt +
          (trsvCnt (I.charge (.bin p .mul)) (I.charge (.bin p .sub)) (I.charge (.bin p .div))
            n.eval) } ∧
        Store.BlockFrame s₀ p Tb x xo.eval n.eval s' (fun m => some (c m)) ∧ G n.eval c := by
  refine (exists_exec_loop_eq_some_of_forall I (st := σ) (fun i σ' => ∃ s' c, σ' = { σ with
      store := s', cnt := σ.cnt +
        (trsvCnt (I.charge (.bin p .mul)) (I.charge (.bin p .sub)) (I.charge (.bin p .div))
          i) } ∧
      Store.BlockFrame s₀ p Tb x xo.eval n.eval s' (fun m => some (c m)) ∧ G i c ∧
      ∀ m, i ≤ m → c m = xw m) ⟨σ.store, xw, by simp [trsvCnt], h, h0, fun _ _ => rfl⟩ ?_).imp
    fun σ' ⟨hrun, s', c, hσ, hF, hG, _⟩ => ⟨hrun, s', c, hσ, hF, hG⟩
  rintro i hi σ' ⟨s, c, hσ, hF, hG, hrest⟩
  replace hF : Store.BlockFrame s₀ p Tb x xo.eval n.eval σ'.store (fun m => some (c m)) :=
    hσ ▸ hF
  obtain ⟨σ₁, h₁, s₁, c₁, rfl, hF₁, hR₁, hc₁⟩ :=
    exec_row hC hi hF (R i) (hrow i hi c hG (hrest i le_rfl)) (hmul i hi)
  obtain ⟨v, hv, hG'⟩ := hdiv i hi c₁ hR₁
  obtain ⟨s₂, h₂, hF₂⟩ := exec_div (σ := { σ' with store := s₁, cnt := σ'.cnt +
    i • (I.charge (.bin p .mul) + I.charge (.bin p .sub)) }) hC hi hF₁ hv
  refine ⟨_, by rw [exec_seq, h₁, Option.bind_some, h₂], s₂, _, ?_, hF₂, hG', fun m hm => ?_⟩
  · subst hσ
    simp only [trsvCnt, add_assoc]
  · rw [Function.update_of_ne (by omega), hc₁ m (by omega), hrest m (by omega)]

/-- **The run of `trsvLower`, for any value semantics**: with the words $t_{ij}$ ($j \le i < n$)
and $x_i$ stored, and the cells of $\mathbf{x}$ outside the block of $\mathbf{T}$, the run
succeeds when every operation does, under invariants `G` (at the start of each row) and `R`
(within a row), and writes the final words into $\mathbf{x}$. -/
private theorem exec_core (I : Interp P ι K C) (p : P) (st : St P K C) (n : IExp ℕ) (T : ℕ)
    (tOff : IExp ℕ) (x : ℕ) (xo : IExp ℕ) (tw : ℕ → ℕ → K) (xw : ℕ → K)
    (hT : ∀ i < n.eval, ∀ j ≤ i,
      st.store.read p T (tOff.eval + i + n.eval * j) = some (tw i j))
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xw i))
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval)
    (G : ℕ → (ℕ → K) → Prop) (R : ℕ → ℕ → (ℕ → K) → Prop) (h0 : G 0 xw)
    (hrow : ∀ i < n.eval, ∀ c, G i c → c i = xw i → R i 0 c)
    (hmul : ∀ i < n.eval, ∀ j < i, ∀ c, R i j c → ∃ q v,
      I.sem.bin p .mul (tw i j) (c j) = some q ∧ I.sem.bin p .sub (c i) q = some v ∧
        R i (j + 1) (Function.update c i v))
    (hdiv : ∀ i < n.eval, ∀ c, R i i c → ∃ v, I.sem.bin p .div (c i) (tw i i) = some v ∧
      G (i + 1) (Function.update c i v)) :
    ∃ st' c, exec I (trsvLower p n T tOff x xo).run st = some st' ∧ G n.eval c ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map c) = some st'.store ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + trsvCnt (I.charge (.bin p .mul)) (I.charge (.bin p .sub))
        (I.charge (.bin p .div)) n.eval ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  have hxlt : 0 < n.eval → x < st.store.size := fun h => Store.lt_size_of_read_eq_some (hx 0 h)
  have hC : Ctx (st.store.push (p, Array.replicate (1 : IExp ℕ).eval none)) p st.store.size T x
      n.eval tOff.eval xo.eval tw :=
    { scratch := Store.getElem?_shape_push_size _ _ _
      x_ne := fun h => Nat.ne_of_lt (hxlt h)
      x_shape := fun i hi => by
        rw [Store.getElem?_shape_push_of_lt _ (hxlt (by omega))]
        exact Store.exists_getElem?_shape_of_read_eq_some (hx i hi)
      T_read := fun i hi j hj => by
        rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hT i hi j hj))]
        exact hT i hi j hj
      T_out := fun i hi j hj => by
        have hlt : i + n.eval * j < n.eval * n.eval :=
          Nat.add_mul_lt_mul_of_lt_of_lt hi (by omega)
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hT i hi j hj)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hxT rfl with h | h <;> omega }
  have hbase : Store.BlockFrame st.store p st.store.size x xo.eval n.eval st.store
      (fun m => some (xw m)) := ⟨rfl, fun _ _ _ _ _ => rfl, fun m hm => hx m hm⟩
  rw [run_trsvLower, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  obtain ⟨σF, hF, sF, cF, rfl, hIF, hG⟩ := exec_rows hC
    (σ := { st with
      store := st.store.push (p, Array.replicate (1 : IExp ℕ).eval none)
      cur := Function.update st.cur p (st.cur p + (1 : IExp ℕ).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (1 : IExp ℕ).eval))
      curW := st.curW + (1 : IExp ℕ).eval * I.width p
      peakW := max st.peakW (st.curW + (1 : IExp ℕ).eval * I.width p) })
    xw (hbase.push _ hxlt) G R h0 hrow hmul hdiv
  rw [hF, Option.map_some]
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some (s := st.store) (p := p) (b := x)
    (off := xo.eval) (xs := (List.range n.eval).toArray.map cF)
    fun j hj => ⟨xw j, hx j (by simpa using hj)⟩
  refine ⟨_, cF, rfl, hG, ?_, rfl, ?_, ?_, rfl, ?_, ?_⟩
  · rw [hs₁]
    exact congrArg some (hIF.pop_eq hs₁ (by simp) fun m hm => by simp [hm]).symm
  · funext q
    by_cases hq : q = p <;> simp [hq]
  · simp
  · simp
  · simp

/-- A partial row trace reads $x_j$ only for $j < k$. -/
private theorem rowTrace_congr {err : BinOp → ℝ → ℝ → Prop} {t : ℕ → ℕ → ℝ} {b xv xv' : ℕ → ℝ}
    {i k : ℕ} {s : ℕ → ℝ} (h : IsSubstRowTrace err t b xv i k s)
    (hx : ∀ j < k, xv j = xv' j) : IsSubstRowTrace err t b xv' i k s :=
  ⟨h.1, fun j hj => by rw [← hx j hj]; exact h.2 j hj⟩

/-- A trace of the first $i$ rows reads $x_j$ only for $j < i$. -/
private theorem trace_congr {err : BinOp → ℝ → ℝ → Prop} {t : ℕ → ℕ → ℝ} {b xv xv' : ℕ → ℝ}
    {i : ℕ} (h : IsSubstTrace err t b i xv) (hx : ∀ j < i, xv j = xv' j) :
    IsSubstTrace err t b i xv' := fun i' hi' =>
  let ⟨s, hs, hd⟩ := h i' hi'
  ⟨s, rowTrace_congr hs fun j hj => hx j (by omega), by rw [← hx i' hi']; exact hd⟩

end TrsvLower

/-- **`trsvLower` solves a lower triangular system** under exact arithmetic: if buffer $T$ holds
the lower triangular part of the lower triangular $n \times n$ matrix $\mathbf{T}$ from
$\mathit{tOff}$ (column-major; the cells above the diagonal need not hold anything), with
nonzero diagonal, the cells of $\mathbf{x}$ hold $\mathbf{b}$, and they lie outside the block of
$\mathbf{T}$, the run writes $\mathbf{T}^{-1}\mathbf{b}$ into the cells of $\mathbf{x}$ and
nothing else, keeps the tape and the current memory, raises the peak by one cell, and counts
$n(n-1)/2$ multiplications and subtractions and $n$ divisions. The operation is in
[GolubVanLoan2013, §3.1]. -/
theorem exec_trsvLower {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]
    (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (p : P) (st : St P 𝕜 (OpCount P ι))
    (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) 𝕜) (hM : M.BlockTriangular OrderDual.toDual)
    (hdiag : ∀ i, M i i ≠ 0) (b : Fin n.eval → 𝕜)
    (hT : ∀ i j : Fin n.eval, j ≤ i →
      st.store.read p T (tOff.eval + i + n.eval * j) = some (M i j))
    (hx : ∀ i : Fin n.eval, st.store.read p x (xo.eval + i) = some (b i))
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval)
    (s₁ : Store P 𝕜) (h₁ : st.store.writeBlock p x xo.eval (Array.ofFn (M⁻¹ *ᵥ b)) = some s₁) :
    ∃ st', exec I (trsvLower p n T tOff x xo).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + ((n.eval * (n.eval - 1) / 2) • (Finsupp.single (.bin p .mul) 1 +
        Finsupp.single (.bin p .sub) 1) + n.eval • Finsupp.single (.bin p .div) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  classical
  have hlow : ∀ i j : Fin n.eval, i < j → M i j = 0 := fun i j h =>
    hM (OrderDual.toDual_lt_toDual.mpr h)
  set v := M⁻¹ *ᵥ b with hv
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_isLowerTriangular M hM]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)
  have hMv : M *ᵥ v = b := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]
  set W : ℕ → 𝕜 := fun i => if h : i < n.eval then v ⟨i, h⟩ else 0 with hW
  set tw : ℕ → ℕ → 𝕜 := fun i j => if h : i < n.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩
    else 0 with htw
  set xw : ℕ → 𝕜 := fun i => if h : i < n.eval then b ⟨i, h⟩ else 0 with hxw
  have htii : ∀ i < n.eval, tw i i ≠ 0 := fun i hi => by simpa [htw, hi] using hdiag ⟨i, hi⟩
  have key : ∀ i < n.eval, (xw i - ∑ j ∈ range i, tw i j * W j) / tw i i = W i := by
    intro i hi
    have hrow := congrFun hMv ⟨i, hi⟩
    simp only [Matrix.mulVec, dotProduct] at hrow
    have h₁ : ∑ j : Fin n.eval, M ⟨i, hi⟩ j * v j = ∑ j ∈ range n.eval, tw i j * W j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => tw i j * W j)]
      exact Finset.sum_congr rfl fun j _ => by simp [htw, hW, hi, j.2]
    have h₂ : ∑ j ∈ range n.eval, tw i j * W j = ∑ j ∈ range (i + 1), tw i j * W j := by
      refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j hj hj' => ?_).symm
      simp only [Finset.mem_range] at hj hj'
      have : M ⟨i, hi⟩ ⟨j, hj⟩ = 0 := hlow _ _ (Fin.mk_lt_mk.mpr (by omega))
      simp [htw, hi, hj, this]
    rw [h₁, h₂, Finset.sum_range_succ] at hrow
    rw [div_eq_iff (htii i hi)]
    have hb : xw i = b ⟨i, hi⟩ := by simp [hxw, hi]
    rw [hb, ← hrow]
    ring
  obtain ⟨st', c, hrun, hG, hwb, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    TrsvLower.exec_core I p st n T tOff x xo tw xw
      (fun i hi j hj => by
        simpa [htw, hi, show j < n.eval by omega] using
          hT ⟨i, hi⟩ ⟨j, by omega⟩ (Fin.mk_le_mk.mpr hj))
      (fun i hi => by simpa [hxw, hi] using hx ⟨i, hi⟩) hxT
      (fun i c => ∀ m < i, c m = W m)
      (fun i k c => (∀ m < i, c m = W m) ∧ c i = xw i - ∑ j ∈ range k, tw i j * W j)
      (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun i _ c hG hc => ⟨hG, by simp [hc]⟩)
      (fun i _ j hj c ⟨hG, hci⟩ => ⟨tw i j * c j, c i - tw i j * c j, by rw [hI]; rfl,
        by rw [hI]; rfl, ⟨fun m hm => by rw [Function.update_of_ne (by omega), hG m hm],
          by rw [Function.update_self, hci, hG j hj, Finset.sum_range_succ]; ring⟩⟩)
      (fun i hi c ⟨hG, hci⟩ => ⟨c i / tw i i, by rw [hI]; simp [exactSem, htii i hi],
        fun m hm => by
          by_cases hmi : m = i
          · subst hmi
            rw [Function.update_self, hci, key m hi]
          · rw [Function.update_of_ne hmi, hG m (by omega)]⟩)
  refine ⟨st', hrun, ?_, hpos, hcur, hcurW, ?_, hpeak, hpeakW⟩
  · have hA : (List.range n.eval).toArray.map c = Array.ofFn v :=
      Array.ext (by simp) fun k hk₁ _ => by
        have hk : k < n.eval := by simpa using hk₁
        simp [hG k hk, hW, hk]
    rw [hA, h₁] at hwb
    exact (Option.some.inj hwb).symm
  · rw [hcnt, TrsvLower.trsvCnt_eq, hc.charge_eq]

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C) {dec : P → K → ℝ}

/-- **The run of `trsvLower` under an error contract**: if buffer $T$ holds words decoding to
$t_{ij}$ ($i, j < n$, column-major from $\mathit{tOff}$) with $t_{ii} \ne 0$, the cells of
$\mathbf{x}$ hold words decoding to $b_i$ and lie outside the block of $\mathbf{T}$, and on
every trace prefix the next product, difference and quotient are in range, then the run
succeeds, writes words $w_i$ into the cells of $\mathbf{x}$ and nothing else, and the decoded
$w_i$ form a trace of forward substitution under `err`. [Higham2002, Lemma 8.4], for the order
of operations of `trsvLower`. -/
theorem IsArithErrSem.exec_trsvLower {err : P → BinOp → ℝ → ℝ → Prop} {safe : P → ℝ → Prop}
    (h : IsArithErrSem err dec safe I.sem) (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ) (x : ℕ)
    (xo : IExp ℕ) (tv : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hT : ∀ i < n.eval, ∀ j ≤ i, ∃ w,
      st.store.read p T (tOff.eval + i + n.eval * j) = some w ∧ dec p w = tv i j)
    (hdiag : ∀ i < n.eval, tv i i ≠ 0)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = b i)
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval)
    (hsafe : ∀ i < n.eval, ∀ xv : ℕ → ℝ, IsSubstTrace (err p) tv b i xv →
      (∀ k < i, ∀ s : ℕ → ℝ, IsSubstRowTrace (err p) tv b xv i k s →
        safe p (tv i k * xv k) ∧ ∀ q, err p .mul (tv i k * xv k) q → safe p (s k - q)) ∧
      ∀ s : ℕ → ℝ, IsSubstRowTrace (err p) tv b xv i i s → safe p (s i / tv i i)) :
    ∃ st', ∃ W : ℕ → K, exec I (trsvLower p n T tOff x xo).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      IsSubstTrace (err p) tv b n.eval (fun i => dec p (W i)) := by
  classical
  have : Inhabited K := ⟨(h.lit_zero p).choose⟩
  have hT' : ∀ i j, ∃ w : K, i < n.eval → j ≤ i →
      st.store.read p T (tOff.eval + i + n.eval * j) = some w ∧ dec p w = tv i j := fun i j => by
    by_cases hij : i < n.eval ∧ j ≤ i
    · obtain ⟨w, hw⟩ := hT i hij.1 j hij.2
      exact ⟨w, fun _ _ => hw⟩
    · exact ⟨default, fun hi hj => absurd ⟨hi, hj⟩ hij⟩
  choose tw htw using hT'
  have hx' : ∀ i, ∃ w : K, i < n.eval →
      st.store.read p x (xo.eval + i) = some w ∧ dec p w = b i := fun i => by
    by_cases hi : i < n.eval
    · obtain ⟨w, hw⟩ := hx i hi
      exact ⟨w, fun _ => hw⟩
    · exact ⟨default, fun h => absurd h hi⟩
  choose xw hxw using hx'
  obtain ⟨st', c, hrun, hG, hwb, -⟩ := TrsvLower.exec_core I p st n T tOff x xo tw xw
    (fun i hi j hj => (htw i j hi hj).1) (fun i hi => (hxw i hi).1) hxT
    (fun i c => IsSubstTrace (err p) tv b i (fun m => dec p (c m)))
    (fun i k c => IsSubstTrace (err p) tv b i (fun m => dec p (c m)) ∧
      ∃ s, IsSubstRowTrace (err p) tv b (fun m => dec p (c m)) i k s ∧ s k = dec p (c i))
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i hi c hG hc => ⟨hG, fun _ => b i, ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
      by rw [hc]; exact (hxw i hi).2.symm⟩)
    (fun i hi j hj c ⟨hG, s, hs, hsj⟩ => by
      obtain ⟨hsafe₁, -⟩ := hsafe i hi _ hG
      obtain ⟨hm, hsub⟩ := hsafe₁ j hj s hs
      have htij := (htw i j hi hj.le).2
      obtain ⟨q, hq⟩ := h.bin_ok p .mul (tw i j) (c j) trivial (by intro h; cases h)
        (by simpa [BinOp.realOp, htij] using hm)
      have hqe : err p .mul (tv i j * dec p (c j)) (dec p q) := by
        simpa [BinOp.realOp, htij] using h.bin_err p .mul _ _ _ trivial hq
      obtain ⟨v, hv⟩ := h.bin_ok p .sub (c i) q trivial (by intro h; cases h)
        (by simpa [BinOp.realOp, hsj] using hsub _ hqe)
      have hve : err p .sub (s j - dec p q) (dec p v) := by
        simpa [BinOp.realOp, hsj] using h.bin_err p .sub _ _ _ trivial hv
      refine ⟨q, v, hq, hv, TrsvLower.trace_congr hG fun m hm => ?_,
        Function.update s (j + 1) (dec p v),
        ⟨by rw [Function.update_of_ne (by omega : 0 ≠ j + 1)]; exact hs.1, fun j' hj' => ?_⟩,
        by simp⟩
      · rw [Function.update_of_ne (by omega : m ≠ i)]
      · dsimp only
        rw [Function.update_of_ne (by omega : j' ≠ i),
          Function.update_of_ne (by omega : j' ≠ j + 1)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | rfl
        · rw [Function.update_of_ne (by omega : j' + 1 ≠ j + 1)]
          exact hs.2 j' hlt
        · rw [Function.update_self]
          exact ⟨_, hqe, hve⟩)
    (fun i hi c ⟨hG, s, hs, hsi⟩ => by
      obtain ⟨-, hd⟩ := hsafe i hi _ hG
      have htii := (htw i i hi le_rfl).2
      obtain ⟨v, hv⟩ := h.bin_ok p .div (c i) (tw i i) trivial
        (fun _ => by rw [htii]; exact hdiag i hi) (by simpa [BinOp.realOp, htii, hsi] using hd s hs)
      have hve : err p .div (s i / tv i i) (dec p v) := by
        simpa [BinOp.realOp, htii, hsi] using h.bin_err p .div _ _ _ trivial hv
      refine ⟨v, hv, fun i' hi' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
      · refine TrsvLower.trace_congr hG (fun m hm => ?_) i' hlt
        rw [Function.update_of_ne (by omega : m ≠ i)]
      · refine ⟨s, TrsvLower.rowTrace_congr hs fun m hm => ?_, ?_⟩
        · rw [Function.update_of_ne (by omega : m ≠ i')]
        · dsimp only
          rw [Function.update_self]
          exact hve)
  exact ⟨st', c, hrun, hwb, hG⟩

/-- **Backward error of triangular solve** in the standard model
[Higham2002, Theorem 8.5], with the factor of [CarsonMaShao2026, (3)]: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range and $u_p < 1$, if buffer $T$ holds the
lower triangular part of the real lower triangular $n \times n$ matrix $\mathbf{T}$ through the
decoding (column-major from $\mathit{tOff}$; the cells above the diagonal need not hold anything)
with nonzero diagonal, and the cells of $\mathbf{x}$ hold words decoding to $\mathbf{b}$ and lie
outside the block of $\mathbf{T}$, the run of `trsvLower` succeeds, writes words $w_i$ into the
cells of $\mathbf{x}$ and nothing else, and the decoded $\hat{\mathbf{x}}$ solves a nearby system
exactly: for some $\Delta\mathbf{T}$ with
$\lvert \Delta t_{ij} \rvert \le \gamma_n \lvert t_{ij} \rvert$,
$\gamma_n = (1 - u_p)^{-n} - 1$,
$$(\mathbf{T} + \Delta\mathbf{T})\,\hat{\mathbf{x}} = \mathbf{b}\,.$$
Then $\Delta\mathbf{T}$ is lower triangular too. -/
theorem IsRelErrSem.exec_trsvLower_add_mulVec_eq {u : P → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (n : IExp ℕ) (T : ℕ) (tOff : IExp ℕ)
    (x : ℕ) (xo : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : M.BlockTriangular OrderDual.toDual) (hdiag : ∀ i, M i i ≠ 0) (b : Fin n.eval → ℝ)
    (hu1 : u p < 1)
    (hT : ∀ i j : Fin n.eval, j ≤ i → ∃ w,
      st.store.read p T (tOff.eval + i + n.eval * j) = some w ∧ dec p w = M i j)
    (hx : ∀ i : Fin n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = b i)
    (hxT : x = T → xo.eval + n.eval ≤ tOff.eval ∨ tOff.eval + n.eval * n.eval ≤ xo.eval) :
    ∃ st', ∃ W : ℕ → K, exec I (trsvLower p n T tOff x xo).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∃ ΔT : Matrix (Fin n.eval) (Fin n.eval) ℝ,
        (∀ i j, |ΔT i j| ≤ roundingFactor n.eval (u p) * |M i j|) ∧
        (M + ΔT) *ᵥ (fun i => dec p (W i)) = b := by
  classical
  have hlow : ∀ i j : Fin n.eval, i < j → M i j = 0 := fun i j h =>
    hM (OrderDual.toDual_lt_toDual.mpr h)
  set tv : ℕ → ℕ → ℝ := fun i j => if h : i < n.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩
    else 0 with htv
  set bv : ℕ → ℝ := fun i => if h : i < n.eval then b ⟨i, h⟩ else 0 with hbv
  have htd : ∀ i < n.eval, tv i i ≠ 0 := fun i hi => by simpa [htv, hi] using hdiag ⟨i, hi⟩
  obtain ⟨st', W, hrun, hwb, htr⟩ := (h.isArithErrSem fun _ => trivial).exec_trsvLower I p st n
    T tOff x xo tv bv
    (fun i hi j hj => by
      simpa [htv, hi, show j < n.eval by omega] using
        hT ⟨i, hi⟩ ⟨j, by omega⟩ (Fin.mk_le_mk.mpr hj))
    htd (fun i hi => by simpa [hbv, hi] using hx ⟨i, hi⟩) hxT
    (fun _ _ _ _ => ⟨fun _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩, fun _ _ => trivial⟩)
  obtain ⟨Δ, hΔ, hsum⟩ :=
    htr.exists_sum_add_mul_eq htd (h.nonneg trivial) hu1
  refine ⟨st', W, hrun, hwb, fun i j => if (j : ℕ) ≤ i then Δ i j else 0, fun i j => ?_, ?_⟩
  · dsimp only
    split_ifs with hji
    · simpa [htv] using hΔ i i.2 j hji
    · simp [hlow i j (Fin.lt_def.mpr (by omega))]
  · funext i
    set G : ℕ → ℝ := fun j => (tv i j + if j ≤ i then Δ i j else 0) * dec p (W j) with hG
    have h₁ : ∑ j : Fin n.eval, (M i j + if (j : ℕ) ≤ i then Δ i j else 0) * dec p (W j) =
        ∑ j ∈ range n.eval, G j := by
      rw [← Fin.sum_univ_eq_sum_range G]
      exact Finset.sum_congr rfl fun j _ => by simp [hG, htv, i.2, j.2]
    have h₂ : ∑ j ∈ range n.eval, G j =
        ∑ j ∈ range (i + 1), (tv i j + Δ i j) * dec p (W j) := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : (i : ℕ) + 1 ≤ n.eval))
        fun j hj hj' => ?_]
      · exact Finset.sum_congr rfl fun j hj => by
          simp only [Finset.mem_range] at hj
          simp [hG, show j ≤ (i : ℕ) by omega]
      · simp only [Finset.mem_range] at hj hj'
        have : M i ⟨j, hj⟩ = 0 := hlow _ _ (Fin.lt_def.mpr (by simp; omega))
        simp [hG, htv, i.2, hj, this, show ¬ j ≤ (i : ℕ) by omega]
    exact (h₁.trans (h₂.trans (hsum i i.2))).trans (by simp [hbv, i.2])

end NLAlib.Computation
