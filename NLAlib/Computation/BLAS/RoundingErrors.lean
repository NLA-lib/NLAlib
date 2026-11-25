/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Contract
public import NLAlib.Computation.BLAS.Traces
public import NLAlib.Computation.BLAS.ReciprocalScaling

/-!
# Rounding errors of the BLAS kernels

Error analyses of the library's own `dot`, `axpy`, `gemv` and `gemm` programs, in the order of
operations they execute, against an error contract on the value semantics. Every theorem
asserts that the run **succeeds**, under hypotheses on the inputs alone, and bounds the decoded
result.

Two layers. The **run lemmas** (`NLAlib.Computation.IsArithErrSem.exec_dot`, …) hold for any
error relation `err` and range condition `safe`: the run succeeds and produces a trace
(`NLAlib.Computation.IsDotTrace`), provided every operation on every trace prefix is in range.
The **standard-model theorems** (`NLAlib.Computation.IsRelErrSem.exec_dot_eq_sum_mul_one_add`,
…) take the contract `NLAlib.Computation.IsRelErrSem` with every value in range
($\mathrm{safe} = \mathrm{True}$, underflow and overflow ignored as in [Higham2002, §2.2]), where
the range hypothesis is void, and bound the trace by `NLAlib/Computation/BLAS/Traces.lean`.
The factor is $\gamma_n = (1 - u_p)^{-n} - 1$ of [CarsonMaShao2026], under $u_p < 1$ alone. A
model with underflow and overflow reuses the run lemmas and discharges their range hypothesis
from explicit bounds on the data.

Decoded values are real: the kernels are analysed over real data.

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_dot`, `NLAlib.Computation.IsArithErrSem.exec_axpy`,
  `NLAlib.Computation.IsArithErrSem.exec_gemv`, `NLAlib.Computation.IsArithErrSem.exec_gemm`:
  the run lemmas.
* `NLAlib.Computation.IsRelErrSem.exec_dot_eq_sum_mul_one_add`,
  `NLAlib.Computation.IsRelErrSem.exec_dot_abs_sum_mul_sub_le`,
  `NLAlib.Computation.IsRelErrSem.exec_dot_eq_sum_mul_one_add_isRoundingProduct`: `dot`,
  [Higham2002, §3.1].
* `NLAlib.Computation.IsRelErrSem.exec_axpy`: `axpy`.
* `NLAlib.Computation.IsRelErrSem.exec_rscl`: `rscl`.
* `NLAlib.Computation.IsRelErrSem.exec_gemv_eq_add_mulVec`,
  `NLAlib.Computation.IsRelErrSem.exec_gemv_abs_mulVec_sub_le`: `gemv`, [Higham2002, §3.5].
* `NLAlib.Computation.IsRelErrSem.exec_gemm_abs_mul_sub_le`: `gemm`, [Higham2002, §3.5].
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P)
  (st : St P K C) {dec : P → K → ℝ}

/-! ### Helpers -/

section Helpers

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Reordering the witnesses of a successful run with two more. -/
private theorem exists₃_of {β W S : Type} {o : Option β} {Q : β → W → S → Prop}
    (h : ∃ b, o = some b ∧ ∃ w s, Q b w s) : ∃ b w s, o = some b ∧ Q b w s :=
  let ⟨b, hb, w, s, hQ⟩ := h; ⟨b, w, s, hb, hQ⟩

/-- Reordering the witnesses of a successful run with one more. -/
private theorem exists₂_of {β W : Type} {o : Option β} {Q : β → W → Prop}
    (h : ∃ b, o = some b ∧ ∃ w, Q b w) : ∃ b w, o = some b ∧ Q b w :=
  let ⟨b, hb, w, hQ⟩ := h; ⟨b, w, hb, hQ⟩

/-- The writes of a fold depend only on the values at the indices of the list. -/
private theorem foldlM_write_congr {s : Store P K} {p : P} {b : ℕ} {idx : ℕ → ℕ} {f g : ℕ → K}
    (l : List ℕ) (h : ∀ j ∈ l, f j = g j) :
    l.foldlM (fun s j => s.write p b (idx j) (f j)) s =
      l.foldlM (fun s j => s.write p b (idx j) (g j)) s := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldlM_cons, List.foldlM_cons, h i List.mem_cons_self]
    exact congrArg _ (funext fun s => ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

/-- Extending a trace of recursive accumulation by one step. -/
private theorem IsDotTrace.update {err : BinOp → ℝ → ℝ → Prop} {x y s : ℕ → ℝ} {k : ℕ}
    {q v : ℝ} (h : IsDotTrace err x y k s) (hq : err .mul (x k * y k) q)
    (hv : err .add (s k + q) v) (h0 : s k = 0 → v = q) :
    IsDotTrace err x y (k + 1) (Function.update s (k + 1) v) := by
  refine ⟨by rw [Function.update_of_ne (by omega)]; exact h.1, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · obtain ⟨q', h1, h2, h3⟩ := h.2 j hj
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact ⟨q', h1, h2, h3⟩
  · rw [Function.update_of_ne (by omega), Function.update_self]
    exact ⟨q, hq, hv, h0⟩

variable (I : Interp P ι K C) (p : P) {dec : P → K → ℝ} {err : P → BinOp → ℝ → ℝ → Prop}
  {safe : P → ℝ → Prop}

/-- One step of `dot` under an error contract, from a store with the word `w` written into
`dst` and a scratch buffer pushed. -/
private theorem exec_dot_step_err (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) {s si : Store P K} {dst : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ}
    {y : ℕ} {yo : IExp ℕ} {t i : ℕ} {wx wy w : K} {st' : St P K C} {arr : Array (Option K)}
    (hx : s.read p x (xo.eval + i) = some wx) (hy : s.read p y (yo.eval + i) = some wy)
    (hdx : dst.buf = x → dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → dst.idx.eval ≠ yo.eval + i) (ht : s.size = t)
    (hsi : s.write p dst.buf dst.idx.eval w = some si) (harr : arr.size = 1)
    (hst : st'.store = si.push (p, arr)) (hs₁ : safe p (dec p wx * dec p wy))
    (hs₂ : ∀ q, err p .mul (dec p wx * dec p wy) q → safe p (dec p w + q)) :
    ∃ (arr' : Array (Option K)) (w' : K) (si' : Store P K) (q : ℝ), arr'.size = 1 ∧
      s.write p dst.buf dst.idx.eval w' = some si' ∧
      exec I (.seq (.instr (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩))
        (.seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩))
          (.seq (.instr (.bin p .add dst dst ⟨t, 0⟩)) .skip))) st' =
        some { st' with
          store := si'.push (p, arr')
          cnt := st'.cnt + I.charge (.un p .conj) + I.charge (.bin p .mul) +
            I.charge (.bin p .add) } ∧
      err p .mul (dec p wx * dec p wy) q ∧ err p .add (dec p w + q) (dec p w') ∧
      (dec p w = 0 → dec p w' = q) := by
  have hsz : si.size = t := by rw [← ht, Store.size_of_write_eq_some hsi]
  have hlt : ∀ {b j : ℕ} {v : K}, s.read p b j = some v → b < si.size := fun h => by
    rw [Store.size_of_write_eq_some hsi]; exact Store.lt_size_of_read_eq_some h
  have hdlt : dst.buf < si.size := by
    rw [Store.size_of_write_eq_some hsi]; exact Store.lt_size_of_write_eq_some hsi
  have r1 : ∀ arr' : Array (Option K), Store.read (si.push (p, arr')) p x (xo.eval + i) =
      some wx := by
    intro arr'
    rw [Store.read_push_of_lt (hlt hx), Store.read_of_write_eq_some_of_ne hsi, hx]
    by_cases h : x = dst.buf
    · exact Or.inr fun he => hdx h.symm he.symm
    · exact Or.inl h
  have r3 : ∀ arr' : Array (Option K), Store.read (si.push (p, arr')) p y (yo.eval + i) =
      some wy := by
    intro arr'
    rw [Store.read_push_of_lt (hlt hy), Store.read_of_write_eq_some_of_ne hsi, hy]
    by_cases h : y = dst.buf
    · exact Or.inr fun he => hdy h.symm he.symm
    · exact Or.inl h
  obtain ⟨zc, hzc, hdc⟩ := h.conj p wx
  obtain ⟨zq, hzq⟩ := h.bin_ok p .mul zc wy trivial (fun h => nomatch h)
    (by rw [hdc]; exact hs₁)
  have hq : err p .mul (dec p wx * dec p wy) (dec p zq) := by
    have := h.bin_err p .mul zc wy zq trivial hzq
    rwa [hdc] at this
  obtain ⟨zn, hzn⟩ := h.bin_ok p .add w zq trivial (fun h => nomatch h) (hs₂ _ hq)
  have hn : err p .add (dec p w + dec p zq) (dec p zn) := h.bin_err p .add w zq zn trivial hzn
  obtain ⟨si', hsi'⟩ := Store.exists_write_eq_some_of_write_eq_some hsi zn
  set a₁ := arr.set! 0 (some zc)
  set a₂ := a₁.set! 0 (some zq)
  have h₁ : 0 < a₁.size := by simp [a₁, harr]
  have w3 : Store.write (si.push (p, a₂)) p dst.buf dst.idx.eval zn =
      some (si'.push (p, a₂)) := by
    rw [Store.write_push_of_lt hdlt, Store.write_of_write_eq_some hsi, hsi', Option.map_some]
  refine ⟨a₂, zn, si', dec p zq, by simp [a₂, a₁, harr], hsi',
    (exec_seq_instr_un I (s := si.push (p, a₁)) (by rw [hst]; exact r1 arr) hzc
      (by dsimp only [IExp.eval_zero]; rw [hst, ← hsz, Store.write_push_size (by omega)])).trans
    ((exec_seq_instr_bin I (s := si.push (p, a₂))
      (by dsimp only [IExp.eval_zero]; rw [← hsz];
          exact Store.read_push_size_set!_zero (by omega)) (r3 _)
      hzq (by dsimp only [IExp.eval_zero]; rw [← hsz, Store.write_push_size h₁])).trans
    ((exec_seq_instr_bin I
      (by rw [Store.read_push_of_lt hdlt]; exact Store.read_of_write_eq_some hsi)
      (by dsimp only [IExp.eval_zero]; rw [← hsz]; exact Store.read_push_size_set!_zero h₁)
      hzn w3).trans (exec_skip I _))),
    hq, hn, fun h0 => hz p w zq zn hzn h0⟩

/-- One step of `axpy` under an error contract, from a store with a scratch buffer pushed. -/
private theorem exec_axpy_step_err (h : IsArithErrSem err dec safe I.sem) {si : Store P K}
    {a : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo : IExp ℕ} {t i : ℕ} {wa wx wy : K}
    {st' : St P K C} {arr : Array (Option K)}
    (ha : si.read p a.buf a.idx.eval = some wa) (hx : si.read p x (xo.eval + i) = some wx)
    (hy : si.read p y (yo.eval + i) = some wy) (ht : si.size = t) (harr : arr.size = 1)
    (hst : st'.store = si.push (p, arr)) (hs₁ : safe p (dec p wa * dec p wx))
    (hs₂ : ∀ q, err p .mul (dec p wa * dec p wx) q → safe p (q + dec p wy)) :
    ∃ (arr' : Array (Option K)) (w' : K) (si' : Store P K) (q : ℝ), arr'.size = 1 ∧
      si.write p y (yo.eval + i) w' = some si' ∧
      exec I (.seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩))
        (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip)) st' =
      some { st' with
        store := si'.push (p, arr')
        cnt := st'.cnt + I.charge (.bin p .mul) + I.charge (.bin p .add) } ∧
      err p .mul (dec p wa * dec p wx) q ∧ err p .add (q + dec p wy) (dec p w') := by
  obtain ⟨zq, hzq⟩ := h.bin_ok p .mul wa wx trivial (fun h => nomatch h) hs₁
  have hq : err p .mul (dec p wa * dec p wx) (dec p zq) := h.bin_err p .mul wa wx zq trivial hzq
  obtain ⟨zn, hzn⟩ := h.bin_ok p .add wy zq trivial (fun h => nomatch h) (by
    change safe p (dec p wy + dec p zq)
    rw [add_comm]
    exact hs₂ _ hq)
  have hn : err p .add (dec p zq + dec p wy) (dec p zn) := by
    have := h.bin_err p .add wy zq zn trivial hzn
    change err p .add (dec p wy + dec p zq) _ at this
    rwa [add_comm] at this
  obtain ⟨si', hsi'⟩ := Store.exists_write_eq_some_of_read_eq_some (v := zn) hy
  set a₁ := arr.set! 0 (some zq)
  have h₁ : 0 < a₁.size := by simp [a₁, harr]
  have hylt : y < si.size := Store.lt_size_of_read_eq_some hy
  refine ⟨a₁, zn, si', dec p zq, by simp [a₁, harr], hsi',
    (exec_seq_instr_bin I (s := si.push (p, a₁))
      (by rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some ha)]; exact ha)
      (by rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some hx)]; exact hx)
      hzq
      (by dsimp only [IExp.eval_zero]; rw [hst, ← ht, Store.write_push_size (by omega)])).trans
    ((exec_seq_instr_bin I
      (by rw [Store.read_push_of_lt hylt]; exact hy)
      (by dsimp only [IExp.eval_zero]; rw [← ht]; exact Store.read_push_size_set!_zero (by omega))
      hzn
      (by rw [Store.write_push_of_lt hylt]; dsimp only [IExp.eval_add, IExp.eval_var];
          rw [hsi', Option.map_some])).trans (exec_skip I _)), hq, hn⟩

/-- The store facts of a run of `gemv` from the store `s₀` (with the scratch buffer `T`
pushed): the scratch buffer, the cells of $\mathbf{y}$, and the decoded words of $\mathbf{A}$
and $\mathbf{x}$ outside them. -/
private structure GemvErrCtx (s₀ : Store P K) (dec : P → K → ℝ) (p : P) (T A x y m n ao xo yo : ℕ)
    (av : ℕ → ℕ → ℝ) (xv : ℕ → ℝ) : Prop where
  scratch : s₀.shape[T]? = some (p, 1)
  y_ne : 0 < m → y ≠ T
  y_shape : ∀ i < m, ∃ k, s₀.shape[y]? = some (p, k) ∧ yo + i < k
  A_read : ∀ i < m, ∀ j < n, ∃ w, s₀.read p A (ao + i + m * j) = some w ∧ dec p w = av i j
  A_out : ∀ i < m, ∀ j < n, A ≠ T ∧ ¬(p = p ∧ A = y ∧ yo ≤ ao + i + m * j ∧
    ao + i + m * j < yo + m)
  x_read : ∀ j < n, ∃ w, s₀.read p x (xo + j) = some w ∧ dec p w = xv j
  x_out : ∀ j < n, x ≠ T ∧ ¬(p = p ∧ x = y ∧ yo ≤ xo + j ∧ xo + j < yo + m)

/-- One step of `gemv` under an error contract: $t \leftarrow a_{ij} x_j$, then
$y_i \leftarrow y_i + t$, in the frame of the block of $\mathbf{y}$. -/
private theorem exec_gemvStep_err (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) {s₀ : Store P K} {T A x y L : ℕ} {m ao xo yo : IExp ℕ}
    {σ : St P K C} {g : ℕ → Option K} {i j : ℕ} {wa wx w : K}
    (hF : Store.BlockFrame s₀ p T y yo.eval L σ.store g) (hT : s₀.shape[T]? = some (p, 1))
    (hyT : y ≠ T) (hi : i < L) (hy : ∃ k, s₀.shape[y]? = some (p, k) ∧ yo.eval + i < k)
    (hA : σ.store.read p A (ao.eval + i + m.eval * j) = some wa)
    (hx : σ.store.read p x (xo.eval + j) = some wx) (hw : g i = some w)
    (hs₁ : safe p (dec p wa * dec p wx))
    (hs₂ : ∀ q, err p .mul (dec p wa * dec p wx) q → safe p (dec p w + q)) :
    ∃ (σ' : St P K C) (w' : K) (q : ℝ), exec I (.seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) σ = some σ' ∧
      Store.BlockFrame s₀ p T y yo.eval L σ'.store (Function.update g i (some w')) ∧
      err p .mul (dec p wa * dec p wx) q ∧ err p .add (dec p w + q) (dec p w') ∧
      (dec p w = 0 → dec p w' = q) := by
  obtain ⟨zq, hzq⟩ := h.bin_ok p .mul wa wx trivial (fun h => nomatch h) hs₁
  have hq : err p .mul (dec p wa * dec p wx) (dec p zq) := h.bin_err p .mul wa wx zq trivial hzq
  obtain ⟨s₁, h₁⟩ := hF.exists_write_eq_some zq hT one_pos
  have h₁' := hF.write_scratch (fun _ => hyT) h₁
  obtain ⟨k, hysh, hylt⟩ := hy
  have rw₁ : s₁.read p y (yo.eval + i) = some w := by rw [h₁'.2.2 _ hi, hw]
  obtain ⟨zn, hzn⟩ := h.bin_ok p .add w zq trivial (fun h => nomatch h) (hs₂ _ hq)
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some zn hysh hylt
  exact ⟨_, zn, dec p zq, (exec_seq_instr_bin I hA hx hzq h₁).trans
    ((exec_seq_instr_bin I rw₁ (Store.read_of_write_eq_some h₁) hzn h₂).trans (exec_skip I _)),
    h₁'.write_of_lt hi h₂, hq, h.bin_err p .add w zq zn trivial hzn,
    fun h0 => hz p w zq zn hzn h0⟩

/-- One column of `gemv` under an error contract: every row trace advances by one step. -/
private theorem exec_gemvRow_err (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) {s₀ : Store P K} {T A x y : ℕ} {m n ao xo yo : IExp ℕ}
    {av : ℕ → ℕ → ℝ} {xv : ℕ → ℝ}
    (hC : GemvErrCtx s₀ dec p T A x y m.eval n.eval ao.eval xo.eval yo.eval av xv)
    (hsafe : ∀ i < m.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ, IsDotTrace (err p) (av i) xv k s →
      safe p (av i k * xv k) ∧ ∀ q, err p .mul (av i k * xv k) q → safe p (s k + q))
    {σ : St P K C} {W : ℕ → K} {S : ℕ → ℕ → ℝ} {j : ℕ} (hj : j < n.eval)
    (hF : Store.BlockFrame s₀ p T y yo.eval m.eval σ.store fun k => some (W k))
    (hS : ∀ i < m.eval, IsDotTrace (err p) (av i) xv j (S i) ∧ dec p (W i) = S i j) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) σ = some σ' ∧
      ∃ (W' : ℕ → K) (S' : ℕ → ℕ → ℝ),
        Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store (fun k => some (W' k)) ∧
        ∀ i < m.eval, IsDotTrace (err p) (av i) xv (j + 1) (S' i) ∧
          dec p (W' i) = S' i (j + 1) := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ (W' : ℕ → K) (S' : ℕ → ℕ → ℝ),
      Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store (fun k => some (W' k)) ∧
      ∀ i < m.eval, IsDotTrace (err p) (av i) xv (if i < i' then j + 1 else j) (S' i) ∧
        dec p (W' i) = S' i (if i < i' then j + 1 else j)) ⟨W, S, hF, by simpa using hS⟩ ?_).imp
    fun σ' ⟨hrun, W', S', hF', hrow⟩ =>
      ⟨hrun, W', S', hF', fun i hi => by simpa [hi] using hrow i hi⟩
  rintro i' hi' σ' ⟨W', S', hF', hrow⟩
  obtain ⟨hAT, hAout⟩ := hC.A_out i' hi' j hj
  obtain ⟨hxT, hxout⟩ := hC.x_out j hj
  obtain ⟨wa, hwa, hva⟩ := hC.A_read i' hi' j hj
  obtain ⟨wx, hwx, hvx⟩ := hC.x_read j hj
  have htr := hrow i' hi'
  simp only [lt_irrefl, if_false] at htr
  have hsf := hsafe i' hi' j hj (S' i') htr.1
  rw [← hva, ← hvx] at hsf
  obtain ⟨σ'', w', q, hrun, hF'', hq, hn, h0⟩ := exec_gemvStep_err I p h hz hF' hC.scratch
    (hC.y_ne (by omega)) hi' (hC.y_shape i' hi') ((hF'.read_of_ne hAT hAout).trans hwa)
    ((hF'.read_of_ne hxT hxout).trans hwx) rfl hsf.1 (by rw [htr.2]; exact hsf.2)
  rw [hva, hvx] at hq
  rw [htr.2] at hn h0
  refine ⟨σ'', hrun, Function.update W' i' w',
    Function.update S' i' (Function.update (S' i') (j + 1) (dec p w')),
    by convert hF'' using 1; exact Function.comp_update some W' i' w', fun i hi => ?_⟩
  by_cases hii : i = i'
  · subst hii
    simp only [lt_add_one, if_true, Function.update_self]
    exact ⟨htr.1.update hq hn h0, trivial⟩
  · rw [Function.update_of_ne hii, Function.update_of_ne hii]
    have : (i < i' + 1) = (i < i') := propext (by omega)
    simp only [this]
    exact hrow i hi

/-- The columns of `gemv` under an error contract, from $\mathbf{y}$ holding the zero word. -/
private theorem exec_gemvCols_err (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) {s₀ : Store P K} {T A x y : ℕ} {m n ao xo yo : IExp ℕ}
    {av : ℕ → ℕ → ℝ} {xv : ℕ → ℝ}
    (hC : GemvErrCtx s₀ dec p T A x y m.eval n.eval ao.eval xo.eval yo.eval av xv)
    (hsafe : ∀ i < m.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ, IsDotTrace (err p) (av i) xv k s →
      safe p (av i k * xv k) ∧ ∀ q, err p .mul (av i k * xv k) q → safe p (s k + q))
    {σ : St P K C} {z0 : K} (hz0 : dec p z0 = 0)
    (hF : Store.BlockFrame s₀ p T y yo.eval m.eval σ.store fun _ => some z0) :
    ∃ σ', exec I (.loop n fun j => .seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) .skip) σ = some σ' ∧
      ∃ (W : ℕ → K) (S : ℕ → ℕ → ℝ),
        Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store (fun k => some (W k)) ∧
        ∀ i < m.eval, IsDotTrace (err p) (av i) xv n.eval (S i) ∧ dec p (W i) = S i n.eval := by
  refine exists_exec_loop_eq_some_of_forall I (fun j' σ' => ∃ (W : ℕ → K) (S : ℕ → ℕ → ℝ),
      Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store (fun k => some (W k)) ∧
      ∀ i < m.eval, IsDotTrace (err p) (av i) xv j' (S i) ∧ dec p (W i) = S i j')
    ⟨fun _ => z0, fun _ _ => 0, hF,
      fun _ _ => ⟨⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩, hz0⟩⟩ ?_
  rintro j hj σ' ⟨W, S, hF, hS⟩
  obtain ⟨σ'', hrun, W', S', hF', hS'⟩ := exec_gemvRow_err I p h hz hC hsafe hj hF hS
  exact ⟨σ'', by rw [exec_seq_skip, hrun], W', S', hF', hS'⟩

/-- The zeroing loop of `gemv`: every cell of $\mathbf{y}$ gets the zero word. -/
private theorem exec_gemvZero_err {z0 : K} (hz0 : I.sem.lit p 0 = some z0) {s₀ : Store P K}
    {T y : ℕ} {m yo : IExp ℕ} {σ : St P K C} {g : ℕ → Option K}
    (hy : ∀ i < m.eval, ∃ k, s₀.shape[y]? = some (p, k) ∧ yo.eval + i < k)
    (hF : Store.BlockFrame s₀ p T y yo.eval m.eval σ.store g) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.lit p ⟨y, yo + .var i⟩ 0)) .skip) σ =
        some σ' ∧
      ∃ g', Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store g' ∧
        ∀ i < m.eval, g' i = some z0 := by
  refine exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ g',
      Store.BlockFrame s₀ p T y yo.eval m.eval σ'.store g' ∧ ∀ i < i', g' i = some z0)
    ⟨g, hF, by simp⟩ ?_
  rintro i' hi' σ' ⟨g', hF', hrow⟩
  obtain ⟨k, hysh, hylt⟩ := hy i' hi'
  obtain ⟨s'', hw⟩ := hF'.exists_write_eq_some z0 hysh hylt
  refine ⟨_, (exec_seq_instr_lit I hz0 hw).trans (exec_skip I _), _, hF'.write_of_lt hi' hw,
    fun i hi => ?_⟩
  by_cases hii : i = i'
  · subst hii
    simp
  · rw [Function.update_of_ne hii]
    exact hrow i (by omega)

/-- The cells of a block that can be written: the buffer exists, and its shape. -/
private theorem block_facts_of_write {s : Store P K} {b off L : ℕ}
    (h : ∀ i < L, ∃ v s₁, s.write p b (off + i) v = some s₁) :
    (0 < L → b < s.size) ∧ ∀ i < L, ∃ k, s.shape[b]? = some (p, k) ∧ off + i < k := by
  refine ⟨fun hL => ?_, fun i hi => ?_⟩
  · obtain ⟨v, s₁, hw⟩ := h 0 hL
    exact Store.lt_size_of_write_eq_some hw
  · obtain ⟨v, s₁, hw⟩ := h i hi
    obtain ⟨k, hk, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some
      (Store.read_of_write_eq_some hw)
    exact ⟨k, Store.shape_of_write_eq_some hw ▸ hk, hlt⟩

end Helpers

/-! ### Run lemmas, for any error relation -/

section Runs

variable {err : P → BinOp → ℝ → ℝ → Prop} {safe : P → ℝ → Prop}

/-- **The run of `dot` under an error contract**: if the cells of $\mathbf{x}$ and $\mathbf{y}$
hold words decoding to $x_i$, $y_i$ ($i < n$), $\mathit{dst}$ is a cell of tag $p$ in neither,
adding zero is exact, and on every trace prefix the next product and sum are in range, then the
run succeeds, writes one word $w$ into $\mathit{dst}$ and nothing else, and $w$ decodes to the
last value of a trace of recursive accumulation of $\sum_{i<n} x_i y_i$ under `err`.
[Higham2002, §3.1], for the order of operations of `dot`. -/
theorem IsArithErrSem.exec_dot (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁)
    (hsafe : ∀ k < n.eval, ∀ s : ℕ → ℝ, IsDotTrace (err p) xs ys k s →
      safe p (xs k * ys k) ∧ ∀ q, err p .mul (xs k * ys k) q → safe p (s k + q)) :
    ∃ st' w, ∃ s : ℕ → ℝ, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      IsDotTrace (err p) xs ys n.eval s ∧ dec p w = s n.eval := by
  obtain ⟨z0, hz0, hdz0⟩ := h.lit_zero p
  obtain ⟨v, s₁, hw⟩ := hdst
  obtain ⟨s0, hs0⟩ := Store.exists_write_eq_some_of_write_eq_some hw z0
  rw [run_dot, exec_seq_skip, exec_named, exec_seq_instr_lit I hz0 hs0, exec_alloc,
    exec_seq_skip]
  refine exists₃_of (Option.exists_map_eq_some_of_exists (exists_exec_loop_eq_some_of_forall I
    (fun i st' => ∃ si : Store P K, ∃ arr : Array (Option K), ∃ w : K, ∃ s : ℕ → ℝ,
      st.store.write p dst.buf dst.idx.eval w = some si ∧ arr.size = 1 ∧
      st'.store = si.push (p, arr) ∧ IsDotTrace (err p) xs ys i s ∧ dec p w = s i) ?_ ?_)
    fun _ ⟨si, _, w, s, hsi, _, hst, htr, hws⟩ => ⟨w, s, by simpa [hst] using hsi, htr, hws⟩)
  · exact ⟨s0, Array.replicate 1 none, z0, fun _ => 0, hs0, by simp, rfl,
      ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩, hdz0⟩
  · intro i hi st' ⟨si, arr, w, s, hsi, harr, hst, htr, hws⟩
    obtain ⟨wx, hwx, hvx⟩ := hx i hi
    obtain ⟨wy, hwy, hvy⟩ := hy i hi
    have hsf := hsafe i hi s htr
    rw [← hvx, ← hvy] at hsf
    obtain ⟨arr', w', si', q, harr', hsi', hrun, hq, hn, h0⟩ := exec_dot_step_err I p h hz hwx
      hwy (fun h => hdx h i hi) (fun h => hdy h i hi) (Store.size_of_write_eq_some hs0).symm
      hsi harr hst hsf.1 (by rw [hws]; exact hsf.2)
    rw [hvx, hvy] at hq
    rw [hws] at hn h0
    refine ⟨_, hrun, si', arr', w', Function.update s (i + 1) (dec p w'), hsi', harr', rfl,
      htr.update hq hn h0, by rw [Function.update_self]⟩

/-- **The run of `axpy` under an error contract**: if $a$ and the cells of $\mathbf{x}$ and
$\mathbf{y}$ hold words decoding to $a$, $x_i$, $y_i$ ($i < n$), $a$ is not in $\mathbf{y}$,
$\mathbf{x}$ and $\mathbf{y}$ are the same vector or do not overlap, and every $a x_i$ and every
$q + y_i$ with $q$ related to $a x_i$ is in range, then the run succeeds, writes words $w_i$ into
the cells of $\mathbf{y}$ and nothing else, and $w_i$ decodes to a value related by `err` to
$q_i + y_i$ for a $q_i$ related to $a x_i$. From the model (2.4) of [Higham2002, §2.2], for
the order of operations of `axpy`. -/
theorem IsArithErrSem.exec_axpy (h : IsArithErrSem err dec safe I.sem) (a : Cell ℕ ℕ) (x : ℕ)
    (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : ℝ) (xs ys : ℕ → ℝ)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (hsafe : ∀ i < n.eval, safe p (av * xs i) ∧ ∀ q, err p .mul (av * xs i) q →
      safe p (q + ys i)) :
    ∃ st', ∃ W : ℕ → K, exec I (axpy p a x xo y yo n).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, ∃ q, err p .mul (av * xs i) q ∧ err p .add (q + ys i) (dec p (W i)) := by
  obtain ⟨wa, hwa, hva⟩ := ha
  rw [run_axpy, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  refine exists₂_of (Option.exists_map_eq_some_of_exists (exists_exec_loop_eq_some_of_forall I
    (fun i st' => ∃ si : Store P K, ∃ arr : Array (Option K), ∃ W : ℕ → K,
      (List.range i).foldlM (fun s j => s.write p y (yo.eval + j) (W j)) st.store = some si ∧
      arr.size = 1 ∧ st'.store = si.push (p, arr) ∧
      ∀ k < i, ∃ q, err p .mul (av * xs k) q ∧ err p .add (q + ys k) (dec p (W k))) ?_ ?_)
    fun _ ⟨si, _, W, hsi, _, hst, hW⟩ =>
      ⟨W, by rw [Store.writeBlock_map_range, hsi]; simp [hst], hW⟩)
  · exact ⟨st.store, Array.replicate 1 none, fun _ => wa, rfl, by simp, rfl,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  · intro i hi st' ⟨si, arr, W, hsi, harr, hst, hW⟩
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ y ∨ j ≠ yo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    obtain ⟨wx, hwx, hvx⟩ := hx i hi
    obtain ⟨wy, hwy, hvy⟩ := hy i hi
    have ha' : si.read p a.buf a.idx.eval = some wa := by
      rw [hrd fun k hk => ?_, hwa]
      by_cases h : a.buf = y
      · exact Or.inr (hay h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some wx := by
      rw [hrd fun k hk => ?_, hwx]
      by_cases h : x = y
      · exact Or.inr fun he => absurd (hxy h i hi k (hk.trans hi) he) (by omega)
      · exact Or.inl h
    have hy' : si.read p y (yo.eval + i) = some wy := by
      rw [hrd fun k hk => Or.inr (by omega), hwy]
    have hsf := hsafe i hi
    rw [← hva, ← hvx, ← hvy] at hsf
    obtain ⟨arr', w', si', q, harr', hsi', hrun, hq, hn⟩ := exec_axpy_step_err I p h ha' hx' hy'
      (Store.size_of_foldlM_write_eq_some _ _ _ hsi) harr hst hsf.1 hsf.2
    rw [hva, hvx] at hq
    rw [hvy] at hn
    refine ⟨_, hrun, si', arr', Function.update W i w', ?_, harr', rfl, fun k hk => ?_⟩
    · rw [List.range_succ, List.foldlM_append, foldlM_write_congr _ fun j hj =>
        Function.update_of_ne (Nat.ne_of_lt (List.mem_range.mp hj)) _ _, hsi]
      simp [hsi']
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt hk)]
        exact hW k hk
      · rw [Function.update_self]
        exact ⟨q, hq, hn⟩

/-- **The run of `gemv` under an error contract**: if buffer $A$ holds words decoding to
$a_{ij}$ ($i < m$, $j < n$, column-major from $\mathit{ao}$), the cells of $\mathbf{x}$ words
decoding to $x_j$, the cells of $\mathbf{y}$ are cells of tag $p$ overlapping neither, adding
zero is exact, and on every trace prefix of every row the next product and sum are in range,
then the run succeeds, writes words $w_i$ into the cells of $\mathbf{y}$ and nothing else, and
$w_i$ decodes to the last value of a trace of recursive accumulation of
$\sum_{j<n} a_{ij} x_j$. [Higham2002, §3.5], for the order of operations of `gemv`. -/
theorem IsArithErrSem.exec_gemv (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (av : ℕ → ℕ → ℝ) (xv : ℕ → ℝ)
    (hA : ∀ i < m.eval, ∀ j < n.eval, ∃ w,
      st.store.read p A (ao.eval + i + m.eval * j) = some w ∧ dec p w = av i j)
    (hx : ∀ j < n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁)
    (hsafe : ∀ i < m.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ, IsDotTrace (err p) (av i) xv k s →
      safe p (av i k * xv k) ∧ ∀ q, err p .mul (av i k * xv k) q → safe p (s k + q)) :
    ∃ st', ∃ W : ℕ → K, ∃ s : ℕ → ℕ → ℝ, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ∀ i < m.eval, IsDotTrace (err p) (av i) xv n.eval (s i) ∧ dec p (W i) = s i n.eval := by
  obtain ⟨z0, hz0, hdz0⟩ := h.lit_zero p
  obtain ⟨hylt, hyshape⟩ := block_facts_of_write p hy
  rw [run_gemv, exec_seq_skip, exec_named, exec_seq]
  obtain ⟨σ₁, h0, g₁, hI₁, hzr⟩ := exec_gemvZero_err I p (s₀ := st.store) (T := st.store.size)
    (σ := st) hz0 hyshape ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hsz : σ₁.store.size = st.store.size := by
    simpa [Store.size_shape] using congrArg Array.size hI₁.1
  rw [h0, Option.bind_some, exec_alloc, exec_seq_skip, hsz]
  have hC : GemvErrCtx (st.store.push (p, Array.replicate (1 : IExp ℕ).eval none)) dec p
      st.store.size A x y m.eval n.eval ao.eval xo.eval yo.eval av xv :=
    { scratch := Store.getElem?_shape_push_size _ _ _
      y_ne := fun h => Nat.ne_of_lt (hylt h)
      y_shape := fun i hi => by
        rw [Store.getElem?_shape_push_of_lt _ (hylt (by omega))]
        exact hyshape i hi
      A_read := fun i hi j hj => by
        obtain ⟨w, hw, hv⟩ := hA i hi j hj
        exact ⟨w, by rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some hw), hw], hv⟩
      A_out := fun i hi j hj => by
        obtain ⟨w, hw, -⟩ := hA i hi j hj
        have hlt : i + m.eval * j < m.eval * n.eval := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some hw), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyA rfl with h | h <;> omega
      x_read := fun j hj => by
        obtain ⟨w, hw, hv⟩ := hx j hj
        exact ⟨w, by rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some hw), hw], hv⟩
      x_out := fun j hj => by
        obtain ⟨w, hw, -⟩ := hx j hj
        refine ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some hw), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyx rfl with h | h <;> omega }
  obtain ⟨σF, hF, W, S, hIF, hS⟩ := exec_gemvCols_err I p h hz hC hsafe
    (σ := { σ₁ with
      store := σ₁.store.push (p, Array.replicate (1 : IExp ℕ).eval none)
      cur := Function.update σ₁.cur p (σ₁.cur p + (1 : IExp ℕ).eval)
      peak := Function.update σ₁.peak p (max (σ₁.peak p) (σ₁.cur p + (1 : IExp ℕ).eval))
      curW := σ₁.curW + (1 : IExp ℕ).eval * I.width p
      peakW := max σ₁.peakW (σ₁.curW + (1 : IExp ℕ).eval * I.width p) })
    hdz0 ((hI₁.push _ hylt).congr hzr)
  rw [hF, Option.map_some]
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := st.store) (p := p)
    (b := y) (off := yo.eval) (xs := (List.range m.eval).toArray.map W)
    fun i hi => hyshape i (by simpa using hi)
  refine ⟨_, W, S, rfl, ?_, hS⟩
  rw [hs₁, hIF.pop_eq hs₁ (by simp) fun i hi => by simp [hi]]

/-- One column of `gemm` under an error contract: the `gemv` of column $c$, from a store in
the frame of the block of $\mathbf{C}$. -/
private theorem exec_gemm_step_err (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ)
    (bo : IExp ℕ) (Cb : ℕ) (co : IExp ℕ) (av bv : ℕ → ℕ → ℝ)
    (hA : ∀ i < m.eval, ∀ k < n.eval, ∃ w,
      st.store.read p A (ao.eval + i + m.eval * k) = some w ∧ dec p w = av i k)
    (hB : ∀ k < n.eval, ∀ j < l.eval, ∃ w,
      st.store.read p B (bo.eval + k + n.eval * j) = some w ∧ dec p w = bv k j)
    (hCA : Cb = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : Cb = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hCsh : ∀ k < m.eval * l.eval, ∃ N, st.store.shape[Cb]? = some (p, N) ∧ co.eval + k < N)
    (hsafe : ∀ i < m.eval, ∀ j < l.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ,
      IsDotTrace (err p) (av i) (fun k => bv k j) k s →
      safe p (av i k * bv k j) ∧ ∀ q, err p .mul (av i k * bv k j) q → safe p (s k + q))
    {c : ℕ} (hcl : c < l.eval) (σ : St P K C) (g : ℕ → Option K) (W : ℕ → K)
    (S : ℕ → ℕ → ℕ → ℝ)
    (hD : Store.BlockFrame st.store p st.store.size Cb co.eval (m.eval * l.eval) σ.store g)
    (hg : ∀ k < m.eval * c, g k = some (W k))
    (hS : ∀ i < m.eval, ∀ j < c, IsDotTrace (err p) (av i) (fun k => bv k j) n.eval (S i j) ∧
      dec p (W (i + m.eval * j)) = S i j n.eval) :
    ∃ σ', exec I (gemv p m n A ao B (bo + n * .var c) Cb (co + m * .var c)).run σ = some σ' ∧
      ∃ (g' : ℕ → Option K) (W' : ℕ → K) (S' : ℕ → ℕ → ℕ → ℝ),
        Store.BlockFrame st.store p st.store.size Cb co.eval (m.eval * l.eval) σ'.store g' ∧
        (∀ k < m.eval * (c + 1), g' k = some (W' k)) ∧
        ∀ i < m.eval, ∀ j < c + 1,
          IsDotTrace (err p) (av i) (fun k => bv k j) n.eval (S' i j) ∧
          dec p (W' (i + m.eval * j)) = S' i j n.eval := by
  have hmc : m.eval * c + m.eval ≤ m.eval * l.eval := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcl
  have hnc : n.eval * c + n.eval ≤ n.eval * l.eval := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcl
  have hA' : ∀ i < m.eval, ∀ k < n.eval, ∃ w,
      σ.store.read p A (ao.eval + i + m.eval * k) = some w ∧ dec p w = av i k := by
    intro i hi k hk
    obtain ⟨w, hw, hv⟩ := hA i hi k hk
    have := Nat.add_mul_lt_mul_of_lt_of_lt hi hk
    refine ⟨w, (hD.read_of_ne (Nat.ne_of_lt (Store.lt_size_of_read_eq_some hw)) ?_).trans hw, hv⟩
    rintro ⟨-, h, h₁, h₂⟩
    rcases hCA h.symm with h | h <;> omega
  have hx : ∀ k < n.eval, ∃ w, σ.store.read p B ((bo + n * .var c).eval + k) = some w ∧
      dec p w = bv k c := by
    intro k hk
    obtain ⟨w, hw, hv⟩ := hB k hk c hcl
    have := Nat.add_mul_lt_mul_of_lt_of_lt hk hcl
    simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]
    rw [show bo.eval + n.eval * c + k = bo.eval + k + n.eval * c by omega]
    refine ⟨w, (hD.read_of_ne (Nat.ne_of_lt (Store.lt_size_of_read_eq_some hw)) ?_).trans hw, hv⟩
    rintro ⟨-, h, h₁, h₂⟩
    rcases hCB h.symm with h | h <;> omega
  obtain ⟨σ', Wc, Sc, hrun, hst, hSc⟩ := IsArithErrSem.exec_gemv I p σ h hz m n A ao B
    (bo + n * .var c) Cb (co + m * .var c) av (fun k => bv k c) hA' hx
    (fun h => by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]; omega)
    (fun h => by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]; omega)
    (fun i hi => by
      obtain ⟨N, hN, hlt⟩ := hCsh (m.eval * c + i) (by omega)
      obtain ⟨s', hs'⟩ := hD.exists_write_eq_some (Classical.choice ⟨W 0⟩) hN hlt
      exact ⟨_, s', by simpa [add_assoc] using hs'⟩)
    fun i hi k hk s hs => hsafe i hi c hcl k hk s hs
  simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] at hst
  refine ⟨σ', hrun, _, fun k => if m.eval * c ≤ k ∧ k < m.eval * c + m.eval then
      Wc (k - m.eval * c) else W k, fun i j => if j = c then Sc i else S i j,
    hD.writeBlock hst (by simp; omega), fun k hk => ?_, fun i hi j hj => ?_⟩
  · by_cases hkc : k < m.eval * c
    · simp only [Array.size_map, List.size_toArray, List.length_range]
      rw [if_neg (by omega), if_neg (by omega), hg k hkc]
    · have hk' : k < m.eval * c + m.eval := by rw [Nat.mul_succ] at hk; omega
      simp only [Array.size_map, List.size_toArray, List.length_range]
      rw [if_pos ⟨by omega, hk'⟩, if_pos ⟨by omega, hk'⟩]
      simp [show k - m.eval * c < m.eval by omega]
  · beta_reduce
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
      rw [if_neg (Nat.ne_of_lt hj), if_neg (by omega)]
      exact hS i hi j hj
    · rw [if_pos rfl, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel]
      exact hSc i hi

/-- **The run of `gemm` under an error contract**: if buffers $A$ and $B$ hold words decoding to
$a_{ik}$ and $b_{kj}$ ($m \times n$ and $n \times l$, column-major from $\mathit{ao}$ and
$\mathit{bo}$), the block of $\mathbf{C}$ is $ml$ cells of tag $p$ overlapping neither, adding
zero is exact, and on every trace prefix of every entry the next product and sum are in range,
then the run succeeds, writes words $w_{i + mj}$ into the block of $\mathbf{C}$ and nothing else,
and $w_{i+mj}$ decodes to the last value of a trace of recursive accumulation of
$\sum_{k<n} a_{ik} b_{kj}$. [Higham2002, §3.5], for the order of operations of `gemm`. -/
theorem IsArithErrSem.exec_gemm (h : IsArithErrSem err dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ)
    (bo : IExp ℕ) (C : ℕ) (co : IExp ℕ) (av bv : ℕ → ℕ → ℝ)
    (hA : ∀ i < m.eval, ∀ k < n.eval, ∃ w,
      st.store.read p A (ao.eval + i + m.eval * k) = some w ∧ dec p w = av i k)
    (hB : ∀ k < n.eval, ∀ j < l.eval, ∃ w,
      st.store.read p B (bo.eval + k + n.eval * j) = some w ∧ dec p w = bv k j)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hC : ∀ t < m.eval * l.eval, ∃ v s₁, st.store.write p C (co.eval + t) v = some s₁)
    (hsafe : ∀ i < m.eval, ∀ j < l.eval, ∀ k < n.eval, ∀ s : ℕ → ℝ,
      IsDotTrace (err p) (av i) (fun k => bv k j) k s →
      safe p (av i k * bv k j) ∧ ∀ q, err p .mul (av i k * bv k j) q → safe p (s k + q)) :
    ∃ st', ∃ W : ℕ → K, ∃ s : ℕ → ℕ → ℕ → ℝ,
      exec I (gemm p m n l A ao B bo C co).run st = some st' ∧
      st.store.writeBlock p C co.eval ((List.range (m.eval * l.eval)).toArray.map W) =
        some st'.store ∧
      ∀ i < m.eval, ∀ j < l.eval, IsDotTrace (err p) (av i) (fun k => bv k j) n.eval (s i j) ∧
        dec p (W (i + m.eval * j)) = s i j n.eval := by
  obtain ⟨z0, -, -⟩ := h.lit_zero p
  obtain ⟨hClt, hCsh⟩ := block_facts_of_write p hC
  rw [run_gemm, exec_seq_skip, exec_named, exec_seq_skip]
  obtain ⟨σ, hrun, g, W, S, hD, hg, hS⟩ := exists_exec_loop_eq_some_of_forall I (n := l)
    (body := fun c => (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run)
    (fun c σ => ∃ (g : ℕ → Option K) (W : ℕ → K) (S : ℕ → ℕ → ℕ → ℝ),
      Store.BlockFrame st.store p st.store.size C co.eval (m.eval * l.eval) σ.store g ∧
      (∀ k < m.eval * c, g k = some (W k)) ∧
      ∀ i < m.eval, ∀ j < c, IsDotTrace (err p) (av i) (fun k => bv k j) n.eval (S i j) ∧
        dec p (W (i + m.eval * j)) = S i j n.eval)
    ⟨_, fun _ => z0, fun _ _ _ => 0,
      ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, by simp, by simp⟩
    fun c hcl σ ⟨g, W, S, hD, hg, hS⟩ =>
      exec_gemm_step_err I p st h hz m n l A ao B bo C co av bv hA hB hCA hCB hCsh hsafe hcl σ
        g W S hD hg hS
  refine ⟨σ, W, S, hrun, ?_, hS⟩
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := st.store) (p := p)
    (b := C) (off := co.eval) (xs := (List.range (m.eval * l.eval)).toArray.map W)
    fun k hk => hCsh k (by simpa using hk)
  have hpop := (hD.push (p, Array.replicate 1 none) hClt).pop_eq hs₁ (by simp)
    fun k hk => by rw [hg k hk]; simp [hk]
  rw [Array.pop_push] at hpop
  rw [hs₁, hpop]

end Runs

/-! ### The standard model -/

section StandardModel

variable {u : P → ℝ}

/-- **Backward error of `dot`** in the standard model [Higham2002, §3.1], (3.4)
there, with the factor of [CarsonMaShao2026, (3)]: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and $u_p < 1$, if
the cells of $\mathbf{x}$ and $\mathbf{y}$ hold words decoding to $x_i$, $y_i$ ($i < n$) and
$\mathit{dst}$ is a cell of tag $p$ in neither, the run of `dot` succeeds, writes one word $w$ into
$\mathit{dst}$ and nothing else, and
$$w \text{ decodes to } \sum_{i<n} x_i y_i (1 + \eta_i)\,, \qquad
\lvert \eta_i \rvert \le \gamma_n = (1 - u_p)^{-n} - 1\,.$$ -/
theorem IsRelErrSem.exec_dot_eq_sum_mul_one_add
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ) (hu1 : u p < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      ∃ η : ℕ → ℝ, (∀ i < n.eval, |η i| ≤ roundingFactor n.eval (u p)) ∧
        dec p w = ∑ i ∈ range n.eval, xs i * ys i * (1 + η i) := by
  obtain ⟨st', w, s, hrun, hst, htr, hw⟩ := IsArithErrSem.exec_dot I p st
    (h.isArithErrSem fun _ => trivial) hz dst x xo y yo n xs ys hx hy hdx hdy hdst
    fun _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  obtain ⟨η, hη, hs⟩ := htr.exists_eq_sum_mul_one_add (h.nonneg trivial) hu1
  exact ⟨st', w, hrun, hst, η, hη, hw.trans hs⟩

/-- **Backward error of `dot`, product form** in the standard model [Higham2002, §3.1], (3.4)
there: under the contract `NLAlib.Computation.IsRelErrSem` with every value in range and adding
zero exactly, if the cells of $\mathbf{x}$ and $\mathbf{y}$ hold words decoding to $x_i$, $y_i$
($i < n$) and $\mathit{dst}$ is a cell of tag $p$ in neither, the run of `dot` succeeds, writes
one word $w$ into $\mathit{dst}$ and nothing else, and
$$w \text{ decodes to } \sum_{i<n} x_i y_i (1 + \eta_i)\,,$$
each $1 + \eta_i$ a product of $n$ factors $(1 + \delta)^{\pm 1}$ with
$\lvert \delta \rvert \le u_p$ (`NLAlib.Computation.IsRoundingProduct`). -/
theorem IsRelErrSem.exec_dot_eq_sum_mul_one_add_isRoundingProduct
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      ∃ η : ℕ → ℝ, (∀ i < n.eval, IsRoundingProduct (u p) n.eval (η i)) ∧
        dec p w = ∑ i ∈ range n.eval, xs i * ys i * (1 + η i) := by
  obtain ⟨st', w, s, hrun, hst, htr, hw⟩ := IsArithErrSem.exec_dot I p st
    (h.isArithErrSem fun _ => trivial) hz dst x xo y yo n xs ys hx hy hdx hdy hdst
    fun _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  obtain ⟨η, hη, hs⟩ := htr.exists_eq_sum_mul_one_add_isRoundingProduct (h.nonneg trivial)
  exact ⟨st', w, hrun, hst, η, hη, hw.trans hs⟩

/-- **Forward error of `dot`** in the standard model [Higham2002, §3.1], (3.5)
there, with the factor of [CarsonMaShao2026, (3)]: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and $u_p < 1$, if
the cells of $\mathbf{x}$ and $\mathbf{y}$ hold words decoding to $x_i$, $y_i$ ($i < n$) and
$\mathit{dst}$ is a cell of tag $p$ in neither, the run of `dot` succeeds, writes one word $w$ into
$\mathit{dst}$ and nothing else, and
$$\Bigl\lvert \sum_{i<n} x_i y_i - w \Bigr\rvert \le \gamma_n \sum_{i<n}
\lvert x_i \rvert \lvert y_i \rvert\,,$$ with $w$ read through its decoding and
$\gamma_n = (1 - u_p)^{-n} - 1$. -/
theorem IsRelErrSem.exec_dot_abs_sum_mul_sub_le
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ) (hu1 : u p < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      |∑ i ∈ range n.eval, xs i * ys i - dec p w| ≤
        roundingFactor n.eval (u p) * ∑ i ∈ range n.eval, |xs i| * |ys i| := by
  obtain ⟨st', w, s, hrun, hst, htr, hw⟩ := IsArithErrSem.exec_dot I p st
    (h.isArithErrSem fun _ => trivial) hz dst x xo y yo n xs ys hx hy hdx hdy hdst
    fun _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  exact ⟨st', w, hrun, hst,
    hw ▸ htr.abs_sum_mul_sub_le (h.nonneg trivial) hu1⟩

/-- **Rounding error of `axpy`** in the standard model: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range and $u_p < 1$, if $a$ and the cells
of $\mathbf{x}$ and $\mathbf{y}$ hold words decoding to $a$, $x_i$, $y_i$ ($i < n$), $a$ is not
in $\mathbf{y}$, and $\mathbf{x}$ and $\mathbf{y}$ are the same vector or do not overlap, the run
of `axpy` succeeds, writes words $w_i$ into the cells of $\mathbf{y}$ and nothing else, and
$$w_i \text{ decodes to } a x_i (1 + \theta_i) + y_i (1 + \delta_i)\,, \qquad
\lvert \theta_i \rvert \le \gamma_2 = (1 - u_p)^{-2} - 1\,,\quad
\lvert \delta_i \rvert \le u_p\,.$$ From the model (2.4) of [Higham2002, §2.2] and
[CarsonMaShao2026, Lemma 2]. -/
theorem IsRelErrSem.exec_axpy
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : ℝ) (xs ys : ℕ → ℝ) (hu1 : u p < 1)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j) :
    ∃ st', ∃ W : ℕ → K, exec I (axpy p a x xo y yo n).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 (u p) ∧ |δ| ≤ u p ∧
        dec p (W i) = av * xs i * (1 + θ) + ys i * (1 + δ) := by
  obtain ⟨st', W, hrun, hst, hW⟩ := IsArithErrSem.exec_axpy I p st
    (h.isArithErrSem fun _ => trivial) a x xo y yo n av xs ys ha hx hy hay hxy
    fun _ _ => ⟨trivial, fun _ _ => trivial⟩
  refine ⟨st', W, hrun, hst, fun i hi => ?_⟩
  obtain ⟨q, hq, hz⟩ := hW i hi
  exact exists_eq_mul_one_add_add_mul_one_add_of_relErr hq hz hu1

/-- **Rounding error of `rscl`** in the standard model: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range, if $a$ decodes to a nonzero $a$ and
the cells of $\mathbf{x}$ hold words decoding to $x_i$ ($i < n$), $a$ not among them, the run of
`rscl` succeeds, writes words $w_i$ into the cells of $\mathbf{x}$ and nothing else, and
$$w_i \text{ decodes to } \frac{x_i}{a}(1 + \delta_i)\,, \qquad \lvert \delta_i \rvert \le u_p\,.$$
From the model (2.4) of [Higham2002, §2.2]. -/
theorem IsRelErrSem.exec_rscl (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (a : Cell ℕ ℕ)
    (x : ℕ) (xo n : IExp ℕ) (av : ℝ) (xs : ℕ → ℝ) (hav : av ≠ 0)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i) :
    ∃ st', ∃ W : ℕ → K, exec I (rscl p a x xo n).run st = some st' ∧
      st.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ∀ i < n.eval, ∃ δ : ℝ, |δ| ≤ u p ∧ dec p (W i) = xs i / av * (1 + δ) := by
  exact IsArithErrSem.exec_rscl I p st (h.isArithErrSem fun _ => trivial)
    a x xo n av xs hav ha hx hax (fun _ _ => trivial)

/-- **Backward error of `gemv`** in the standard model [Higham2002, §3.5], (3.11)
there, with the factor of [CarsonMaShao2026, (3)]: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and $u_p < 1$, if
buffer $A$ holds the real $m \times n$ matrix $\mathbf{A}$ through the decoding (column-major from
$\mathit{ao}$), the cells of $\mathbf{x}$ hold words decoding to $\mathbf{x}$, and the cells of
$\mathbf{y}$ are cells of tag $p$ overlapping neither, the run of `gemv` succeeds, writes words
$w_i$ into the cells of $\mathbf{y}$ and nothing else, and for some $\Delta\mathbf{A}$ with
$\lvert \Delta a_{ij} \rvert \le \gamma_n \lvert a_{ij} \rvert$,
$\gamma_n = (1 - u_p)^{-n} - 1$,
$$w_i \text{ decodes to } \bigl((\mathbf{A} + \Delta\mathbf{A})\mathbf{x}\bigr)_i\,.$$ -/
theorem IsRelErrSem.exec_gemv_eq_add_mulVec
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (hu1 : u p < 1) (hA : HoldsDecoded st.store dec p A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ∃ ΔA : Matrix (Fin m.eval) (Fin n.eval) ℝ,
        (∀ i j, |ΔA i j| ≤ roundingFactor n.eval (u p) * |M i j|) ∧
        ∀ i : Fin m.eval, dec p (W i) = ((M + ΔA) *ᵥ xv) i := by
  obtain ⟨st', W, S, hrun, hst, hS⟩ := IsArithErrSem.exec_gemv I p st
    (h.isArithErrSem fun _ => trivial) hz m n A ao x xo y yo
    (fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)
    (fun j => if h : j < n.eval then xv ⟨j, h⟩ else 0)
    (fun i hi j hj => by simpa [hi, hj] using hA ⟨i, hi⟩ ⟨j, hj⟩)
    (fun j hj => by simpa [hj] using hx ⟨j, hj⟩) hyA hyx hy
    fun _ _ _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  have hη : ∀ i : Fin m.eval, ∃ η : ℕ → ℝ,
      (∀ k < n.eval, |η k| ≤ roundingFactor n.eval (u p)) ∧ dec p (W i) =
        ∑ k ∈ range n.eval, (if h : (i : ℕ) < m.eval ∧ k < n.eval then M ⟨i, h.1⟩ ⟨k, h.2⟩
          else 0) * (if h : k < n.eval then xv ⟨k, h⟩ else 0) * (1 + η k) := fun i => by
    obtain ⟨η, hη, hs⟩ :=
      (hS i i.2).1.exists_eq_sum_mul_one_add (h.nonneg trivial) hu1
    exact ⟨η, hη, (hS i i.2).2.trans hs⟩
  choose η hηb hηe using hη
  refine ⟨st', W, hrun, hst, fun i j => M i j * η i j, fun i j => ?_, fun i => ?_⟩
  · rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hηb i j j.2) (abs_nonneg _)
  · rw [hηe i]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => by
      change _ = (M i j + M i j * η i j) * xv j
      simp [i.2, j.2]; ring

/-- **Forward error of `gemv`** in the standard model [Higham2002, §3.5], (3.12)
there, with the factor of [CarsonMaShao2026, (3)]: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and $u_p < 1$, if
buffer $A$ holds the real $m \times n$ matrix $\mathbf{A}$ through the decoding (column-major from
$\mathit{ao}$), the cells of $\mathbf{x}$ hold words decoding to $\mathbf{x}$, and the cells of
$\mathbf{y}$ are cells of tag $p$ overlapping neither, the run of `gemv` succeeds, writes words
$w_i$ into the cells of $\mathbf{y}$ and nothing else, and
$$\bigl\lvert (\mathbf{A}\mathbf{x})_i - w_i \bigr\rvert \le
\gamma_n \bigl(\lvert \mathbf{A} \rvert \lvert \mathbf{x} \rvert\bigr)_i\,,$$ with $w_i$
read through its decoding and absolute values entrywise and $\gamma_n = (1 - u_p)^{-n} - 1$.
-/
theorem IsRelErrSem.exec_gemv_abs_mulVec_sub_le
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (hu1 : u p < 1) (hA : HoldsDecoded st.store dec p A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ∀ i : Fin m.eval, |(M *ᵥ xv) i - dec p (W i)| ≤
        roundingFactor n.eval (u p) * ((M.map abs) *ᵥ (fun j => |xv j|)) i := by
  obtain ⟨st', W, S, hrun, hst, hS⟩ := IsArithErrSem.exec_gemv I p st
    (h.isArithErrSem fun _ => trivial) hz m n A ao x xo y yo
    (fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)
    (fun j => if h : j < n.eval then xv ⟨j, h⟩ else 0)
    (fun i hi j hj => by simpa [hi, hj] using hA ⟨i, hi⟩ ⟨j, hj⟩)
    (fun j hj => by simpa [hj] using hx ⟨j, hj⟩) hyA hyx hy
    fun _ _ _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  refine ⟨st', W, hrun, hst, fun i => ?_⟩
  have key := (hS i i.2).1.abs_sum_mul_sub_le (h.nonneg trivial) hu1
  rw [← (hS i i.2).2] at key
  convert key using 2
  · simp only [Matrix.mulVec, dotProduct]
    rw [← Fin.sum_univ_eq_sum_range]
    congr 1
    exact sum_congr rfl fun j _ => by simp [i.2, j.2]
  · simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => by simp [i.2, j.2]

/-- **Forward error of `gemm`** in the standard model [Higham2002, §3.5], (3.13)
there, with the factor of [CarsonMaShao2026, (3)]: under the contract
`NLAlib.Computation.IsRelErrSem` with every value in range, adding zero exactly, and $u_p < 1$, if
buffers $A$ and $B$ hold the real $m \times n$ and $n \times l$ matrices $\mathbf{A}$, $\mathbf{B}$
through the decoding (column-major from $\mathit{ao}$, $\mathit{bo}$) and the block of $\mathbf{C}$
is $ml$ cells of tag $p$ overlapping neither, the run of `gemm` succeeds, writes words $w_{i+mj}$
into the block of $\mathbf{C}$ and nothing else, and
$$\bigl\lvert (\mathbf{A}\mathbf{B})_{ij} - w_{i+mj} \bigr\rvert \le
\gamma_n \bigl(\lvert \mathbf{A} \rvert \lvert \mathbf{B} \rvert\bigr)_{ij}\,,$$ with
$w_{i+mj}$ read through its decoding and absolute values entrywise and
$\gamma_n = (1 - u_p)^{-n} - 1$. -/
theorem IsRelErrSem.exec_gemm_abs_mul_sub_le
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ)
    (bo : IExp ℕ) (C : ℕ) (co : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin n.eval) ℝ)
    (MB : Matrix (Fin n.eval) (Fin l.eval) ℝ) (hu1 : u p < 1)
    (hA : HoldsDecoded st.store dec p A ao.eval MA) (hB : HoldsDecoded st.store dec p B bo.eval MB)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hC : ∀ t < m.eval * l.eval, ∃ v s₁, st.store.write p C (co.eval + t) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemm p m n l A ao B bo C co).run st = some st' ∧
      st.store.writeBlock p C co.eval ((List.range (m.eval * l.eval)).toArray.map W) =
        some st'.store ∧
      ∀ (i : Fin m.eval) (j : Fin l.eval), |(MA * MB) i j - dec p (W (i + m.eval * j))| ≤
        roundingFactor n.eval (u p) * (MA.map abs * MB.map abs) i j := by
  obtain ⟨st', W, S, hrun, hst, hS⟩ := IsArithErrSem.exec_gemm I p st
    (h.isArithErrSem fun _ => trivial) hz m n l A ao B bo C co
    (fun i k => if h : i < m.eval ∧ k < n.eval then MA ⟨i, h.1⟩ ⟨k, h.2⟩ else 0)
    (fun k j => if h : k < n.eval ∧ j < l.eval then MB ⟨k, h.1⟩ ⟨j, h.2⟩ else 0)
    (fun i hi k hk => by simpa [hi, hk] using hA ⟨i, hi⟩ ⟨k, hk⟩)
    (fun k hk j hj => by simpa [hk, hj] using hB ⟨k, hk⟩ ⟨j, hj⟩) hCA hCB hC
    fun _ _ _ _ _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩
  refine ⟨st', W, hrun, hst, fun i j => ?_⟩
  have key := (hS i i.2 j j.2).1.abs_sum_mul_sub_le (h.nonneg trivial) hu1
  rw [← (hS i i.2 j j.2).2] at key
  convert key using 2
  · simp only [Matrix.mul_apply]
    rw [← Fin.sum_univ_eq_sum_range]
    congr 1
    exact sum_congr rfl fun k _ => by simp [i.2, j.2, k.2]
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun k _ => by simp [i.2, j.2, k.2]

end StandardModel

end NLAlib.Computation
