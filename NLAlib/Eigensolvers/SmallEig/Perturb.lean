/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedKernels
public import NLAlib.Eigensolvers.SmallEig.Draws
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Matrix.FinitePrecision.OpsSampling
public import NLAlib.RandomMatrix.Gaussian.Tape

/-!
# The Gaussian perturbation of the input

The first step of the small-eigenvalue program of [BanksGarzaVargasSrivastava2025, Theorem 1.1]:
the input $\mathbf{A}$ of order $N$ becomes $\mathbf{A} + \gamma' \mathbf{G}$ with $\mathbf{G}$ a
standard complex Gaussian matrix drawn from $2N^2$ entries of a Gaussian stream and the scale
$\gamma' = \mathrm{fl}(\gamma/\sqrt N)$ computed by the program from the word $\gamma$, all rounded.
Except with a small probability the result is in the diagonalization class (condition $2/t_2$,
separation $t_1/2$) and is within $\delta/2$ of $\mathbf{A}$: the random-matrix hypotheses at the
order $N$ (`NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix`), the norm of
the perturbation, and the rounding, which the closed class absorbs
(`NLAlib.isClosed_setOf_exists_pseudoConditionNumber_le_and_le_norm_sub`).

## Main definitions

* `NLAlib.SmallEig.ginibrePerturb`: the program `[N, nq] (A, Q) → (A)`.

## Main results

* `NLAlib.SmallEig.ginibrePerturb_writes_word`: the stored words.
* `NLAlib.SmallEig.ginibrePerturb_pwrites`: the class after the perturbation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]

/-- **The Gaussian perturbation** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], line 1 of
`Eig`, with the scale computed by the program): draw $2N^2$ words of the stream `sG` into scratch,
compute $\gamma' = \mathrm{fl}(\gamma/\mathrm{fl}(\sqrt N))$ from the word $\gamma$ = `Q[0]` and the
literal $N$, and the stored $\sqrt{1/2}$, and add $\gamma'\sqrt{1/2}(x_{2k} + i x_{2k+1})$ to the
$k$-th entry of `A`, rounded. The interface is `[N, nq] (A, Q) → (A)`.
Algorithm: small-eig -/
def ginibrePerturb (sG : ℕ) : Impl O Q := opsImpl% [N, nq] (A, Qw) → (A) {
  let G ← alloc (2 * (N * N));
  let Sc ← alloc 3;
  run (gaussDraws (O := O) (Q := Q) sG).body [2 * (N * N)] (G);
  call (Has.inj IndexOp.lit) [N] () → (Sc);
  call (Has.inj ScalarOp.sqrt) [] (Sc) → (Sc);
  call (Has.inj ScalarOp.div) [] (Qw, Sc) → (Sc);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Sc[1]);
  call (Has.inj (ScalarOp.lit 2)) [] () → (Sc[2]);
  call (Has.inj ScalarOp.div) [] (Sc[1], Sc[2]) → (Sc[1]);
  call (Has.inj ScalarOp.sqrt) [] (Sc[1]) → (Sc[1]);
  for j < N * N {
    call (Has.inj ScalarOp.mul) [] (G[2 * j], Sc[1]) → (G[2 * j]);
    call (Has.inj ScalarOp.mul) [] (G[2 * j + 1], Sc[1]) → (G[2 * j + 1]);
    call (Has.inj ScalarOp.mul) [] (G[2 * j], Sc) → (G[2 * j]);
    call (Has.inj ScalarOp.mul) [] (G[2 * j + 1], Sc) → (G[2 * j + 1]);
    call (Has.inj ScalarOp.add) [] (A[2 * j], G[2 * j]) → (A[2 * j]);
    call (Has.inj ScalarOp.add) [] (A[2 * j + 1], G[2 * j + 1]) → (A[2 * j + 1])
  }
}

end Program

section Prefix

/-- An index below $N^2$ makes $N$ positive. -/
private theorem pos_of_lt_mul_self {j N : ℕ} (hj : j < N * N) : 0 < N :=
  Nat.pos_of_ne_zero (by rintro rfl; simp at hj)

/-- The matrix after the first $j$ entries, in column-major order, of
`NLAlib.Ops.Machine.perturbWords`: the other entries are those of $\mathbf{A}$. -/
private noncomputable def perturbPrefix (M : Machine ℝ) {N : ℕ} (γ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (x : ℕ → ℝ) (j : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun r c => if (c : ℕ) * N + r < j then M.perturbWords γ A x r c else A r c

/-- No entry is perturbed before the loop. -/
private theorem perturbPrefix_zero (M : Machine ℝ) {N : ℕ} (γ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (x : ℕ → ℝ) : perturbPrefix M γ A x 0 = A := by
  ext r c
  simp [perturbPrefix]

/-- Every entry is perturbed after the loop. -/
private theorem perturbPrefix_all (M : Machine ℝ) {N : ℕ} (γ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (x : ℕ → ℝ) :
    perturbPrefix M γ A x (N * N) = M.perturbWords γ A x := by
  ext r c
  simp only [perturbPrefix, Matrix.of_apply]
  rw [if_pos (Idx.add_lt_mul c.isLt r.isLt)]

/-- The entry of the perturbation at the flat index $j$, column-major. -/
private theorem perturbWords_apply_divMod (M : Machine ℝ) {N : ℕ} (γ : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) (x : ℕ → ℝ) {j : ℕ} (hj : j < N * N) :
    M.perturbWords γ A x ⟨j % N, Nat.mod_lt _ (pos_of_lt_mul_self hj)⟩
        ⟨j / N, Nat.div_lt_of_lt_mul hj⟩ =
      ⟨M.add (A ⟨j % N, Nat.mod_lt _ (pos_of_lt_mul_self hj)⟩
          ⟨j / N, Nat.div_lt_of_lt_mul hj⟩).re
          (M.mul (M.mul (x (2 * j)) M.sqrtHalf) (M.div γ (M.sqrt (M.lit (N : ℚ))))),
        M.add (A ⟨j % N, Nat.mod_lt _ (pos_of_lt_mul_self hj)⟩
          ⟨j / N, Nat.div_lt_of_lt_mul hj⟩).im
          (M.mul (M.mul (x (2 * j + 1)) M.sqrtHalf) (M.div γ (M.sqrt (M.lit (N : ℚ)))))⟩ := by
  simp only [Ops.Machine.perturbWords, Matrix.of_apply, Nat.div_add_mod']

/-- Writing the entry $j$ (column-major) of the perturbation advances the prefix: the other cells
of the buffer are kept. -/
private theorem holdsMatrix_perturbPrefix_succ {M : Machine ℝ} {N : ℕ} {γ : ℝ}
    {A : Matrix (Fin N) (Fin N) ℂ} {x : ℕ → ℝ} {j : ℕ} (hj : j < N * N) {a : ℕ × ℕ}
    {s s' : Store ℝ} (h : HoldsMatrix a (perturbPrefix M γ A x j) s)
    (hkeep : ∀ i, i ≠ a.2 + 2 * j → i ≠ a.2 + 2 * j + 1 → s'.get a.1 i = s.get a.1 i)
    (hre : s'.get a.1 (a.2 + 2 * j) = some
      (M.perturbWords γ A x ⟨j % N, Nat.mod_lt _ (pos_of_lt_mul_self hj)⟩
        ⟨j / N, Nat.div_lt_of_lt_mul hj⟩).re)
    (him : s'.get a.1 (a.2 + 2 * j + 1) = some
      (M.perturbWords γ A x ⟨j % N, Nat.mod_lt _ (pos_of_lt_mul_self hj)⟩
        ⟨j / N, Nat.div_lt_of_lt_mul hj⟩).im) :
    HoldsMatrix a (perturbPrefix M γ A x (j + 1)) s' := by
  have hN : 0 < N := pos_of_lt_mul_self hj
  have hidx : ∀ (r c : Fin N), (c : ℕ) * N + r = j →
      r = ⟨j % N, Nat.mod_lt _ hN⟩ ∧ c = ⟨j / N, Nat.div_lt_of_lt_mul hj⟩ := fun r c he => by
    have hd := congrArg (· / N) he
    have hm := congrArg (· % N) he
    simp only [Idx.div_add r.isLt, Idx.mod_add r.isLt] at hd hm
    exact ⟨Fin.ext hm, Fin.ext hd⟩
  have hval : ∀ (r c : Fin N), (c : ℕ) * N + r ≠ j →
      perturbPrefix M γ A x (j + 1) r c = perturbPrefix M γ A x j r c := fun r c hne => by
    simp only [perturbPrefix, Matrix.of_apply]
    by_cases hlt : (c : ℕ) * N + r < j
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]
  have hnew : ∀ (r c : Fin N), (c : ℕ) * N + r = j →
      perturbPrefix M γ A x (j + 1) r c = M.perturbWords γ A x r c := fun r c he => by
    simp only [perturbPrefix, Matrix.of_apply]
    rw [if_pos (by omega)]
  apply HoldsMatrix.of_get
  · intro r c
    by_cases he : (c : ℕ) * N + r = j
    · obtain ⟨rfl, rfl⟩ := hidx r c he
      rw [hnew _ _ he, he]
      exact hre
    · rw [hval r c he, hkeep _ (by omega) (by omega)]
      exact h.get_re r c
  · intro r c
    by_cases he : (c : ℕ) * N + r = j
    · obtain ⟨rfl, rfl⟩ := hidx r c he
      rw [hnew _ _ he, he]
      exact him
    · rw [hval r c he, hkeep _ (by omega) (by omega)]
      exact h.get_im r c

end Prefix

/-- `omega` after reducing the projections of literal pairs. -/
local macro "pomega" : tactic => `(tactic| ((try dsimp only) <;> omega))

section Steps

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O]

/-- A cell outside a block of a different buffer, or before or after it, is not in the block. -/
private theorem not_inBlock_of {b o n b' i : ℕ} (h : b' ≠ b ∨ i < o ∨ o + n ≤ i) :
    ¬ Store.inBlock b o n b' i := fun hi => by
  obtain ⟨h1, h2, h3⟩ := hi
  omega

/-- **The scale prelude** of `NLAlib.SmallEig.ginibrePerturb`: the index literal $N$, its rounded
square root, $\gamma' = \mathrm{fl}(\gamma/\mathrm{fl}(\sqrt N))$ in `Sc[0]`, and the stored
$\sqrt{1/2}$ in `Sc[1]`, written in the three cells of `Sc` only. -/
private theorem writes_scalePrelude {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {F : Fp} {P : Mem ℝ → Prop}
    {e : IExp} {N L : ℕ} {o₁ o₄ o₅ : Operand}
    {i₂ u₂ i₃ u₃ i₆ u₆ i₇ u₇ : List Operand} {next : Stmt O Q} {q : ℕ × ℕ} {γ : ℝ}
    (he : e.eval ρ.idx = some N) (h₁ : o₁.eval ρ = some (L + 1, 0))
    (h₂ : Operand.evalList ρ i₂ = some [(L + 1, 0)])
    (h₂' : Operand.evalList ρ u₂ = some [(L + 1, 0)])
    (h₃ : Operand.evalList ρ i₃ = some [q, (L + 1, 0)])
    (h₃' : Operand.evalList ρ u₃ = some [(L + 1, 0)]) (h₄ : o₄.eval ρ = some (L + 1, 1))
    (h₅ : o₅.eval ρ = some (L + 1, 2))
    (h₆ : Operand.evalList ρ i₆ = some [(L + 1, 1), (L + 1, 2)])
    (h₆' : Operand.evalList ρ u₆ = some [(L + 1, 1)])
    (h₇ : Operand.evalList ρ i₇ = some [(L + 1, 1)])
    (h₇' : Operand.evalList ρ u₇ = some [(L + 1, 1)])
    (hq : m.store.get q.1 q.2 = some γ) (hqL : q.1 < L + 1) (hlen : L + 1 < m.store.length)
    (hSc : m.store.len (L + 1) = 3) (hF : Store.inBlock (L + 1) 0 3 ≤ F)
    (hnext : ∀ m' : Mem ℝ, m.store.EqOff (Store.inBlock (L + 1) 0 3) m'.store → m'.pos = m.pos →
      m'.store.get (L + 1) 0 = some (M.div γ (M.sqrt (M.lit (N : ℚ)))) →
      m'.store.get (L + 1) 1 = some M.sqrtHalf → Writes .total I τ next ρ F P m') :
    Writes .total I τ
      (.seq (.call (Has.inj IndexOp.lit) [e] [] [o₁])
        (.seq (.call (Has.inj ScalarOp.sqrt) [] i₂ u₂)
          (.seq (.call (Has.inj ScalarOp.div) [] i₃ u₃)
            (.seq (.call (Has.inj (ScalarOp.lit 1)) [] [] [o₄])
              (.seq (.call (Has.inj (ScalarOp.lit 2)) [] [] [o₅])
                (.seq (.call (Has.inj ScalarOp.div) [] i₆ u₆)
                  (.seq (.call (Has.inj ScalarOp.sqrt) [] i₇ u₇) next))))))) ρ F P m := by
  have hsub : ∀ k < 3, Store.inBlock (L + 1) k 1 ≤ Store.inBlock (L + 1) 0 3 := fun k hk =>
    Fp.inBlock_le_inBlock (by pomega) (by pomega)
  have hle : ∀ k < 3, Store.inBlock (L + 1) k 1 ≤ F := fun k hk => (hsub k hk).trans hF
  refine (writes_indexLit hL (m := m) (τ := τ) he h₁ (by pomega)).seq_le (hle 0 (by pomega)) ?_
  rintro m₁ hf₁ ⟨hp₁, hg₁⟩
  refine (writes_call_un (hS .sqrt) h₂ h₂' trivial hg₁ rfl
    (by rw [hf₁.len_eq]; pomega)).seq_le (hle 0 (by pomega)) ?_
  rintro m₂ hf₂ ⟨hp₂, hg₂⟩
  have hq₂ : m₂.store.get q.1 q.2 = some γ := by
    rw [hf₂.2 _ _ (not_inBlock_of (by pomega)), hf₁.2 _ _ (not_inBlock_of (by pomega))]
    exact hq
  refine (writes_call_bin (hS .div) h₃ h₃' trivial hq₂ hg₂ rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true, and_self,
        hf₂.length_eq, hf₁.length_eq]; pomega,
      by rw [hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le (hle 0 (by pomega)) ?_
  rintro m₃ hf₃ ⟨hp₃, hg₃⟩
  refine (writes_call_const (hS (.lit 1)) h₄ trivial
    (by rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega)).seq_le (hle 1 (by pomega)) ?_
  rintro m₄ hf₄ ⟨hp₄, hg₄⟩
  refine (writes_call_const (hS (.lit 2)) h₅ trivial
    (by rw [hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega)).seq_le
    (hle 2 (by pomega)) ?_
  rintro m₅ hf₅ ⟨hp₅, hg₅⟩
  have hg₄' : m₅.store.get (L + 1) 1 = some (M.lit 1) := by
    rw [hf₅.2 _ _ (not_inBlock_of (by pomega))]
    exact hg₄
  have hlen₅ : m₅.store.length = m.store.length := by
    rw [hf₅.length_eq, hf₄.length_eq, hf₃.length_eq, hf₂.length_eq, hf₁.length_eq]
  have hSc₅ : m₅.store.len (L + 1) = 3 := by
    rw [hf₅.len_eq, hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq, hSc]
  refine (writes_call_bin (hS .div) h₆ h₆' trivial hg₄' hg₅ rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true, and_self]; pomega,
      by pomega⟩)).seq_le (hle 1 (by pomega)) ?_
  rintro m₆ hf₆ ⟨hp₆, hg₆⟩
  refine (writes_call_un (hS .sqrt) h₇ h₇' trivial hg₆ rfl
    (by rw [hf₆.len_eq]; pomega)).seq_le (hle 1 (by pomega)) ?_
  rintro m₇ hf₇ ⟨hp₇, hg₇⟩
  have hg₃' : m₇.store.get (L + 1) 0 = some (M.div γ (M.sqrt (M.lit (N : ℚ)))) := by
    rw [hf₇.2 _ _ (not_inBlock_of (by pomega)), hf₆.2 _ _ (not_inBlock_of (by pomega)),
      hf₅.2 _ _ (not_inBlock_of (by pomega)), hf₄.2 _ _ (not_inBlock_of (by pomega))]
    exact hg₃
  refine hnext m₇ ?_ (by rw [hp₇, hp₆, hp₅, hp₄, hp₃, hp₂, hp₁]) hg₃' hg₇
  exact ((((((hf₁.mono (hsub 0 (by pomega))).trans (hf₂.mono (hsub 0 (by pomega)))).trans
    (hf₃.mono (hsub 0 (by pomega)))).trans (hf₄.mono (hsub 1 (by pomega)))).trans
    (hf₅.mono (hsub 2 (by pomega)))).trans (hf₆.mono (hsub 1 (by pomega)))).trans
    (hf₇.mono (hsub 1 (by pomega)))

omit [Has IndexOp O] in
/-- **One entry of the perturbation loop**: with $\gamma'$ in `Sc[0]`, $\sqrt{1/2}$ in `Sc[1]` and
the words $w_0, w_1$ at `G[2j]`, `G[2j+1]`, the six calls store
$\mathrm{fl}(a_k + \mathrm{fl}(\mathrm{fl}(w_k\sqrt{1/2})\gamma'))$ at `A[2j + k]`, writing only
those cells and the two words of `G`. -/
private theorem writes_perturbEntry {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {L t zb zo : ℕ} {g h w₀ w₁ a₀ a₁ : ℝ}
    {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ i₅ u₅ i₆ u₆ : List Operand}
    (h₁ : Operand.evalList ρ i₁ = some [(L, t), (L + 1, 1)])
    (h₁' : Operand.evalList ρ u₁ = some [(L, t)])
    (h₂ : Operand.evalList ρ i₂ = some [(L, t + 1), (L + 1, 1)])
    (h₂' : Operand.evalList ρ u₂ = some [(L, t + 1)])
    (h₃ : Operand.evalList ρ i₃ = some [(L, t), (L + 1, 0)])
    (h₃' : Operand.evalList ρ u₃ = some [(L, t)])
    (h₄ : Operand.evalList ρ i₄ = some [(L, t + 1), (L + 1, 0)])
    (h₄' : Operand.evalList ρ u₄ = some [(L, t + 1)])
    (h₅ : Operand.evalList ρ i₅ = some [(zb, zo), (L, t)])
    (h₅' : Operand.evalList ρ u₅ = some [(zb, zo)])
    (h₆ : Operand.evalList ρ i₆ = some [(zb, zo + 1), (L, t + 1)])
    (h₆' : Operand.evalList ρ u₆ = some [(zb, zo + 1)])
    (hz : zb < L) (hlen : L + 1 < m.store.length) (htl : t + 2 ≤ m.store.len L)
    (hzl : zo + 2 ≤ m.store.len zb)
    (hg : m.store.get (L + 1) 0 = some g) (hh : m.store.get (L + 1) 1 = some h)
    (hw₀ : m.store.get L t = some w₀) (hw₁ : m.store.get L (t + 1) = some w₁)
    (ha₀ : m.store.get zb zo = some a₀) (ha₁ : m.store.get zb (zo + 1) = some a₁) :
    Writes .total I τ
      (.seq (.call (Has.inj ScalarOp.mul) [] i₁ u₁) (.seq (.call (Has.inj ScalarOp.mul) [] i₂ u₂)
        (.seq (.call (Has.inj ScalarOp.mul) [] i₃ u₃)
          (.seq (.call (Has.inj ScalarOp.mul) [] i₄ u₄)
            (.seq (.call (Has.inj ScalarOp.add) [] i₅ u₅)
              (.call (Has.inj ScalarOp.add) [] i₆ u₆)))))) ρ
      (Store.inBlock L t 2 ⊔ Store.inBlock zb zo 2)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get zb zo = some (M.add a₀ (M.mul (M.mul w₀ h) g)) ∧
        m'.store.get zb (zo + 1) = some (M.add a₁ (M.mul (M.mul w₁ h) g))) m := by
  have K : ∀ {s s' : Store ℝ} {b o b' i : ℕ} {v : ℝ}, s.EqOff (Store.inBlock b o 1) s' →
      (b' ≠ b ∨ i ≠ o) → s.get b' i = some v → s'.get b' i = some v :=
    fun hf hne hv => (hf.2 _ _ (not_inBlock_of (by pomega))).trans hv
  have hG : ∀ k < 2, Store.inBlock L (t + k) 1 ≤ Store.inBlock L t 2 ⊔ Store.inBlock zb zo 2 :=
    fun k hk => le_sup_of_le_left (Fp.inBlock_le_inBlock (by pomega) (by pomega))
  have hZ : ∀ k < 2, Store.inBlock zb (zo + k) 1 ≤
      Store.inBlock L t 2 ⊔ Store.inBlock zb zo 2 :=
    fun k hk => le_sup_of_le_right (Fp.inBlock_le_inBlock (by pomega) (by pomega))
  refine (writes_call_bin (hS .mul) h₁ h₁' trivial hw₀ hh rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true]; pomega, by pomega⟩)).seq_le
    (by simpa using hG 0 (by pomega)) ?_
  rintro m₁ hf₁ ⟨hp₁, hv₁⟩
  refine (writes_call_bin (hS .mul) h₂ h₂' trivial (K hf₁ (by pomega) hw₁) (K hf₁ (by pomega) hh)
    rfl (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true, hf₁.length_eq]; pomega, by
      rw [hf₁.len_eq]; pomega⟩)).seq_le (hG 1 (by pomega)) ?_
  rintro m₂ hf₂ ⟨hp₂, hv₂⟩
  refine (writes_call_bin (hS .mul) h₃ h₃' trivial (K hf₂ (by pomega) hv₁)
    (K hf₂ (by pomega) (K hf₁ (by pomega) hg)) rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true,
        hf₂.length_eq, hf₁.length_eq]; pomega, by
      rw [hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le (by simpa using hG 0 (by pomega)) ?_
  rintro m₃ hf₃ ⟨hp₃, hv₃⟩
  have hlen₃ : m₃.store.length = m.store.length :=
    hf₃.length_eq.trans (hf₂.length_eq.trans hf₁.length_eq)
  refine (writes_call_bin (hS .mul) h₄ h₄' trivial (K hf₃ (by pomega) hv₂)
    (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) hg))) rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true]; pomega, by
      rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le (hG 1 (by pomega)) ?_
  rintro m₄ hf₄ ⟨hp₄, hv₄⟩
  have ha₀' := K hf₄ (by pomega) (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) ha₀)))
  have ha₁' := K hf₄ (by pomega) (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) ha₁)))
  have hlen₄ : m₄.store.length = m.store.length := hf₄.length_eq.trans hlen₃
  refine (writes_call_bin (hS .add) h₅ h₅' trivial ha₀' (K hf₄ (by pomega) hv₃) rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true]; pomega, by
      rw [hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le
    (by simpa using hZ 0 (by pomega)) ?_
  rintro m₅ hf₅ ⟨hp₅, hv₅⟩
  refine (writes_call_bin (hS .add) h₆ h₆' trivial (K hf₅ (by pomega) ha₁')
    (K hf₅ (by pomega) hv₄) rfl
    (fun _ => ⟨by simp only [Mem.live_cons, Mem.live_nil, and_true, hf₅.length_eq]; pomega, by
      rw [hf₅.len_eq, hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega⟩)).mono
    (hZ 1 (by pomega)) ?_
  rintro m₆ hf₆ ⟨hp₆, hv₆⟩
  exact ⟨by rw [hp₆, hp₅, hp₄, hp₃, hp₂, hp₁], K hf₆ (by pomega) hv₅, hv₆⟩

omit [Has IndexOp O] in
/-- **The perturbation loop**: with $\gamma'$ in `Sc[0]`, $\sqrt{1/2}$ in `Sc[1]`, the words
$x_t$ at `G[t]` and $\mathbf{A}$ at `a`, the $N^2$ rounds store
`NLAlib.Ops.Machine.perturbWords` at `a`. -/
private theorem writes_perturbLoop {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {N L : ℕ} {n : IExp} {a : ℕ × ℕ} {γ : ℝ}
    {A : Matrix (Fin N) (Fin N) ℂ} {x : ℕ → ℝ}
    {i₁ u₁ i₂ u₂ i₃ u₃ i₄ u₄ i₅ u₅ i₆ u₆ : List Operand} (hn : n.eval ρ.idx = some (N * N))
    (h₁ : ∀ j, Operand.evalList (ρ.pushIdx j) i₁ = some [(L, 2 * j), (L + 1, 1)])
    (h₁' : ∀ j, Operand.evalList (ρ.pushIdx j) u₁ = some [(L, 2 * j)])
    (h₂ : ∀ j, Operand.evalList (ρ.pushIdx j) i₂ = some [(L, 2 * j + 1), (L + 1, 1)])
    (h₂' : ∀ j, Operand.evalList (ρ.pushIdx j) u₂ = some [(L, 2 * j + 1)])
    (h₃ : ∀ j, Operand.evalList (ρ.pushIdx j) i₃ = some [(L, 2 * j), (L + 1, 0)])
    (h₃' : ∀ j, Operand.evalList (ρ.pushIdx j) u₃ = some [(L, 2 * j)])
    (h₄ : ∀ j, Operand.evalList (ρ.pushIdx j) i₄ = some [(L, 2 * j + 1), (L + 1, 0)])
    (h₄' : ∀ j, Operand.evalList (ρ.pushIdx j) u₄ = some [(L, 2 * j + 1)])
    (h₅ : ∀ j, Operand.evalList (ρ.pushIdx j) i₅ = some [(a.1, a.2 + 2 * j), (L, 2 * j)])
    (h₅' : ∀ j, Operand.evalList (ρ.pushIdx j) u₅ = some [(a.1, a.2 + 2 * j)])
    (h₆ : ∀ j, Operand.evalList (ρ.pushIdx j) i₆ = some [(a.1, a.2 + 2 * j + 1), (L, 2 * j + 1)])
    (h₆' : ∀ j, Operand.evalList (ρ.pushIdx j) u₆ = some [(a.1, a.2 + 2 * j + 1)])
    (haL : a.1 < L) (hlen : m.store.length = L + 2) (hG : m.store.len L = 2 * (N * N))
    (hg : m.store.get (L + 1) 0 = some (M.div γ (M.sqrt (M.lit (N : ℚ)))))
    (hh : m.store.get (L + 1) 1 = some M.sqrtHalf)
    (hx : ∀ t < 2 * (N * N), m.store.get L t = some (x t)) (hA : HoldsMatrix a A m.store) :
    Writes .total I τ
      (.loop n (.seq (.call (Has.inj ScalarOp.mul) [] i₁ u₁)
        (.seq (.call (Has.inj ScalarOp.mul) [] i₂ u₂)
          (.seq (.call (Has.inj ScalarOp.mul) [] i₃ u₃)
            (.seq (.call (Has.inj ScalarOp.mul) [] i₄ u₄)
              (.seq (.call (Has.inj ScalarOp.add) [] i₅ u₅)
                (.call (Has.inj ScalarOp.add) [] i₆ u₆))))))) ρ
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (M.perturbWords γ A x) m'.store) m := by
  set F := Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L
  set Inv : ℕ → Mem ℝ → Prop := fun j μ => μ.pos = m.pos ∧ μ.store.length = L + 2 ∧
    μ.store.len L = 2 * (N * N) ∧ μ.store.get (L + 1) 0 = some (M.div γ (M.sqrt (M.lit (N : ℚ))))
    ∧ μ.store.get (L + 1) 1 = some M.sqrtHalf ∧
    (∀ t, 2 * j ≤ t → t < 2 * (N * N) → μ.store.get L t = some (x t)) ∧
    HoldsMatrix a (perturbPrefix M γ A x j) μ.store
  have hA0 : HoldsMatrix a (perturbPrefix M γ A x 0) m.store := by
    rw [perturbPrefix_zero]; exact hA
  refine (writes_loop (N := N * N) hn (fun _ => F) (fun _ _ => le_rfl) Inv
    ⟨rfl, hlen, hG, hg, hh, fun t _ ht => hx t ht, hA0⟩ ?_).mono le_rfl ?_
  · rintro j hj μ - ⟨hp, hl', hG', hg', hh', hx', hW⟩
    have hN : 0 < N := pos_of_lt_mul_self hj
    set r : Fin N := ⟨j % N, Nat.mod_lt _ hN⟩
    set c : Fin N := ⟨j / N, Nat.div_lt_of_lt_mul hj⟩
    have hjc : (c : ℕ) * N + r = j := Nat.div_add_mod' j N
    have hold : perturbPrefix M γ A x j r c = A r c := by
      simp only [perturbPrefix, Matrix.of_apply]
      rw [if_neg (by pomega)]
    have hroom := Store.le_len_of_readBlock hW (by positivity)
    have ha₀ := hW.get_re r c
    have ha₁ := hW.get_im r c
    rw [hold, hjc] at ha₀ ha₁
    refine (writes_perturbEntry hS (h₁ j) (h₁' j) (h₂ j) (h₂' j) (h₃ j) (h₃' j) (h₄ j) (h₄' j)
      (h₅ j) (h₅' j) (h₆ j) (h₆' j) haL (by pomega) (by pomega) (by pomega) hg' hh'
      (hx' _ le_rfl (by pomega)) (hx' _ (by pomega) (by pomega)) ha₀ ha₁).mono
      (sup_le (fun b i hi => Or.inr (hi.1 ▸ le_rfl))
        (le_sup_of_le_left (Fp.inBlock_le_inBlock (by pomega) (by pomega)))) ?_
    rintro μ' hf ⟨hp', hv₀, hv₁⟩
    have hk : ∀ b i, b < L → (b ≠ a.1 ∨ i < a.2 + 2 * j ∨ a.2 + 2 * j + 2 ≤ i) →
        μ'.store.get b i = μ.store.get b i := fun b i hb hne =>
      hf.2 b i (fun hi => hi.elim (fun h => by obtain ⟨h1, h2, h3⟩ := h; pomega)
        (fun h => by obtain ⟨h1, h2, h3⟩ := h; pomega))
    have hkL : ∀ b i, L ≤ b → (b ≠ L ∨ i < 2 * j ∨ 2 * j + 2 ≤ i) →
        μ'.store.get b i = μ.store.get b i := fun b i hb hne =>
      hf.2 b i (fun hi => hi.elim (fun h => by obtain ⟨h1, h2, h3⟩ := h; pomega)
        (fun h => by obtain ⟨h1, h2, h3⟩ := h; pomega))
    refine ⟨hp'.trans hp, hf.length_eq.trans hl', (hf.len_eq L).trans hG',
      (hkL _ _ (by pomega) (by pomega)).trans hg', (hkL _ _ (by pomega) (by pomega)).trans hh',
      fun t ht ht' => (hkL _ _ le_rfl (by pomega)).trans (hx' t (by pomega) ht'), ?_⟩
    refine holdsMatrix_perturbPrefix_succ hj hW (fun i h1 h2 => hk _ _ haL (by pomega)) ?_ ?_
    · rw [perturbWords_apply_divMod M γ A x hj]
      exact hv₀
    · rw [perturbWords_apply_divMod M γ A x hj]
      exact hv₁
  · rintro μ - ⟨hp, -, -, -, -, -, hW⟩
    exact ⟨hp, perturbPrefix_all M γ A x ▸ hW⟩

end Steps


section Class

/-- A sample position of an $N \times N$ matrix, column-major with two real draws per entry, is
in the window of $2N^2$ draws. -/
private theorem tapePos_lt {N : ℕ} (i j : Fin N) (t : ℕ) (ht : t < 2) :
    2 * ((i : ℕ) + N * j) + t < 2 * (N * N) := by
  have h : (i : ℕ) + N * j < N * N :=
    calc (i : ℕ) + N * j < N + N * j := Nat.add_lt_add_right i.isLt _
      _ = N * (j + 1) := by ring
      _ ≤ N * N := Nat.mul_le_mul_left _ j.isLt
  omega

/-- The complex matrix of a window of $2N^2$ real draws, entry $(i, j)$ equal to
$(x_{2(i + Nj)} + i\,x_{2(i + Nj) + 1})/\sqrt2$ (`NLAlib.Computation.tapeComplexMatrix` on the
window). -/
private noncomputable def winMat (N : ℕ) (x : Fin (2 * (N * N)) → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ⟨x ⟨2 * (i + N * j), tapePos_lt i j 0 (by norm_num)⟩ / √2,
    x ⟨2 * (i + N * j) + 1, tapePos_lt i j 1 (by norm_num)⟩ / √2⟩

/-- The matrix of a tape window is the matrix the program draws. -/
private theorem winMat_windowFn (N : ℕ) (τ : Tape ℝ) (s p : ℕ) :
    winMat N (Tape.windowFn τ s p (2 * (N * N))) =
      Computation.tapeComplexMatrix (fun j => τ (p + j) s) N := rfl

/-- The matrix of a window is measurable in the window. -/
private theorem measurable_winMat (N : ℕ) : Measurable (winMat N) := by
  have hpair : Measurable fun v : ℝ × ℝ => (⟨v.1, v.2⟩ : ℂ) :=
    Complex.measurableEquivRealProd.symm.measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact hpair.comp (f := fun x => ((winMat N x i j).re, (winMat N x i j).im))
    (((measurable_pi_apply (⟨2 * (i + N * j), tapePos_lt i j 0 (by norm_num)⟩ :
        Fin (2 * (N * N)))).div_const _).prodMk
      ((measurable_pi_apply (⟨2 * (i + N * j) + 1, tapePos_lt i j 1 (by norm_num)⟩ :
        Fin (2 * (N * N)))).div_const _))

/-- The matrix of a window of independent standard real Gaussian draws is a standard complex
Gaussian matrix. -/
private theorem hasLaw_winMat (N : ℕ) :
    HasLaw (winMat N) (complexGaussianMatrix (Fin N) (Fin N))
      (Measure.pi fun _ : Fin (2 * (N * N)) => gaussianReal 0 1) := by
  set g : (Fin N × Fin N) × Fin 2 → Fin (2 * (N * N)) := fun p =>
    ⟨2 * (p.1.1 + N * p.1.2) + p.2.1, tapePos_lt p.1.1 p.1.2 p.2.1 p.2.isLt⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨i, j⟩, t⟩ ⟨⟨i', j'⟩, t'⟩ h
    simp only [g, Fin.mk.injEq] at h
    have ht : t.1 = t'.1 := by omega
    have h' : i.1 + N * j.1 = i'.1 + N * j'.1 := by omega
    obtain ⟨h1, h2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.2 i'.2).mp h'
    exact Prod.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)) (Fin.ext ht)
  have hind := (iIndepFun_pi (μ := fun _ : Fin (2 * (N * N)) => gaussianReal 0 1)
    (X := fun _ (y : ℝ) => y) fun _ => aemeasurable_id).precomp hg
  have hY := hind.hasLaw_pi fun p =>
    ⟨(measurable_pi_apply (g p)).aemeasurable, (measurePreserving_eval _ (g p)).map_eq⟩
  have hX := Computation.hasLaw_tapeComplexMatrix_of_hasLaw_pi
    (x := fun (ω : Fin (2 * (N * N)) → ℝ) (k : ℕ) =>
      if h : k < 2 * (N * N) then ω ⟨k, h⟩ else 0) (n := N) (by
      convert hY using 2 with ω
      funext p
      simp only [g, dif_pos (tapePos_lt p.1.1 p.1.2 p.2.1 p.2.isLt)])
  convert hX using 2 with ω
  ext i j
  have h0 : 2 * ((i : ℕ) + N * j) < 2 * (N * N) := by simpa using tapePos_lt i j 0 (by norm_num)
  simp only [winMat, Computation.tapeComplexMatrix, Matrix.of_apply, dif_pos h0,
    dif_pos (tapePos_lt i j 1 (by norm_num))]

/-- The class of the order $N$ with condition at most $B$ and separation at least $g$, the
closed set `NLAlib.isClosed_setOf_exists_pseudoConditionNumber_le_and_le_norm_sub`. -/
private def classSet (n : ℕ) (B g : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
  {A | ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
    A * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B ∧
      ∀ i j, i ≠ j → g ≤ ‖d i - d j‖}

/-- The scale and the noise level: $\gamma > 0$ and $\gamma W = \delta/4$. -/
private theorem smallEigScale_spec {δ φ : ℝ} (hδ : 0 < δ) :
    0 < smallEigScale δ φ ∧ smallEigScale δ φ * smallEigNoiseLevel φ = δ / 4 := by
  have hW : 0 < smallEigNoiseLevel φ := by
    unfold smallEigNoiseLevel
    positivity
  refine ⟨div_pos hδ (by positivity), ?_⟩
  unfold smallEigScale
  field_simp

/-- The failure $\varphi/(4 \cdot 2^{\bar c_1})$ at which the gap threshold is inverted is in
$(0, 1]$. -/
private theorem gapFailure_mem {c₁ : PolyLogTail} {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < φ / (4 * 2 ^ c₁.normalize.c) ∧ φ / (4 * 2 ^ c₁.normalize.c) ≤ 1 := by
  have h2c : (1 : ℝ) ≤ 2 ^ c₁.normalize.c := Real.one_le_rpow (by norm_num) (le_max_right _ _)
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith

/-- **The thresholds of the perturbation**: $0 < t_1 \le \gamma/2$ and $0 < t_2 \le 1$ for
$t_1, t_2$ = `NLAlib.SmallEig.smallEigGap`, `NLAlib.SmallEig.smallEigCond` and $\gamma$ =
`NLAlib.SmallEig.smallEigScale`. -/
private theorem perturbThresholds {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) :
    0 < smallEigGap nmax S δ φ c₁ ∧ smallEigGap nmax S δ φ c₁ ≤ smallEigScale δ φ / 2 ∧
      0 < smallEigCond nmax S δ φ c₂ ∧ smallEigCond nmax S δ φ c₂ ≤ 1 := by
  obtain ⟨hγ, -⟩ := smallEigScale_spec (φ := φ) hδ
  obtain ⟨hφ₁, hφ₁1⟩ := gapFailure_mem (c₁ := c₁) hφ hφ1
  obtain ⟨h1p, h1le, -⟩ := ginibreClass_spec (c₂ := c₂) hb₁ hb₂ hn (S := S) (by linarith)
    (by positivity : 0 < smallEigScale δ φ / 2) hφ₁ hφ₁1
  obtain ⟨-, -, h2p, h2le, -⟩ := ginibreClass_spec (c₁ := c₁) hb₁ hb₂ hn (S := S) (by linarith)
    (by positivity : 0 < smallEigScale δ φ / 2) (by positivity : 0 < φ / 4) (by linarith)
  exact ⟨h1p, h1le, h2p, h2le⟩

/-- **The gap tail at the program's scale**: at the scale $\gamma$ =
`NLAlib.SmallEig.smallEigScale` and the threshold $t_1$ = `NLAlib.SmallEig.smallEigGap`
(inverted at the scale $\gamma/2$ and the failure $\varphi/(4 \cdot 2^{\bar c_1})$), for every
order $1 \le N \le n_{\max}$ and norm $0 \le a \le \Sigma$, the normalized gap tail of
`NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix` is at most
$\varphi/4$: halving the scale costs at most the factor $2^{\bar c_1}$. -/
private theorem gapTail_le {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) {N : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ nmax) {a : ℝ} (ha0 : 0 ≤ a) (haS : a ≤ S) :
    c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a *
        (smallEigGap nmax S δ φ c₁ / smallEigScale δ φ) ^ c₁.normalize.b *
        ((a + 4 * smallEigScale δ φ) / smallEigScale δ φ +
          Real.log (smallEigScale δ φ / smallEigGap nmax S δ φ c₁)) ^ c₁.normalize.c ≤ φ / 4 := by
  obtain ⟨hγ, -⟩ := smallEigScale_spec (φ := φ) hδ
  obtain ⟨hφ₁, hφ₁1⟩ := gapFailure_mem (c₁ := c₁) hφ hφ1
  obtain ⟨h1p, h1le, -, -⟩ := perturbThresholds (c₂ := c₂) hb₁ hb₂ hn hδ hδS hφ hφ1
  obtain ⟨-, -, -, -, h1t, -⟩ := ginibreClass_spec (c₂ := c₂) hb₁ hb₂ hn (S := S) (by linarith)
    (by positivity : 0 < smallEigScale δ φ / 2) hφ₁ hφ₁1
  obtain ⟨h1, -⟩ := h1t N hN1 hNn
  set γ := smallEigScale δ φ
  change c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a * (smallEigGap nmax S δ φ c₁ / (γ / 2)) ^
      c₁.normalize.b * ((S + 4 * (γ / 2)) / (γ / 2) +
        Real.log ((γ / 2) / smallEigGap nmax S δ φ c₁)) ^ c₁.normalize.c ≤
      φ / (4 * 2 ^ c₁.normalize.c) at h1
  set t₁ := smallEigGap nmax S δ φ c₁
  have hγh : 0 < γ / 2 := by positivity
  have hc₁ : 0 ≤ c₁.normalize.c := le_max_right _ _
  have hC₁ : 0 ≤ c₁.normalize.C := zero_le_one.trans (le_max_right _ _)
  have hNa₁ : 0 ≤ (N : ℝ) ^ c₁.normalize.a := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hL₁ : 0 ≤ Real.log ((γ / 2) / t₁) := Real.log_nonneg ((one_le_div h1p).mpr h1le)
  have hlog : Real.log (γ / t₁) = Real.log 2 + Real.log ((γ / 2) / t₁) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK0 : 0 ≤ (a + 4 * γ) / γ := by positivity
  have e1 : (a + 4 * γ) / γ = a / γ + 4 := by field_simp
  have e2 : (S + 4 * (γ / 2)) / (γ / 2) = 2 * (S / γ) + 4 := by field_simp
  have haγ : a / γ ≤ S / γ := div_le_div_of_nonneg_right haS hγ.le
  have hSγ : 0 ≤ S / γ := div_nonneg (by linarith) hγ.le
  have hbase : (a + 4 * γ) / γ + Real.log (γ / t₁) ≤
      2 * ((S + 4 * (γ / 2)) / (γ / 2) + Real.log ((γ / 2) / t₁)) := by
    rw [hlog, e1, e2]
    linarith
  have hpow : ((a + 4 * γ) / γ + Real.log (γ / t₁)) ^ c₁.normalize.c ≤
      2 ^ c₁.normalize.c *
        ((S + 4 * (γ / 2)) / (γ / 2) + Real.log ((γ / 2) / t₁)) ^ c₁.normalize.c := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hbase hc₁
  have hrp : (t₁ / γ) ^ c₁.normalize.b ≤ (t₁ / (γ / 2)) ^ c₁.normalize.b :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left h1p.le hγh (by linarith)) hb₁.le
  have hb0 := Real.rpow_nonneg (by linarith : 0 ≤ (a + 4 * γ) / γ + Real.log (γ / t₁))
    c₁.normalize.c
  calc c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a * (t₁ / γ) ^ c₁.normalize.b *
        ((a + 4 * γ) / γ + Real.log (γ / t₁)) ^ c₁.normalize.c
      ≤ c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a * (t₁ / (γ / 2)) ^ c₁.normalize.b *
        (2 ^ c₁.normalize.c *
          ((S + 4 * (γ / 2)) / (γ / 2) + Real.log ((γ / 2) / t₁)) ^ c₁.normalize.c) := by
        gcongr
    _ = 2 ^ c₁.normalize.c * (c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a *
        (t₁ / (γ / 2)) ^ c₁.normalize.b *
          ((S + 4 * (γ / 2)) / (γ / 2) + Real.log ((γ / 2) / t₁)) ^ c₁.normalize.c) := by ring
    _ ≤ 2 ^ c₁.normalize.c * (φ / (4 * 2 ^ c₁.normalize.c)) := by gcongr
    _ = φ / 4 := by field_simp

/-- **The condition tail at the program's scale**: as `gapTail_le`, the normalized condition tail
at the scale $\gamma$ and the threshold $t_2$ = `NLAlib.SmallEig.smallEigCond` is at most
$\varphi/4$. -/
private theorem condTail_le {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) {N : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ nmax) {a : ℝ} (ha0 : 0 ≤ a) (haS : a ≤ S) :
    c₂.normalize.C * (N : ℝ) ^ c₂.normalize.a * smallEigCond nmax S δ φ c₂ ^ c₂.normalize.b *
        ((a + 4 * smallEigScale δ φ) / smallEigScale δ φ +
          Real.log (smallEigCond nmax S δ φ c₂)⁻¹) ^ c₂.normalize.c ≤ φ / 4 := by
  obtain ⟨hγ, -⟩ := smallEigScale_spec (φ := φ) hδ
  obtain ⟨-, -, h2p, h2le⟩ := perturbThresholds (c₁ := c₁) hb₁ hb₂ hn hδ hδS hφ hφ1
  obtain ⟨-, -, -, -, h2t, -⟩ := ginibreClass_spec (c₁ := c₁) hb₁ hb₂ hn (S := S) (by linarith)
    (by positivity : 0 < smallEigScale δ φ / 2) (by positivity : 0 < φ / 4) (by linarith)
  obtain ⟨-, h2⟩ := h2t N hN1 hNn
  set γ := smallEigScale δ φ
  change c₂.normalize.C * (N : ℝ) ^ c₂.normalize.a * smallEigCond nmax S δ φ c₂ ^
      c₂.normalize.b * ((S + 4 * (γ / 2)) / (γ / 2) +
        Real.log (smallEigCond nmax S δ φ c₂)⁻¹) ^ c₂.normalize.c ≤ φ / 4 at h2
  refine le_trans ?_ h2
  have hγh : 0 < γ / 2 := by positivity
  have hK : (a + 4 * γ) / γ ≤ (S + 4 * (γ / 2)) / (γ / 2) := by
    rw [div_le_div_iff₀ hγ hγh]
    nlinarith
  have hL₂ : 0 ≤ Real.log (smallEigCond nmax S δ φ c₂)⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ h2p).mpr h2le)
  have : ((a + 4 * γ) / γ + Real.log (smallEigCond nmax S δ φ c₂)⁻¹) ^ c₂.normalize.c ≤
      ((S + 4 * (γ / 2)) / (γ / 2) + Real.log (smallEigCond nmax S δ φ c₂)⁻¹) ^ c₂.normalize.c :=
    Real.rpow_le_rpow (by positivity) (by linarith) (le_max_right _ _)
  have := Real.rpow_nonneg h2p.le c₂.normalize.b
  have := Real.rpow_nonneg (Nat.cast_nonneg N) c₂.normalize.a
  have : 0 ≤ c₂.normalize.C := zero_le_one.trans (le_max_right _ _)
  gcongr

/-- **The class after the rounding** of the perturbation: if the exact perturbation
$\mathbf{A} + \beta\mathbf{G}$ is in the class (condition $t_2^{-1}$, separation $t_1$), the noise
has norm at most $\delta/4$ and the computed $\widehat{\mathbf{A}}$ is within
$r \le \min(\delta/4, t_1 t_2/(16(n + 1)))$ of it, then $\widehat{\mathbf{A}} = \mathbf{A} +
\mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta/2$ and $\widehat{\mathbf{A}}$ is in the class
(condition $2/t_2$, separation $t_1/2$). -/
private theorem perturb_class {n : ℕ} {A Ahat G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {β δ r t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hcl : A + β • G ∈ classSet n t₂⁻¹ t₁) (hnoise : specNorm (β • G) ≤ δ / 4)
    (hround : specNorm (Ahat - (A + β • G)) ≤ r) (hrδ : r ≤ δ / 4)
    (hrc : r ≤ t₁ / (16 * (n + 1) * t₂⁻¹)) :
    ∃ (E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
      Ahat = A + E ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧ (A + E) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ 2 / t₂ ∧ ∀ i j, i ≠ j → t₁ / 2 ≤ ‖d i - d j‖ := by
  obtain ⟨V, d, hV, hAV, hκ, hgap⟩ := hcl
  obtain ⟨V', d', hV', hAV', hκ', hgap'⟩ := exists_pseudoConditionNumber_le_and_le_norm_sub
    (E := Ahat - (A + β • G)) hV hAV hκ ht₁ hgap (hround.trans hrc)
  have hE : A + (Ahat - A) = Ahat := add_sub_cancel _ _
  have hsum : A + β • G + (Ahat - (A + β • G)) = Ahat := add_sub_cancel _ _
  refine ⟨Ahat - A, V', d', hE.symm, ?_, hV', by rw [hE, ← hsum]; exact hAV', ?_, fun i j hij => ?_⟩
  · have e : Ahat - A = β • G + (Ahat - (A + β • G)) := by abel
    rw [e]
    linarith [specNorm_add_le (β • G) (Ahat - (A + β • G))]
  · rw [div_eq_mul_inv]
    exact hκ'
  · have h := hgap' i j hij
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hr' : 2 * t₂⁻¹ * specNorm (Ahat - (A + β • G)) ≤ t₁ / 2 := by
      have h1 := hround.trans hrc
      have e : t₁ / (16 * (n + 1) * t₂⁻¹) = t₁ * t₂ / (16 * (n + 1)) := by field_simp
      rw [e] at h1
      have h2 : 2 * t₂⁻¹ * (t₁ * t₂ / (16 * (n + 1))) = t₁ / (8 * (n + 1)) := by
        field_simp; ring
      have h3 : t₁ / (8 * (n + 1)) ≤ t₁ / 2 :=
        div_le_div_of_nonneg_left ht₁.le (by norm_num) (by nlinarith)
      calc 2 * t₂⁻¹ * specNorm (Ahat - (A + β • G))
          ≤ 2 * t₂⁻¹ * (t₁ * t₂ / (16 * (n + 1))) := by gcongr
        _ ≤ t₁ / 2 := h2 ▸ h3
    linarith

/-- **The precision of the perturbation**: under the standard model at
$\boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEigReduce`, $0 \le \boldsymbol{u} \le 1/100$ and, for
an order $n + 1 \le n_{\max}$ and $0 \le X \le 2\Sigma$, the rounding bound
$20(n + 1)\boldsymbol{u}X$ is at most $\delta/8$ and at most $t_1/(16(n + 1)t_2^{-1})$. -/
private theorem perturbPrecision {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} {S δ φ : ℝ}
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEigReduce nmax S δ φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ nmax) :
    0 ≤ u ∧ u ≤ 1 / 100 ∧ ∀ X : ℝ, 0 ≤ X → X ≤ 2 * S →
      20 * ((n + 1 : ℕ) : ℝ) * u * X ≤ δ / 8 ∧
        20 * ((n + 1 : ℕ) : ℝ) * u * X ≤
          smallEigGap nmax S δ φ c₁ / (16 * (n + 1) * (smallEigCond nmax S δ φ c₂)⁻¹) := by
  obtain ⟨ht₁p, -, ht₂p, -⟩ := perturbThresholds (c₁ := c₁) (c₂ := c₂) hb₁ hb₂
    (le_trans (Nat.le_add_left 1 n) hn) hδ hδS hφ hφ1
  set t₁ := smallEigGap nmax S δ φ c₁
  set t₂ := smallEigCond nmax S δ φ c₂
  have hSpos : 0 < S := hδ.trans_le hδS
  have hu0 : 0 ≤ u := by
    have := hM.lit 1
    simp only [id, Rat.cast_one, abs_one, mul_one] at this
    exact (abs_nonneg _).trans this
  set m₀ := min (δ / 8) (t₁ / (64 * ((nmax : ℝ) + 1) * (2 / t₂)))
  have hD : 0 < 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) := by positivity
  have huD : u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) ≤ m₀ := by
    have := hu
    unfold uSmallEigReduce at this
    exact (le_div_iff₀ hD).mp this
  have hm₀δ : m₀ ≤ δ / 8 := min_le_left _ _
  have hm₀c : m₀ ≤ t₁ / (64 * ((nmax : ℝ) + 1) * (2 / t₂)) := min_le_right _ _
  have hnmax : ((n + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hn
  have hnm0 : (0 : ℝ) ≤ nmax := Nat.cast_nonneg _
  have hsq1 : (nmax : ℝ) + 1 ≤ ((nmax : ℝ) + 1) ^ 2 := by nlinarith only [hnm0]
  have hrc : m₀ ≤ t₁ / (16 * (n + 1) * t₂⁻¹) := by
    refine hm₀c.trans (div_le_div_of_nonneg_left ht₁p.le (by positivity) ?_)
    have : ((n : ℝ) + 1) ≤ nmax := by exact_mod_cast hn
    rw [div_eq_mul_inv]
    have ht := inv_pos.mpr ht₂p
    have hn1 : (16 : ℝ) * (n + 1) ≤ 64 * ((nmax : ℝ) + 1) * 2 := by linarith only [this, hnm0]
    nlinarith only [hn1, ht]
  refine ⟨hu0, ?_, fun X hX0 hX => ?_⟩
  · have h2 : u * (2000 * S) ≤ u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hsq1, hnm0, hSpos]) hu0
    nlinarith only [h2, huD, hm₀δ, hSpos, hδS]
  have h20 : (20 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ 1000 * ((nmax : ℝ) + 1) ^ 2 := by
    linarith only [hnmax, hsq1, hnm0]
  have hr : 20 * ((n + 1 : ℕ) : ℝ) * u * X ≤ m₀ :=
    calc 20 * ((n + 1 : ℕ) : ℝ) * u * X ≤ 1000 * ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) := by
          gcongr
      _ = u * (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S)) := by ring
      _ ≤ m₀ := huD
  exact ⟨hr.trans hm₀δ, hr.trans hrc⟩

/-- The norm threshold of the noise, $\gamma(2\sqrt2 + \sqrt{\log(4/\varphi)/N})$, is at most
$\gamma W = \delta/4$ for $N \ge 1$. -/
private theorem perturbNoise_le {δ φ : ℝ} (hδ : 0 < δ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) {N : ℕ}
    (hN1 : 1 ≤ N) :
    smallEigScale δ φ * (2 * √2 + √(Real.log (φ / 4)⁻¹ / N)) ≤ δ / 4 := by
  obtain ⟨hγ, hγW⟩ := smallEigScale_spec (φ := φ) hδ
  rw [← hγW]
  unfold smallEigNoiseLevel
  rw [inv_div]
  have hs : √(Real.log (4 / φ) / N) ≤ √(Real.log (4 / φ)) :=
    Real.sqrt_le_sqrt (div_le_self (Real.log_nonneg (by rw [le_div_iff₀ hφ]; linarith))
      (by exact_mod_cast hN1))
  have h22 : 2 * √2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  exact mul_le_mul_of_nonneg_left (by linarith) hγ.le

/-- The bad windows of the perturbation: the exact perturbation $\mathbf{A} + \beta\mathbf{G}$
of the window's matrix is outside the class (condition $t_2^{-1}$, separation $t_1$), or the
noise $\beta\mathbf{G}$ has norm at least `thr`. -/
private def perturbBad {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (β t₁ t₂ thr : ℝ) :
    Set (Fin (2 * ((n + 1) * (n + 1))) → ℝ) :=
  {x | A + β • winMat (n + 1) x ∉ classSet n t₂⁻¹ t₁} ∪
    {x | thr ≤ specNorm (β • winMat (n + 1) x)}

/-- The bad windows are measurable: the class is closed. -/
private theorem measurableSet_perturbBad {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (β t₁ t₂ thr : ℝ) : MeasurableSet (perturbBad A β t₁ t₂ thr) := by
  have hβ := (measurable_winMat (n + 1)).const_smul β
  exact ((isClosed_setOf_exists_pseudoConditionNumber_le_and_le_norm_sub n t₂⁻¹
    t₁).measurableSet.preimage (measurable_const.add hβ)).compl.union
    (measurableSet_le measurable_const (continuous_specNorm.measurable.comp hβ))

/-- **The probability of the bad windows**: under independent standard real Gaussian draws, at
the scale $\gamma$ = `NLAlib.SmallEig.smallEigScale`, $\beta = \gamma/\sqrt{n + 1}$, the
thresholds $t_1, t_2$ and the noise threshold of
`NLAlib.measureReal_specNorm_ge_mul_le_of_hasLaw_complexGaussianMatrix` at $\varphi/4$,
the bad windows have probability at most $3\varphi/4$: the two class tails
(`NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix`) and the norm tail. -/
private theorem measureReal_perturbBad_le {c₁ c₂ : PolyLogTail} (hA : ComplexGaussianGapTail c₁)
    (hB : ComplexGaussianConditionTail c₂) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) {n : ℕ}
    (hn : n + 1 ≤ nmax) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hAS : specNorm A ≤ S) :
    (Measure.pi fun _ : Fin (2 * ((n + 1) * (n + 1))) => gaussianReal 0 1).real
      (perturbBad A (smallEigScale δ φ / √((n + 1 : ℕ) : ℝ)) (smallEigGap nmax S δ φ c₁)
        (smallEigCond nmax S δ φ c₂)
        (smallEigScale δ φ * (2 * √2 + √(Real.log (φ / 4)⁻¹ / ((n + 1 : ℕ) : ℝ))))) ≤
      3 * φ / 4 := by
  have hN1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hnm : 1 ≤ nmax := le_trans hN1 hn
  obtain ⟨hγ, -⟩ := smallEigScale_spec (φ := φ) hδ
  obtain ⟨ht₁p, ht₁le, ht₂p, ht₂le⟩ := perturbThresholds (c₁ := c₁) (c₂ := c₂) hb₁ hb₂ hnm hδ
    hδS hφ hφ1
  have hlaw := hasLaw_winMat (n + 1)
  have h1 := measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix hA hB hlaw A hγ
    ht₁p (by linarith) ht₂p ht₂le
  have h2 := measureReal_specNorm_ge_mul_le_of_hasLaw_complexGaussianMatrix hlaw hγ
    (by positivity : 0 < φ / 4) (by linarith)
  simp only [Fintype.card_fin] at h1 h2
  have h3 := gapTail_le (c₂ := c₂) hb₁ hb₂ hnm hδ hδS hφ hφ1 hN1 hn (specNorm_nonneg A) hAS
  have h4 := condTail_le (c₁ := c₁) hb₁ hb₂ hnm hδ hδS hφ hφ1 hN1 hn (specNorm_nonneg A) hAS
  refine (measureReal_union_le _ _).trans ?_
  set β := smallEigScale δ φ / √((n + 1 : ℕ) : ℝ)
  have e1 : (Measure.pi fun _ : Fin (2 * ((n + 1) * (n + 1))) => gaussianReal 0 1).real
      {x | A + β • winMat (n + 1) x ∉
        classSet n (smallEigCond nmax S δ φ c₂)⁻¹ (smallEigGap nmax S δ φ c₁)} ≤ φ / 4 + φ / 4 :=
    h1.trans (add_le_add h3 h4)
  have e2 : (Measure.pi fun _ : Fin (2 * ((n + 1) * (n + 1))) => gaussianReal 0 1).real
      {x | smallEigScale δ φ * (2 * √2 + √(Real.log (φ / 4)⁻¹ / ((n + 1 : ℕ) : ℝ))) ≤
        specNorm (β • winMat (n + 1) x)} ≤ φ / 4 := h2
  linarith

end Class

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]

/-- `NLAlib.SmallEig.ginibrePerturb` on a scalar machine with index literals and draws that store
the tape entry: from $\mathbf{A}$ of order $N$ at `a` and the word $\gamma$ at `q`, apart, it
writes only the matrix, advances the position by $2N^2$, and stores
`NLAlib.Ops.Machine.perturbWords` $\gamma$ $\mathbf{A}$ of the $2N^2$ entries of the stream `sG`
at the start position. -/
theorem ginibrePerturb_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hSmp : IsSample I) {sG N nq : ℕ} {τ : Tape ℝ} {μ : Mem ℝ}
    {a q : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {γ : ℝ} (hl : μ.Live [a, q])
    (hA : HoldsMatrix a A μ.store) (hq : μ.store.get q.1 q.2 = some γ) :
    Writes .total I τ (ginibrePerturb (O := O) (Q := Q) sG).body (Env.frame [N, nq] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos + 2 * (N * N) ∧
        HoldsMatrix a (M.perturbWords γ A fun j => τ (μ.pos + j) sG) μ'.store) μ := by
  have hal : a.1 < μ.store.length := hl a (by simp)
  have hql : q.1 < μ.store.length := hl q (by simp)
  unfold ginibrePerturb
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 3] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * (N * N), 3]) rfl
    (fun hBelow ⟨hp, hW⟩ => ⟨hp, hW.of_below hBelow hal⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hG : s₁.len L = 2 * (N * N) := by simpa using hlens 0 (by simp)
  have hSc : s₁.len (L + 1) = 3 := by simpa using hlens 1 (by simp)
  have hab : ∀ b o n, L ≤ b →
      Store.inBlock b o n ≤ Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Fp.above L :=
    fun b o n hb _ _ hi => Or.inr (hi.1 ▸ hb)
  refine (gaussDraws_writes (O := O) (Q := Q) hSmp (sG := sG) (m := 2 * (N * N)) (τ := τ)
    (μ := ⟨s₁, μ.pos⟩) (g := (L, 0)) (by simp only [Mem.live_cons, Mem.live_nil, and_true]; pomega)
    (by simp [hG])).frame_seq_le
    rfl rfl (by simp only [Mem.live_cons, Mem.live_nil, and_true]; pomega) (hab _ _ _ le_rfl) ?_
  rintro m₁ hf₁ ⟨hp₁, hr₁⟩
  have hq₁ : m₁.store.get q.1 q.2 = some γ :=
    (hf₁.2 _ _ (not_inBlock_of (by pomega))).trans (hBelow.get_of hql hq)
  refine writes_scalePrelude hS hL rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hq₁
    (by pomega) (by rw [hf₁.length_eq]; pomega) (by rw [hf₁.len_eq]; exact hSc)
    (hab _ _ _ (by pomega)) ?_
  intro m₂ hf₂ hp₂ hg₂ hh₂
  have hx₂ : ∀ t < 2 * (N * N), m₂.store.get L t = some (τ (μ.pos + t) sG) := fun t ht => by
    rw [hf₂.2 _ _ (not_inBlock_of (by pomega))]
    simpa [Tape.window, ht] using Store.get_of_readBlock hr₁ ht (0 : ℝ)
  have hA₂ : HoldsMatrix a A m₂.store :=
    ((hA.of_below hBelow hal).of_eqOff hf₁ (Fp.disj_inBlock_of_ne (by pomega))).of_eqOff hf₂
      (Fp.disj_inBlock_of_ne (by pomega))
  refine (writes_perturbLoop hS rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (by pomega) (by rw [hf₂.length_eq, hf₁.length_eq]; exact hlen)
    (by rw [hf₂.len_eq, hf₁.len_eq]; exact hG) hg₂ hh₂ hx₂ hA₂).mono le_rfl ?_
  rintro μ' - ⟨hp', hW'⟩
  exact ⟨by rw [hp', hp₂, hp₁], hW'⟩

/-- **The perturbation is in the class** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], the
perturbation step, with Lemma 6.5 replaced by the class): on a scalar machine with the standard
model at $\boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEigReduce`, index literals, a measurable
interpretation reading the tape only in its windows whose draws store the tape entry, a stream
`sG` with the standard real Gaussian law, and the random-matrix tails $c_1$ (gap) and $c_2$
(condition) with $b_1, b_2 > 0$: let $1 \le n_{\max}$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$, $\mathbf{A}$ of order $n + 1 \le n_{\max}$ with $\|\mathbf{A}\|_2 \le \Sigma$,
stored at `a`, and the words `NLAlib.SmallEig.smallEigParams` at `q`, apart. Then, except with
probability at most $3\varphi/4$, the run writes only the matrix and stores
$\widehat{\mathbf{A}} = \mathbf{A} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta/2$ and a
diagonalization $\mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le 2/t_2$ and eigenvalues separated by $t_1/2$, for
$t_1, t_2$ = `NLAlib.SmallEig.smallEigGap`, `NLAlib.SmallEig.smallEigCond`. -/
theorem ginibrePerturb_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hSmp : IsSample I) {law : ℕ → Measure ℝ}
    {sG : ℕ} (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hA : ComplexGaussianGapTail c₁)
    (hB : ComplexGaussianConditionTail c₂) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEigReduce nmax S δ φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ nmax)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hAS : specNorm A ≤ S) {a q : ℕ × ℕ} :
    PWrites law I (ginibrePerturb (O := O) (Q := Q) sG).body
      (Env.frame [n + 1, (smallEigParams nmax S δ φ c₁ c₂).length] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix a A μ.store ∧
        μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
          some (smallEigParams nmax S δ φ c₁ c₂) ∧ μ.Live [a, q] ∧
        Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
          (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length))
      (fun μ' => ∃ (E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
        HoldsMatrix a (A + E) μ'.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
        (A + E) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂ ∧
        ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖)
      (3 * φ / 4) := by
  have hN1 : 1 ≤ n + 1 := Nat.le_add_left 1 n
  obtain ⟨hγ, -⟩ := smallEigScale_spec (φ := φ) hδ
  obtain ⟨ht₁p, -, ht₂p, -⟩ := perturbThresholds (c₁ := c₁) (c₂ := c₂) hb₁ hb₂
    (le_trans hN1 hn) hδ hδS hφ hφ1
  obtain ⟨hu0, hu100, hprec⟩ := perturbPrecision hM hb₁ hb₂ hδ hδS hφ hφ1 hu hn
  set γ := smallEigScale δ φ
  set β := γ / √((n + 1 : ℕ) : ℝ) with hβdef
  have hβ : 0 ≤ β := by positivity
  set Bad := perturbBad A β (smallEigGap nmax S δ φ c₁) (smallEigCond nmax S δ φ c₂)
    (γ * (2 * √2 + √(Real.log (φ / 4)⁻¹ / ((n + 1 : ℕ) : ℝ))))
  have hprob : (Measure.pi fun _ : Fin (2 * ((n + 1) * (n + 1))) => law sG).real Bad ≤
      3 * φ / 4 := by
    rw [hG]
    exact measureReal_perturbBad_le hA hB hb₁ hb₂ hδ hδS hφ hφ1 hn hAS
  refine PWrites.of_window (s := sG) (W := 2 * ((n + 1) * (n + 1))) (Bad := fun _ => Bad)
    (measurable_snd (measurableSet_perturbBad _ _ _ _ _)) (fun _ _ => hprob) ?_
  rintro μ τ ⟨hAμ, hq, hl, -⟩ hgood
  have hq0 : μ.store.get q.1 q.2 = some γ := by
    simpa [smallEigParams] using Store.get_of_readBlock hq (j := 0) (by simp [smallEigParams]) 0
  refine (ginibrePerturb_writes_word hS hL hSmp hl hAμ hq0).mono le_rfl ?_
  rintro μ' - ⟨-, hW'⟩
  -- the good window
  set Gm := winMat (n + 1) (Tape.windowFn τ sG μ.pos (2 * ((n + 1) * (n + 1))))
  have hGm : Gm = Computation.tapeComplexMatrix (fun j => τ (μ.pos + j) sG) (n + 1) :=
    winMat_windowFn (n + 1) τ sG μ.pos
  simp only [Bad, perturbBad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_le]
    at hgood
  obtain ⟨hcl, hnoise⟩ := hgood
  have hnoise' : specNorm (β • Gm) ≤ δ / 4 := hnoise.le.trans (perturbNoise_le hδ hφ hφ1 hN1)
  have hround := hM.specNorm_perturbWords_sub_le hu0 hu100 hN1 hγ.le A
    (fun j => τ (μ.pos + j) sG)
  rw [← hGm, ← hβdef] at hround
  rw [show ((β : ℝ) : ℂ) • Gm = β • Gm from (RCLike.real_smul_eq_coe_smul (K := ℂ) β Gm).symm]
    at hround
  have hGn : β * specNorm Gm ≤ δ / 4 := by
    rwa [specNorm_real_smul, abs_of_nonneg hβ] at hnoise'
  obtain ⟨hr₁, hr₂⟩ := hprec (specNorm A + β * specNorm Gm) (by positivity) (by linarith)
  obtain ⟨E, V, d, hE, hEn, hV, hAV, hκ, hgap⟩ := perturb_class ht₁p ht₂p hcl hnoise'
    (hround.trans le_rfl) (by linarith) hr₂
  exact ⟨E, V, d, hE ▸ hW', hEn, hV, hAV, hκ, hgap⟩

end Theorems

end NLAlib.SmallEig
