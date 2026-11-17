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
    (fun _ => ⟨by simp [Mem.Live, hf₂.length_eq, hf₁.length_eq]; pomega,
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
    (fun _ => ⟨by simp [Mem.Live, hlen₅]; pomega, by pomega⟩)).seq_le (hle 1 (by pomega)) ?_
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
    (fun _ => ⟨by simp [Mem.Live]; pomega, by pomega⟩)).seq_le
    (by simpa using hG 0 (by pomega)) ?_
  rintro m₁ hf₁ ⟨hp₁, hv₁⟩
  refine (writes_call_bin (hS .mul) h₂ h₂' trivial (K hf₁ (by pomega) hw₁) (K hf₁ (by pomega) hh)
    rfl (fun _ => ⟨by simp [Mem.Live, hf₁.length_eq]; pomega, by
      rw [hf₁.len_eq]; pomega⟩)).seq_le (hG 1 (by pomega)) ?_
  rintro m₂ hf₂ ⟨hp₂, hv₂⟩
  refine (writes_call_bin (hS .mul) h₃ h₃' trivial (K hf₂ (by pomega) hv₁)
    (K hf₂ (by pomega) (K hf₁ (by pomega) hg)) rfl
    (fun _ => ⟨by simp [Mem.Live, hf₂.length_eq, hf₁.length_eq]; pomega, by
      rw [hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le (by simpa using hG 0 (by pomega)) ?_
  rintro m₃ hf₃ ⟨hp₃, hv₃⟩
  have hlen₃ : m₃.store.length = m.store.length :=
    hf₃.length_eq.trans (hf₂.length_eq.trans hf₁.length_eq)
  refine (writes_call_bin (hS .mul) h₄ h₄' trivial (K hf₃ (by pomega) hv₂)
    (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) hg))) rfl
    (fun _ => ⟨by simp [Mem.Live, hlen₃]; pomega, by
      rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le (hG 1 (by pomega)) ?_
  rintro m₄ hf₄ ⟨hp₄, hv₄⟩
  have ha₀' := K hf₄ (by pomega) (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) ha₀)))
  have ha₁' := K hf₄ (by pomega) (K hf₃ (by pomega) (K hf₂ (by pomega) (K hf₁ (by pomega) ha₁)))
  have hlen₄ : m₄.store.length = m.store.length := hf₄.length_eq.trans hlen₃
  refine (writes_call_bin (hS .add) h₅ h₅' trivial ha₀' (K hf₄ (by pomega) hv₃) rfl
    (fun _ => ⟨by simp [Mem.Live, hlen₄]; pomega, by
      rw [hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega⟩)).seq_le
    (by simpa using hZ 0 (by pomega)) ?_
  rintro m₅ hf₅ ⟨hp₅, hv₅⟩
  refine (writes_call_bin (hS .add) h₆ h₆' trivial (K hf₅ (by pomega) ha₁')
    (K hf₅ (by pomega) hv₄) rfl
    (fun _ => ⟨by simp [Mem.Live, hf₅.length_eq, hlen₄]; pomega, by
      rw [hf₅.len_eq, hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; pomega⟩)).mono
    (hZ 1 (by pomega)) ?_
  rintro m₆ hf₆ ⟨hp₆, hv₆⟩
  exact ⟨by rw [hp₆, hp₅, hp₄, hp₃, hp₂, hp₁], K hf₆ (by pomega) hv₅, hv₆⟩

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
    (hA : HoldsMatrix a A μ.store) (hq : μ.store.get q.1 q.2 = some γ)
    (haq : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock q.1 q.2 1)) :
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
    (μ := ⟨s₁, μ.pos⟩) (g := (L, 0)) (by simp [Mem.Live]; pomega) (by simp [hG])).frame_seq_le
    rfl rfl (by simp [Mem.Live]; pomega) (hab _ _ _ le_rfl) ?_
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
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hSmp : IsSample I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sG : ℕ}
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hA : ComplexGaussianGapTail c₁)
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
  sorry

end Theorems

end NLAlib.SmallEig
