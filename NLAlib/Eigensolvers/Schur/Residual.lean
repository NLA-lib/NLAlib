/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Contracts
public import NLAlib.Ops.Blas.Matrix
public import NLAlib.Ops.Logic.ProbabilisticFamily
public import NLAlib.Matrix.FinitePrecision.Deflation

/-!
# The residual of a scaled, tracked run

A Schur pipeline scales its input by the reciprocal of a norm estimate, runs stages that carry a
tracked unitary similarity (`NLAlib.IsTrackedUnitarySimilar`) and scales the result back. This
file has the pieces of that argument that do not mention the pipeline: the in-place scaling loop
and the stored matrix it leaves, the stored identity, the residual of the scaled run in matrix
form and its scalar budget, and the near-unitary bounds of an accumulator.

## Main results

* `NLAlib.Schur.writes_loop_mul_cell`: the scaling loop (its stored matrix is
  `NLAlib.Ops.StdModel.exists_holdsMatrix_mul`).
* `NLAlib.Schur.holdsMatrix_one_of_holdsVec`: the stored identity.
* `NLAlib.Schur.specNorm_sub_mul_mul_conjTranspose_le_of_scaled`,
  `NLAlib.Schur.schurPipeline_budget`: the residual of a scaled run and its budget.
* `NLAlib.Schur.exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose`: a computed Schur form is
  an exact Schur form of a nearby matrix.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory
open scoped Matrix

variable {O : Type}

/-- **An in-place scaling loop**: the loop of $N$ rounds whose round $t$ multiplies the cell
$o + t$ of the buffer $b$ by a cell $y$ outside the block, in place, stores in each cell of the
block the machine product of its old word with the word of $y$; it writes only the block and keeps
the tape position. -/
theorem writes_loop_mul_cell {K : Type} [Has ScalarOp O] {Q : Type} {M : Machine K}
    {I : Interp O Q K} (hS : IsScalar M I) {τ : Tape K} {ρ : Env} {m : Mem K}
    {n : IExp} {N b o : ℕ} {y : ℕ × ℕ} {X Y : Operand} {r : K} (hn : n.eval ρ.idx = some N)
    (hX : ∀ t < N, Operand.evalList (ρ.pushIdx t) [X, Y] = some [(b, o + t), y])
    (hX' : ∀ t < N, Operand.evalList (ρ.pushIdx t) [X] = some [(b, o + t)])
    (hl : m.Live [(b, o), y]) (hv : ∀ t < N, ∃ w, m.store.get b (o + t) = some w)
    (hy : m.store.get y.1 y.2 = some r) (hyb : ¬ Store.inBlock b o N y.1 y.2) :
    Writes .total I τ (.loop n (.call (Has.inj ScalarOp.mul) [] [X, Y] [X])) ρ (Store.inBlock b o N)
      (fun m' => m'.pos = m.pos ∧ ∀ t < N, ∀ w, m.store.get b (o + t) = some w →
        m'.store.get b (o + t) = some (M.mul w r)) m := by
  refine (writes_loop hn (fun i => Store.inBlock b o i)
    (fun i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun i m' => m'.pos = m.pos ∧ ∀ t < i, ∀ w, m.store.get b (o + t) = some w →
      m'.store.get b (o + t) = some (M.mul w r)) ⟨rfl, fun t ht => absurd ht (by omega)⟩
    fun i hi m' hfr ⟨hpos, hdone⟩ => ?_).mono le_rfl fun _ _ h => h
  have hlen := hfr.len_eq b
  obtain ⟨w, hw⟩ := hv i hi
  have hroom : o + i < m.store.len b := Store.lt_len_of_get hw
  have hw' : m'.store.get b (o + i) = some w := by
    rw [hfr.2 b (o + i) (by simp [Store.inBlock]), hw]
  have hy' : m'.store.get y.1 y.2 = some r := by
    rw [hfr.2 y.1 y.2 fun h => hyb ⟨h.1, h.2.1, by have := h.2.2; omega⟩, hy]
  have hl' : m'.Live [(b, o + i), y, (b, o + i)] := by
    have h0 := hl.congr hfr.length_eq
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h0 (b, o) (by simp)
    · exact h0 x (by simp)
    · exact h0 (b, o) (by simp)
  refine (writes_call_bin (hS .mul) (hX i hi) (hX' i hi) trivial hw' hy' rfl
    fun _ => ⟨hl', show o + i < m'.store.len b by rw [hlen]; exact hroom⟩).mono
    (show Store.inBlock b (o + i) 1 ≤ Store.inBlock b o (i + 1) from
      Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m'' hfr' ⟨hp, hg⟩
  refine ⟨hp.trans hpos, fun t ht v hv => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
  · rw [hfr'.2 b (o + t) (by simp [Store.inBlock]; omega), hdone t ht v hv]
  · rw [hg, Option.some.inj (hw.symm.trans hv)]

/-- **The stored identity**: words that are $1$ at the real parts of the diagonal entries and $0$
elsewhere (the output of `NLAlib.Ops.PairMatrix.identity` with exact literals) hold the identity
matrix. -/
theorem holdsMatrix_one_of_holdsVec {N : ℕ} {s : Store ℝ} {b : ℕ × ℕ}
    (h : s.HoldsVec b.1 b.2 (2 * (N * N))
      (fun q => if ∃ j < N, q = 2 * (j * N + j) then (1 : ℝ) else 0)) :
    HoldsMatrix b (1 : Matrix (Fin N) (Fin N) ℂ) s := by
  have key : ∀ (i j : Fin N), (∃ j' < N, j * N + i = j' * N + j') ↔ i = j := by
    intro i j
    constructor
    · rintro ⟨j', hj', e⟩
      have h1 := congrArg (· / N) e
      have h2 := congrArg (· % N) e
      simp only [Nat.add_comm (j.val * N), Nat.add_comm (j' * N), Nat.add_mul_div_right _ _
        (Nat.pos_of_ne_zero (by omega : N ≠ 0)), Nat.div_eq_of_lt i.isLt,
        Nat.div_eq_of_lt hj', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt,
        Nat.mod_eq_of_lt hj'] at h1 h2
      exact Fin.ext (by omega)
    · rintro rfl
      exact ⟨i, i.isLt, rfl⟩
  have hlt : ∀ (i j : Fin N), 2 * (j * N + i) + 1 < 2 * (N * N) := fun i j => by
    have := Idx.add_lt_mul j.isLt i.isLt; omega
  refine HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)
  · rw [h _ (by have := hlt i j; omega)]
    by_cases hij : i = j
    · subst hij; dsimp only; rw [if_pos ⟨i, i.isLt, rfl⟩]; simp
    · have hne : ¬ ∃ j' < N, 2 * (j * N + i) = 2 * (j' * N + j') := fun ⟨j', hj', e⟩ =>
        hij ((key i j).mp ⟨j', hj', by omega⟩)
      dsimp only; rw [if_neg hne]; simp [Matrix.one_apply_ne hij]
  · rw [Nat.add_assoc, h _ (hlt i j)]
    have hne : ¬ ∃ j' < N, 2 * (j * N + i) + 1 = 2 * (j' * N + j') := fun ⟨j', _, e⟩ => by omega
    by_cases hij : i = j
    · subst hij; simp [hne]
    · simp [hne, Matrix.one_apply_ne hij]

/-- The accumulator term of the budget: $(2\varepsilon + \varepsilon^2)X \le
5\varepsilon K/c_1 + (33/256)K\varepsilon_{C,T}$. -/
theorem schurPipeline_budget_acc {ε X Y K c₁ εCT : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16)
    (hX0 : 0 ≤ X) (hX : X ≤ 9 / 8 * Y + K * εCT) (hYK : Y ≤ 21 / 10 * K / c₁) (hc₁ : 0 < c₁)
    (hK0 : 0 ≤ K) (hεCT : 0 ≤ εCT) :
    (2 * ε + ε ^ 2) * X ≤ 5 * (ε * K / c₁) + 33 / 256 * (K * εCT) := by
  have hβ : 2 * ε + ε ^ 2 ≤ 33 / 16 * ε := by
    have := mul_le_mul_of_nonneg_right hε hε0
    rw [sq]; linarith
  calc (2 * ε + ε ^ 2) * X ≤ 33 / 16 * ε * X := mul_le_mul_of_nonneg_right hβ hX0
    _ ≤ 33 / 16 * ε * (9 / 8 * (21 / 10 * K / c₁) + K * εCT) := by
      refine mul_le_mul_of_nonneg_left (hX.trans ?_) (by positivity)
      linarith
    _ = 6237 / 1280 * (ε * K / c₁) + 33 / 16 * ε * (K * εCT) := by ring
    _ ≤ 5 * (ε * K / c₁) + 33 / 256 * (K * εCT) := by
      have h1 : 0 ≤ ε * K / c₁ := by positivity
      have h2 : 33 / 16 * ε * (K * εCT) ≤ 33 / 256 * (K * εCT) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hK0 hεCT)
      linarith

/-- The rounding term of the budget: $(1 + \varepsilon)^2\boldsymbol{u}xX \le
(3/2)x^2\boldsymbol{u}a + K\delta_R/16 + K\varepsilon_{C,T}/16$ when $\boldsymbol{u}x \le 1/32$. -/
theorem schurPipeline_budget_round {ε u x X a K δR εCT : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16)
    (hu : 0 ≤ u) (hx0 : 0 ≤ x) (hx : 1 ≤ x) (hw32 : u * x ≤ 1 / 32) (hX0 : 0 ≤ X)
    (hXa : X ≤ 9 / 8 * (a + 3 * (u * x * a) + K * δR) + K * εCT) (ha : 0 ≤ a) (hK0 : 0 ≤ K)
    (hδR0 : 0 ≤ δR) (hεCT : 0 ≤ εCT) :
    (1 + ε) ^ 2 * u * x * X ≤
      3 / 2 * (x * x) * u * a + 1 / 16 * (K * δR) + 1 / 16 * (K * εCT) := by
  set w := u * x with hw
  have hw0 : 0 ≤ w := mul_nonneg hu hx0
  have hq : (1 + ε) ^ 2 ≤ 289 / 256 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + ε)
      (by linarith : 1 + ε ≤ 17 / 16) 2
    norm_num at this ⊢; linarith
  have hγ : (1 + ε) ^ 2 * u * x ≤ 289 / 256 * w := by
    rw [hw, mul_assoc]; exact mul_le_mul_of_nonneg_right hq (mul_nonneg hu hx0)
  have e : 289 / 256 * w * (9 / 8 * (a + 3 * (w * a) + K * δR) + K * εCT) =
      2601 / 2048 * (w * a) + 7803 / 2048 * (w * (w * a)) +
        2601 / 2048 * (w * (K * δR)) + 289 / 256 * (w * (K * εCT)) := by ring
  have hwa : 0 ≤ w * a := mul_nonneg hw0 ha
  have h1 : w * (w * a) ≤ 1 / 32 * (w * a) := mul_le_mul_of_nonneg_right hw32 hwa
  have h2 : w * (K * δR) ≤ 1 / 32 * (K * δR) :=
    mul_le_mul_of_nonneg_right hw32 (mul_nonneg hK0 hδR0)
  have h3 : w * (K * εCT) ≤ 1 / 32 * (K * εCT) :=
    mul_le_mul_of_nonneg_right hw32 (mul_nonneg hK0 hεCT)
  have h4 : w * a ≤ x * x * u * a := by
    rw [hw]
    have : u * x * a * 1 ≤ u * x * a * x := mul_le_mul_of_nonneg_left hx (by positivity)
    linarith [show u * x * a * x = x * x * u * a by ring]
  calc (1 + ε) ^ 2 * u * x * X ≤ 289 / 256 * w * X :=
        mul_le_mul_of_nonneg_right hγ hX0
    _ ≤ 289 / 256 * w * (9 / 8 * (a + 3 * (w * a) + K * δR) + K * εCT) :=
        mul_le_mul_of_nonneg_left hXa (by positivity)
    _ ≤ _ := by rw [e]; linarith [mul_nonneg hK0 hδR0, mul_nonneg hK0 hεCT]

/-- The scalar budget of the pipeline residual: with $K = c_2x a$, the scaling, regularizer,
reducer, core and accumulator errors, written in the scaled units of the norm estimate $s$, add up
to at most $2K(\delta_R + 3\varepsilon_{H,T}/c_1 + \varepsilon_{C,T} + 8\varepsilon/c_1) + 8x^2
\boldsymbol{u}a$; here $x = \sqrt{n + 1}$, $a = \|\mathbf{A}\|_2$, $F = \|\mathbf{A}\|_{\mathsf F}$,
$t_1$, $t_2$ the norms of the scaled and the regularized matrix. -/
theorem schurPipeline_budget {a F s c₁ c₂ x u δR εHT εCT ε t₁ t₂ : ℝ} (ha : 0 ≤ a)
    (hF0 : 0 ≤ F) (hFa : F ≤ x * a) (hx : 1 ≤ x) (hxu : x * x * u ≤ 1 / 32) (hu : 0 ≤ u)
    (hc₁ : 0 < c₁) (hs : 0 < s) (hsl : c₁ * F ≤ s) (hsu : s ≤ c₂ * F)
    (ht₁a : s * t₁ ≤ a + 3 * u * F) (ht₁F : s * t₁ ≤ (1 + 3 * u) * F) (ht₂ : t₂ ≤ t₁ + δR)
    (ht₂0 : 0 ≤ t₂) (hδR0 : 0 ≤ δR) (hδR : δR ≤ 1 / c₁) (hεHT0 : 0 ≤ εHT)
    (hεHT : εHT ≤ 1 / 8) (hεCT : 0 ≤ εCT) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 16) :
    s * (δR + (εHT * t₂ + εCT) + (2 * ε + ε ^ 2) * (t₂ + (εHT * t₂ + εCT))) + 3 * u * F +
        (1 + ε) ^ 2 * u * s * x * (t₂ + (εHT * t₂ + εCT)) ≤
      (2 * c₂ * x * (δR + 3 * εHT / c₁ + εCT + 8 * ε / c₁) + 8 * (x * x) * u) * a := by
  set K := c₂ * x * a with hK
  set w := u * x with hw
  have hx0 : 0 ≤ x := by linarith
  have hw0 : 0 ≤ w := mul_nonneg hu hx0
  have hw32 : w ≤ 1 / 32 :=
    calc w ≤ u * x * x := le_mul_of_one_le_right (mul_nonneg hu hx0) hx
      _ = x * x * u := by ring
      _ ≤ 1 / 32 := hxu
  have hu32 : u ≤ 1 / 32 := (le_mul_of_one_le_right hu hx).trans hw32
  have hc₂ : 0 ≤ c₂ := by
    by_contra h
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge h)) hF0]
  have hsK : s ≤ K := hsu.trans (by
    rw [hK, mul_assoc]; exact mul_le_mul_of_nonneg_left hFa hc₂)
  have hK0 : 0 ≤ K := hs.le.trans hsK
  have hFK : F * c₁ ≤ K := by linarith [mul_comm c₁ F]
  set Y := s * t₂ with hY
  have hY0 : 0 ≤ Y := mul_nonneg hs.le ht₂0
  have hsδ : s * δR ≤ K * δR := mul_le_mul_of_nonneg_right hsK hδR0
  have hKδ : K * δR * c₁ ≤ K := by
    have := mul_le_mul_of_nonneg_left hδR hK0
    rw [mul_one_div, le_div_iff₀ hc₁] at this; linarith
  have hYst : Y ≤ s * t₁ + s * δR := by
    rw [hY, ← mul_add]; exact mul_le_mul_of_nonneg_left ht₂ hs.le
  have hYc : Y * c₁ ≤ 21 / 10 * K := by
    have h1 : Y * c₁ ≤ s * t₁ * c₁ + s * δR * c₁ := by
      rw [← add_mul]; exact mul_le_mul_of_nonneg_right hYst hc₁.le
    have h2 : s * t₁ * c₁ ≤ (1 + 3 * u) * (F * c₁) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ht₁F hc₁.le
    have h3 : (1 + 3 * u) * (F * c₁) ≤ (1 + 3 * u) * K :=
      mul_le_mul_of_nonneg_left hFK (by linarith)
    have h4 : s * δR * c₁ ≤ K * δR * c₁ := mul_le_mul_of_nonneg_right hsδ hc₁.le
    have h5 : u * K ≤ 1 / 32 * K := mul_le_mul_of_nonneg_right hu32 hK0
    linarith [mul_comm u K, show (1 + 3 * u) * K = K + 3 * (u * K) by ring]
  have hYK : Y ≤ 21 / 10 * K / c₁ := by rw [le_div_iff₀ hc₁]; exact hYc
  have hYa : Y ≤ a + 3 * (w * a) + K * δR := by
    have : u * F ≤ w * a := by
      rw [hw, mul_assoc]; exact mul_le_mul_of_nonneg_left hFa hu
    linarith
  set X := s * (t₂ + (εHT * t₂ + εCT)) with hXdef
  have hX : X ≤ 9 / 8 * Y + K * εCT := by
    have h1 : X = Y + εHT * Y + s * εCT := by rw [hXdef, hY]; ring
    have h2 : εHT * Y ≤ 1 / 8 * Y := mul_le_mul_of_nonneg_right hεHT hY0
    have h3 : s * εCT ≤ K * εCT := mul_le_mul_of_nonneg_right hsK hεCT
    linarith
  have hX0 : 0 ≤ X := by positivity
  -- the six terms
  have hKc : 0 ≤ K / c₁ := div_nonneg hK0 hc₁.le
  have b₂ : s * (εHT * t₂) ≤ 3 * εHT * K / c₁ := by
    have e : s * (εHT * t₂) = εHT * Y := by rw [hY]; ring
    rw [e]
    calc εHT * Y ≤ εHT * (21 / 10 * K / c₁) := mul_le_mul_of_nonneg_left hYK hεHT0
      _ ≤ 3 * εHT * K / c₁ := by
        rw [show 3 * εHT * K / c₁ = 3 * (εHT * (K / c₁)) by ring,
          show εHT * (21 / 10 * K / c₁) = 21 / 10 * (εHT * (K / c₁)) by ring]
        linarith [mul_nonneg hεHT0 hKc]
  have b₃ : s * εCT ≤ K * εCT := mul_le_mul_of_nonneg_right hsK hεCT
  have b₄ := schurPipeline_budget_acc hε0 hε hX0 hX hYK hc₁ hK0 hεCT
  have b₅ : 3 * u * F ≤ 3 * (x * x) * u * a := by
    have : u * F ≤ u * (x * a) := mul_le_mul_of_nonneg_left hFa hu
    have h2 : u * (x * a) ≤ u * (x * a) * x := le_mul_of_one_le_right (by positivity) hx
    have e : 3 * (x * x) * u * a = 3 * (u * (x * a) * x) := by ring
    rw [e]; linarith
  have b₆ := schurPipeline_budget_round hε0 hε hu hx0 hx hw32 hX0
    (by rw [← hw]; linarith) ha hK0 hδR0 hεCT
  -- assemble
  have eL : s * (δR + (εHT * t₂ + εCT) + (2 * ε + ε ^ 2) * (t₂ + (εHT * t₂ + εCT))) +
      3 * u * F + (1 + ε) ^ 2 * u * s * x * (t₂ + (εHT * t₂ + εCT)) =
      s * δR + s * (εHT * t₂) + s * εCT + (2 * ε + ε ^ 2) * X + 3 * u * F +
        (1 + ε) ^ 2 * u * x * X := by rw [hXdef]; ring
  have eR : (2 * c₂ * x * (δR + 3 * εHT / c₁ + εCT + 8 * ε / c₁) + 8 * (x * x) * u) * a =
      2 * (K * δR) + 2 * (3 * εHT * K / c₁) + 2 * (K * εCT) + 16 * (ε * K / c₁) +
        8 * (x * x) * u * a := by rw [hK]; ring
  rw [eL, eR]
  have p₁ : 0 ≤ K * δR := mul_nonneg hK0 hδR0
  have p₂ : 0 ≤ K * εCT := mul_nonneg hK0 hεCT
  have p₃ : 0 ≤ ε * K / c₁ := by positivity
  have p₄ : 0 ≤ 3 * εHT * K / c₁ := by positivity
  have p₅ : 0 ≤ x * x * u * a := by positivity
  linarith

/-- **The residual of the pipeline in matrix form**: the input $\mathbf{A}$ scaled by $1/s$ to
$\mathbf{A}_1$ ($\|s\mathbf{A}_1 - \mathbf{A}\|_2 \le 3\boldsymbol{u}\|\mathbf{A}\|_{\mathsf F}$),
regularized to $\mathbf{A}_2$ within $\delta_R$, carried by a tracked run from
$(\mathbf{I}, \mathbf{A}_2)$ to $(\mathbf{U}, \mathbf{T})$ and scaled back to $\mathbf{T}'$
($\|\mathbf{T}' - s\mathbf{T}\|_{\mathsf F} \le \boldsymbol{u}s\|\mathbf{T}\|_{\mathsf F}$) has
$\|\mathbf{A} - \mathbf{U}\mathbf{T}'\mathbf{U}^{\mathsf H}\|_2$ at most the sum of the scaled
errors. -/
theorem specNorm_sub_mul_mul_conjTranspose_le_of_scaled {N : ℕ}
    {A A₁ A₂ U T T' : Matrix (Fin N) (Fin N) ℂ} {s u δR εT ε : ℝ} (hs : 0 < s) (hu : 0 ≤ u)
    (hA₁ : specNorm ((s : ℂ) • A₁ - A) ≤ 3 * u * frobNorm A) (hA₂ : specNorm (A₂ - A₁) ≤ δR)
    (hT : IsTrackedUnitarySimilar ε εT 1 A₂ U T) (hε0 : 0 ≤ ε)
    (hT' : frobNorm (T' - (s : ℂ) • T) ≤ u * s * frobNorm T) :
    specNorm (A - U * T' * Uᴴ) ≤
      s * (δR + εT + (2 * ε + ε ^ 2) * (specNorm A₂ + εT)) + 3 * u * frobNorm A +
        (1 + ε) ^ 2 * u * s * √(N : ℝ) * (specNorm A₂ + εT) := by
  obtain ⟨V, E, hV, hUV, hE, hAE⟩ := hT.exists_eq_mul_mul_conjTranspose hε0
  have hres := (hT.specNorm_sub_mul_mul_conjTranspose_le hε0).1
  have hTn : specNorm T ≤ specNorm A₂ + εT := by
    rw [← hV.specNorm_mul_conjTranspose_right, ← hV.specNorm_mul_left, ← Matrix.mul_assoc, ← hAE]
    exact (specNorm_add_le _ _).trans (by linarith)
  have hUn : specNorm U ≤ 1 + ε := by
    have := specNorm_add_le V (U - V)
    rw [add_sub_cancel] at this
    linarith [hV.specNorm_le_one]
  have hD : specNorm (U * (T' - (s : ℂ) • T) * Uᴴ) ≤
      (1 + ε) ^ 2 * (u * s * (√(N : ℝ) * specNorm T)) := by
    have h1 : specNorm (T' - (s : ℂ) • T) ≤ u * s * (√(N : ℝ) * specNorm T) :=
      (specNorm_le_frobNorm _).trans (hT'.trans (mul_le_mul_of_nonneg_left
        (by have := frobNorm_le_sqrt_card_mul_specNorm T; rwa [Fintype.card_fin] at this)
        (by positivity)))
    have h0 := specNorm_nonneg (T' - (s : ℂ) • T)
    calc _ ≤ specNorm U * specNorm (T' - (s : ℂ) • T) * specNorm Uᴴ :=
          (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _))
      _ ≤ (1 + ε) * (u * s * (√(N : ℝ) * specNorm T)) * (1 + ε) := by
          rw [specNorm_conjTranspose]
          have hU0 := specNorm_nonneg U
          exact mul_le_mul (mul_le_mul hUn h1 h0 (by linarith)) hUn hU0 (by positivity)
      _ = _ := by ring
  have e : A - U * T' * Uᴴ = -((s : ℂ) • A₁ - A) - (s : ℂ) • (A₂ - A₁) +
      (s : ℂ) • (A₂ - U * T * Uᴴ) - U * (T' - (s : ℂ) • T) * Uᴴ := by
    simp only [smul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    abel
  have hsn : ∀ X : Matrix (Fin N) (Fin N) ℂ, specNorm ((s : ℂ) • X) = s * specNorm X := fun X => by
    rw [specNorm_smul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  rw [e]
  have t₁ := specNorm_sub_le (-((s : ℂ) • A₁ - A) - (s : ℂ) • (A₂ - A₁) +
    (s : ℂ) • (A₂ - U * T * Uᴴ)) (U * (T' - (s : ℂ) • T) * Uᴴ)
  have t₂ := specNorm_add_le (-((s : ℂ) • A₁ - A) - (s : ℂ) • (A₂ - A₁))
    ((s : ℂ) • (A₂ - U * T * Uᴴ))
  have t₃ := specNorm_sub_le (-((s : ℂ) • A₁ - A)) ((s : ℂ) • (A₂ - A₁))
  rw [specNorm_neg, hsn] at t₃
  rw [hsn] at t₂
  set c := (1 + ε) ^ 2 * u * s * √(N : ℝ)
  have hTn' : c * specNorm T ≤ c * (specNorm A₂ + εT) :=
    mul_le_mul_of_nonneg_left hTn (by positivity)
  have hD' : specNorm (U * (T' - (s : ℂ) • T) * Uᴴ) ≤ c * specNorm T := by
    refine hD.trans (le_of_eq ?_); ring
  have h₂ := mul_le_mul_of_nonneg_left hA₂ hs.le
  have h₃ := mul_le_mul_of_nonneg_left hres hs.le
  have eR : s * (δR + εT + (2 * ε + ε ^ 2) * (specNorm A₂ + εT)) + 3 * u * frobNorm A +
      (1 + ε) ^ 2 * u * s * √(N : ℝ) * (specNorm A₂ + εT) = s * δR +
        s * (εT + (2 * ε + ε ^ 2) * (specNorm A₂ + εT)) + 3 * u * frobNorm A +
          c * (specNorm A₂ + εT) := by ring
  rw [eR]
  linarith

/-- **Near a unitary, nearly orthonormal**: if $\|\mathbf{U} - \mathbf{W}\|_2 \le \varepsilon$
for $\mathbf{W}$ with orthonormal columns, then
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le 2\varepsilon + \varepsilon^2$. -/
theorem specNorm_conjTranspose_mul_self_sub_one_le_of_specNorm_sub_le {m : ℕ}
    {U W : Matrix (Fin m) (Fin m) ℂ} (hW : HasOrthonormalCols W) {ε : ℝ}
    (h : specNorm (U - W) ≤ ε) : specNorm (Uᴴ * U - 1) ≤ 2 * ε + ε ^ 2 := by
  obtain ⟨Δ, rfl⟩ : ∃ Δ, U = W + Δ := ⟨U - W, by abel⟩
  rw [add_sub_cancel_left] at h
  have hd := specNorm_nonneg Δ
  have e : (W + Δ)ᴴ * (W + Δ) - 1 = Wᴴ * Δ + Δᴴ * W + Δᴴ * Δ := by
    rw [Matrix.conjTranspose_add]
    simp only [Matrix.add_mul, Matrix.mul_add, hW.conjTranspose_mul_self]
    abel
  have h₁ : specNorm (Wᴴ * Δ) ≤ ε := (hW.specNorm_conjTranspose_mul_le Δ).trans h
  have h₂ : specNorm (Δᴴ * W) ≤ ε := by rwa [hW.specNorm_mul_right, specNorm_conjTranspose]
  have h₃ : specNorm (Δᴴ * Δ) ≤ ε * ε := (specNorm_mul_le _ _).trans
    (mul_le_mul (by rwa [specNorm_conjTranspose]) h hd (hd.trans h))
  rw [e]
  refine ((specNorm_add_le _ _).trans (add_le_add ((specNorm_add_le _ _).trans
    (add_le_add h₁ h₂)) h₃)).trans (le_of_eq ?_)
  ring

/-- The pipeline's accumulator error on every tape: a reducer accumulator within $\varepsilon_H$
of a unitary $\mathbf{V}_1$ and a core accumulator within $\varepsilon_C\|\mathbf{U}_1\|_2$ of
$\mathbf{U}_1\mathbf{V}$ give $\|\mathbf{U}_2^{\mathsf H}\mathbf{U}_2 - \mathbf{I}\|_2 \le
2\varepsilon + \varepsilon^2$, $\varepsilon = (1 + \varepsilon_H)(1 + \varepsilon_C) - 1$. -/
theorem specNorm_conjTranspose_mul_self_sub_one_le_of_tracked {m : ℕ}
    {U₁ U₂ V₁ V : Matrix (Fin m) (Fin m) ℂ} {εH εC : ℝ} (hεC : 0 ≤ εC)
    (hV₁ : HasOrthonormalCols V₁) (hV : HasOrthonormalCols V)
    (h₁ : specNorm (U₁ - V₁) ≤ εH) (h₂ : specNorm (U₂ - U₁ * V) ≤ εC * specNorm U₁) :
    specNorm (U₂ᴴ * U₂ - 1) ≤
      2 * ((1 + εH) * (1 + εC) - 1) + ((1 + εH) * (1 + εC) - 1) ^ 2 := by
  have hW : HasOrthonormalCols (V₁ * V) := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc V₁ᴴ, hV₁.conjTranspose_mul_self, Matrix.one_mul,
      hV.conjTranspose_mul_self]
  refine specNorm_conjTranspose_mul_self_sub_one_le_of_specNorm_sub_le hW ?_
  have hU₁ : specNorm U₁ ≤ 1 + εH := by
    have := specNorm_add_le V₁ (U₁ - V₁); rw [add_sub_cancel] at this
    linarith [hV₁.specNorm_le_one]
  have e : U₂ - V₁ * V = (U₂ - U₁ * V) + (U₁ - V₁) * V := by
    rw [Matrix.sub_mul]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hV.specNorm_mul_right]
  nlinarith [mul_le_mul_of_nonneg_left hU₁ hεC]

/-- The norms after the regularizer and the reducer: from $\|\mathbf{A}_1\|_2 \le 2/c_1$,
$\|\mathbf{A}_2 - \mathbf{A}_1\|_2 \le \delta_R \le 1/c_1$ and a reduction of $\mathbf{A}_2$ to
$\mathbf{H}$ with backward error $\varepsilon_{H,T}\|\mathbf{A}_2\|_2$, $\varepsilon_{H,T} \le 1/8$:
$\|\mathbf{A}_2\|_2 \le 2/c_1 + \delta_R$ and $\|\mathbf{H}\|_2 \le 4/c_1$. -/
theorem specNorm_le_of_reduced {m : ℕ} {A₁ A₂ H V : Matrix (Fin m) (Fin m) ℂ}
    {c₁ δR εHT : ℝ} (hc₁ : 0 < c₁) (hδR : δR ≤ 1 / c₁) (hεHT : εHT ≤ 1 / 8)
    (hA₁ : specNorm A₁ ≤ 2 / c₁) (hA₂ : specNorm (A₂ - A₁) ≤ δR)
    (hV : IsPerturbedUnitarySimilarBy V A₂ H (εHT * specNorm A₂)) :
    specNorm A₂ ≤ 2 / c₁ + δR ∧ specNorm H ≤ 4 / c₁ := by
  have hA₂b : specNorm A₂ ≤ 2 / c₁ + δR := by
    have := specNorm_add_le A₁ (A₂ - A₁); rw [add_sub_cancel] at this; linarith
  refine ⟨hA₂b, ?_⟩
  have hn0 := specNorm_nonneg A₂
  have h₁ := hV.isPerturbedUnitarySimilar.specNorm_le
  have h₂ : εHT * specNorm A₂ ≤ 1 / 8 * specNorm A₂ := mul_le_mul_of_nonneg_right hεHT hn0
  have h₃ : specNorm A₂ ≤ 3 / c₁ := by
    rw [show (3 : ℝ) / c₁ = 2 / c₁ + 1 / c₁ by ring]; linarith
  have h₄ : 9 / 8 * (3 / c₁) ≤ 4 / c₁ := by
    rw [show 9 / 8 * (3 / c₁) = 27 / 8 / c₁ by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hc₁.le
  linarith

/-- **A computed Schur form is an exact Schur form of a nearby matrix**: if $\mathbf{T}$ is
upper triangular, $\|\mathbf{A} - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_2 \le
e_A\|\mathbf{A}\|_2$ and $\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e_U \le 1/8$,
there is an exact unitary $\mathbf{V}$ within $e_U$ of $\mathbf{U}$ with $\mathbf{A} +
\mathbf{E} = \mathbf{V}\mathbf{T}\mathbf{V}^{\mathsf H}$,
$\|\mathbf{E}\|_2 \le (e_A + 4e_U(1 + e_A))\|\mathbf{A}\|_2$ (the polar factor of
$\mathbf{U}$). -/
theorem exists_hasOrthonormalCols_add_eq_mul_mul_conjTranspose {m : ℕ}
    {A U T : Matrix (Fin m) (Fin m) ℂ} {eA eU : ℝ}
    (hA : specNorm (A - U * T * Uᴴ) ≤ eA * specNorm A) (hU : specNorm (Uᴴ * U - 1) ≤ eU)
    (heU : eU ≤ 1 / 8) :
    ∃ V E : Matrix (Fin m) (Fin m) ℂ, HasOrthonormalCols V ∧ specNorm (U - V) ≤ eU ∧
      specNorm E ≤ (eA + 4 * eU * (1 + eA)) * specNorm A ∧ A + E = V * T * Vᴴ := by
  have he0 : 0 ≤ eU := (specNorm_nonneg _).trans hU
  obtain ⟨V, hV, hVU⟩ :=
    exists_hasOrthonormalCols_specNorm_sub_le_of_specNorm_conjTranspose_mul_self_sub_one_le
      he0 (by linarith) hU
  have hUV : specNorm (U - V) ≤ eU := by rwa [← specNorm_neg, neg_sub]
  set η := specNorm (U - V)
  have hη := specNorm_nonneg (U - V)
  set t := specNorm T
  set a := specNorm A
  have ht := specNorm_nonneg T
  have ha := specNorm_nonneg A
  -- the two conjugations differ by at most $(2\eta + \eta^2)\|\mathbf{T}\|_2$
  have hD : specNorm (V * T * Vᴴ - U * T * Uᴴ) ≤ (2 * η + η ^ 2) * t := by
    have e : V * T * Vᴴ - U * T * Uᴴ = -((U - V) * T * Uᴴ + V * T * (U - V)ᴴ) := by
      simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
      abel
    have hUn : specNorm U ≤ 1 + η := by
      have := specNorm_add_le V (U - V)
      rw [add_sub_cancel] at this
      linarith [hV.specNorm_le_one]
    have h₁ : specNorm ((U - V) * T * Uᴴ) ≤ η * t * (1 + η) := by
      refine (specNorm_mul_le _ _).trans (mul_le_mul ((specNorm_mul_le _ _)) ?_
        (specNorm_nonneg _) (mul_nonneg hη ht))
      rwa [specNorm_conjTranspose]
    have h₂ : specNorm (V * T * (U - V)ᴴ) ≤ t * η := by
      rw [Matrix.mul_assoc, hV.specNorm_mul_left]
      refine (specNorm_mul_le _ _).trans (le_of_eq ?_)
      rw [specNorm_conjTranspose]
    rw [e, specNorm_neg]
    refine (specNorm_add_le _ _).trans ?_
    nlinarith
  have hVT : specNorm (V * T * Vᴴ) = t := by
    rw [hV.specNorm_mul_conjTranspose_right, hV.specNorm_mul_left]
  have hR : specNorm (U * T * Uᴴ - A) ≤ eA * a := by rwa [← specNorm_neg, neg_sub]
  -- $\|\mathbf{T}\|_2(1 - 2\eta - \eta^2) \le (1 + e_A)\|\mathbf{A}\|_2$
  have htA : t ≤ a + eA * a + (2 * η + η ^ 2) * t := by
    have e : V * T * Vᴴ = A + (U * T * Uᴴ - A) + (V * T * Vᴴ - U * T * Uᴴ) := by abel
    have := specNorm_add_le (A + (U * T * Uᴴ - A)) (V * T * Vᴴ - U * T * Uᴴ)
    have := specNorm_add_le A (U * T * Uᴴ - A)
    rw [← e, hVT] at *
    linarith
  have hηe : η ≤ 1 / 8 := hUV.trans heU
  have hk : (2 * η + η ^ 2) * t ≤ 4 * eU * (1 + eA) * a := by
    have hk0 : 2 * η + η ^ 2 ≤ 17 / 64 := by nlinarith
    have h1 : 0 ≤ a + eA * a := by nlinarith [mul_le_mul_of_nonneg_right hk0 ht]
    have h2 : (2 * η + η ^ 2) * t ≤ 17 / 8 * η * t := by
      have : 2 * η + η ^ 2 ≤ 17 / 8 * η := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this ht]
    have h3 : 23 / 32 * t ≤ a + eA * a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hUV (mul_nonneg ht (by norm_num : (0 : ℝ) ≤ 17 / 8))]
  refine ⟨V, V * T * Vᴴ - A, hV, hUV, ?_, by abel⟩
  have e : V * T * Vᴴ - A = (U * T * Uᴴ - A) + (V * T * Vᴴ - U * T * Uᴴ) := by abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  nlinarith

end NLAlib.Schur
