/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Shift
public import NLAlib.Ops.Blas.Pair
public import NLAlib.Eigensolvers.ShiftedQR.RoundedModuli
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.IndependentLoop
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Matrix.FinitePrecision.GivensRounded
public import NLAlib.Matrix.FinitePrecision.HessenbergRowPoly
public import NLAlib.Eigensolvers.ShiftedQR.StableStep

/-!
# The rounded last row of a shift polynomial

A complex row vector $\mathbf{r}$, stored as word pairs, times a stored complex matrix
$\mathbf{W}$ of order $N$: each entry $(\mathbf{r}^{\mathsf T}\mathbf{W})_i$ accumulated by $N$
rounded complex multiply–adds (`NLAlib.Ops.Pair.linearCombination`) is within
$((1 + 5\boldsymbol{u})^N - 1)\sum_l \lvert r_l\rvert\lvert W_{li}\rvert$, so the computed row is
within $((1 + 5\boldsymbol{u})^N - 1)\|\mathbf{W}\|_{\mathsf F}\|\mathbf{r}\|$ in the Euclidean
norm. One step of the recurrence $\widehat{\mathbf{r}}_{j+1} =
\mathrm{fl}(\widehat{\mathbf{r}}_j^{\mathsf T}(\mathbf{H} - s_j))$ of
[BanksGarzaVargasSrivastava2022, Lemma 4.5] forms $\mathbf{W} = \mathrm{fl}(\mathbf{H} - s_j)$
(`NLAlib.ShiftedQR.shiftDiagonal`) and multiplies; its relative error is
$12N^{3/2}\boldsymbol{u}$, the per-step hypothesis of
`NLAlib.norm_toLp_sub_aeval_shiftPoly_row_le`.

## Main definitions

* `NLAlib.ShiftedQR.rowEntryWord`: the machine accumulation of one entry.
* `NLAlib.ShiftedQR.rowEntry`, `NLAlib.ShiftedQR.rowMul`, `NLAlib.ShiftedQR.rowShiftStep`,
  `NLAlib.ShiftedQR.rowInit`, `NLAlib.ShiftedQR.rowPolyLoop`: the programs.
* `NLAlib.ShiftedQR.rowPolyVec`: the vectors of the rounded recurrence.

## Main results

* `NLAlib.ShiftedQR.norm_rowEntryWord_sub_le`: the error of one accumulated entry.
* `NLAlib.ShiftedQR.norm_toLp_sub_vecMul_le_of_forall`: entrywise errors to a Euclidean bound.
* `NLAlib.ShiftedQR.norm_toLp_sub_vecMul_sub_smul_le`: the relative error of one rounded step.
* `NLAlib.ShiftedQR.rowPolyLoop_writes_word`: the stored row of the recurrence.
* `NLAlib.ShiftedQR.norm_toLp_rowMulVec_sub_le`: one stored step as a relative error.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

/-! ### The accumulated entry -/

/-- The complex number of a word pair. -/
def pairToComplex (w : ℝ × ℝ) : ℂ := ⟨w.1, w.2⟩

/-- The machine accumulation of $\sum_l a_l x_l$ from the pair `z₀`: step $l$ is the rounded
complex combination `NLAlib.Ops.Pair.linearWords` of $a_l x_l$ and the stored pair `o` times the
running pair. With `o` the pair of $1$ and `z₀` that of $0$, the rounded inner product. -/
def rowEntryWord (M : Machine ℝ) (o z₀ : ℝ × ℝ) (a x : ℕ → ℂ) : ℕ → ℝ × ℝ
  | 0 => z₀
  | l + 1 => Pair.linearWords M ((a l).re, (a l).im) o ((x l).re, (x l).im)
      (rowEntryWord M o z₀ a x l)

/-- **The rounded inner product of complex numbers**: under the standard model with
$0 \le \boldsymbol{u} \le 1/100$, the machine accumulation `NLAlib.ShiftedQR.rowEntryWord` from
$0$, with the pair of $1$, of $l$ terms $a_j x_j$ satisfies
$$\Bigl\lvert \widehat{s}_l - \sum_{j<l} a_j x_j\Bigr\rvert \le
((1 + 5\boldsymbol{u})^l - 1)\sum_{j<l}\lvert a_j\rvert\lvert x_j\rvert.$$
[Higham2002, Lemma 3.4], with the constant of one rounded complex multiply–add. -/
theorem norm_rowEntryWord_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) (a x : ℕ → ℂ) (l : ℕ) :
    ‖pairToComplex (rowEntryWord M (1, 0) (0, 0) a x l) - ∑ j ∈ Finset.range l, a j * x j‖ ≤
      ((1 + 5 * u) ^ l - 1) * ∑ j ∈ Finset.range l, ‖a j‖ * ‖x j‖ := by
  induction l with
  | zero => simp [rowEntryWord, pairToComplex, Complex.ext_iff]
  | succ l ih =>
    set c := pairToComplex (rowEntryWord M (1, 0) (0, 0) a x l)
    set S := ∑ j ∈ Finset.range l, a j * x j
    set A := ∑ j ∈ Finset.range l, ‖a j‖ * ‖x j‖
    have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => by positivity
    have hSA : ‖S‖ ≤ A := (norm_sum_le _ _).trans (by simp only [norm_mul]; exact le_rfl)
    have hG := hM.norm_linearWords_sub_le hu hu' (a l) 1 (x l) c
    have hpair : ((c.re, c.im) : ℝ × ℝ) = rowEntryWord M (1, 0) (0, 0) a x l := rfl
    have hone : (((1 : ℂ).re, (1 : ℂ).im) : ℝ × ℝ) = (1, 0) := by simp
    rw [hpair, hone, norm_one, one_mul, one_mul] at hG
    have hstep : pairToComplex (rowEntryWord M (1, 0) (0, 0) a x (l + 1)) =
        ⟨(Pair.linearWords M ((a l).re, (a l).im) (1, 0) ((x l).re, (x l).im)
          (rowEntryWord M (1, 0) (0, 0) a x l)).1,
         (Pair.linearWords M ((a l).re, (a l).im) (1, 0) ((x l).re, (x l).im)
          (rowEntryWord M (1, 0) (0, 0) a x l)).2⟩ := rfl
    rw [hstep, Finset.sum_range_succ, Finset.sum_range_succ]
    have hc : ‖c‖ ≤ A + ((1 + 5 * u) ^ l - 1) * A := by
      have := norm_sub_norm_le c S; linarith
    have hpow : 1 ≤ (1 + 5 * u) ^ l := one_le_pow₀ (by linarith)
    have hax : 0 ≤ ‖a l‖ * ‖x l‖ := by positivity
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (⟨(Pair.linearWords M ((a l).re, (a l).im) (1, 0) ((x l).re, (x l).im)
          (rowEntryWord M (1, 0) (0, 0) a x l)).1,
         (Pair.linearWords M ((a l).re, (a l).im) (1, 0) ((x l).re, (x l).im)
          (rowEntryWord M (1, 0) (0, 0) a x l)).2⟩ : ℂ) (a l * x l + c) (S + a l * x l)
    have he : a l * x l + c - (S + a l * x l) = c - S := by ring
    rw [he] at htri
    have h5 : 5 * u ≤ (1 + 5 * u) ^ (l + 1) - 1 := by
      rw [pow_succ]; nlinarith
    calc _ ≤ 5 * u * (‖a l‖ * ‖x l‖ + ‖c‖) + ((1 + 5 * u) ^ l - 1) * A := by linarith
      _ ≤ 5 * u * (‖a l‖ * ‖x l‖) + ((1 + 5 * u) ^ (l + 1) - 1) * A := by
          rw [pow_succ]; nlinarith
      _ ≤ ((1 + 5 * u) ^ (l + 1) - 1) * (A + ‖a l‖ * ‖x l‖) := by nlinarith

/-! ### From entries to the Euclidean norm -/

/-- Entrywise errors of a row product: if every entry of $\mathbf{y}$ is within
$\gamma\sum_l \lvert r_l\rvert\lvert W_{li}\rvert$ of $(\mathbf{r}^{\mathsf T}\mathbf{W})_i$, then
$\|\mathbf{y} - \mathbf{r}^{\mathsf T}\mathbf{W}\| \le \gamma\|\mathbf{W}\|_{\mathsf F}
\|\mathbf{r}\|$ (Cauchy–Schwarz in each entry). -/
theorem norm_toLp_sub_vecMul_le_of_forall {m : Type*} [Fintype m] {γ : ℝ} (hγ : 0 ≤ γ)
    {r y : m → ℂ} {W : Matrix m m ℂ}
    (h : ∀ i, ‖y i - (r ᵥ* W) i‖ ≤ γ * ∑ l, ‖r l‖ * ‖W l i‖) :
    ‖WithLp.toLp 2 (y - r ᵥ* W)‖ ≤ γ * frobNorm W * ‖WithLp.toLp 2 r‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, mul_pow, mul_pow, EuclideanSpace.norm_sq_eq,
    frobNorm_sq_eq_sum, Finset.sum_comm]
  have hsum : ∀ i, ‖(WithLp.toLp 2 (y - r ᵥ* W)) i‖ ^ 2 ≤
      γ ^ 2 * ((∑ l, ‖r l‖ ^ 2) * ∑ l, ‖W l i‖ ^ 2) := fun i => by
    have h1 : ‖(WithLp.toLp 2 (y - r ᵥ* W)) i‖ = ‖y i - (r ᵥ* W) i‖ := rfl
    rw [h1]
    calc ‖y i - (r ᵥ* W) i‖ ^ 2 ≤ (γ * ∑ l, ‖r l‖ * ‖W l i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = γ ^ 2 * (∑ l, ‖r l‖ * ‖W l i‖) ^ 2 := by ring
      _ ≤ γ ^ 2 * ((∑ l, ‖r l‖ ^ 2) * ∑ l, ‖W l i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) (by positivity)
  calc ∑ i, ‖(WithLp.toLp 2 (y - r ᵥ* W)) i‖ ^ 2 ≤
        ∑ i, γ ^ 2 * ((∑ l, ‖r l‖ ^ 2) * ∑ l, ‖W l i‖ ^ 2) := Finset.sum_le_sum fun i _ => hsum i
    _ = γ ^ 2 * (∑ i, ∑ l, ‖W l i‖ ^ 2) * ∑ l, ‖r l‖ ^ 2 := by
        rw [← Finset.mul_sum]; simp_rw [← Finset.mul_sum]; ring
    _ = _ := by simp

/-- **One rounded step of the row recurrence**: let $\lvert s\rvert \le C\|\mathbf{H}\|_2$, the
stored $\mathbf{W}$ be $\mathbf{H} - s$ with an error at most $\boldsymbol{u}(\|\mathbf{H}\|_2 +
\lvert s\rvert)$, $0 \le \boldsymbol{u} \le 1/10$, $5N\boldsymbol{u} \le 1$ ($N = n + 1$), and
every entry of $\mathbf{y}$ within $((1 + 5\boldsymbol{u})^N - 1)\sum_l\lvert r_l\rvert
\lvert W_{li}\rvert$ of $(\mathbf{r}^{\mathsf T}\mathbf{W})_i$. Then
$$\|\mathbf{y} - \mathbf{r}^{\mathsf T}(\mathbf{H} - s)\| \le
12N^{3/2}\boldsymbol{u}\,(1 + C)\|\mathbf{H}\|_2\,\|\mathbf{r}\|,$$
the per-step hypothesis of `NLAlib.norm_toLp_sub_aeval_shiftPoly_row_le` with
$\eta = 12N^{3/2}\boldsymbol{u}$. [BanksGarzaVargasSrivastava2022, Lemma 4.5] has
$N^{3/2}\boldsymbol{u}$ (for the Hessenberg support of the recurrence) and leaves the
rounding of the shift implicit. -/
theorem norm_toLp_sub_vecMul_sub_smul_le {n : ℕ} {u C : ℝ} (hu : 0 ≤ u) (hu10 : u ≤ 1 / 10)
    (hNu : 5 * ((n + 1 : ℕ) : ℝ) * u ≤ 1) {H W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ}
    (hs : ‖s‖ ≤ C * specNorm H)
    (hW : specNorm (W - (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) ≤
      u * (specNorm H + ‖s‖))
    {r y : Fin (n + 1) → ℂ}
    (hy : ∀ i, ‖y i - (r ᵥ* W) i‖ ≤ ((1 + 5 * u) ^ (n + 1) - 1) * ∑ l, ‖r l‖ * ‖W l i‖) :
    ‖WithLp.toLp 2 (y - r ᵥ* (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))‖ ≤
      12 * ((n + 1 : ℕ) * √((n + 1 : ℕ) : ℝ) * u) * ((1 + C) * specNorm H) *
        ‖WithLp.toLp 2 r‖ := by
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  set L := (1 + C) * specNorm H
  have hN1 : 1 ≤ N := by simp only [N]; exact_mod_cast Nat.succ_pos n
  have hsq1 : 1 ≤ √N := Real.one_le_sqrt.mpr hN1
  have hHs : specNorm H + ‖s‖ ≤ L := by simp only [L]; linarith
  have hr0 := norm_nonneg (WithLp.toLp 2 r)
  have hγ0 : 0 ≤ (1 + 5 * u) ^ (n + 1) - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (a := 1 + 5 * u) (by linarith) (n := n + 1); linarith
  have hγ : (1 + 5 * u) ^ (n + 1) - 1 ≤ 10 * N * u := by
    have := one_add_pow_le_one_add_two_mul (u := 5 * u) (by positivity) (N := n + 1)
      (by simp only [N] at hNu; linarith)
    simp only [N]; push_cast at this ⊢; linarith
  have hS1 : specNorm (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ≤
      specNorm H + ‖s‖ := by
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_smul, specNorm_one, mul_one]
  have hWn : specNorm W ≤ (1 + u) * L := by
    have := specNorm_add_le (W - (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
    rw [sub_add_cancel] at this
    nlinarith
  have hF : frobNorm W ≤ √N * specNorm W := by
    simpa [N] using frobNorm_le_sqrt_card_mul_specNorm W
  have h1 := norm_toLp_sub_vecMul_le_of_forall hγ0 hy
  have h2 : ‖WithLp.toLp 2 (r ᵥ* (W - (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))))‖ ≤
      u * L * ‖WithLp.toLp 2 r‖ :=
    (norm_toLp_vecMul_le _ _).trans (mul_le_mul_of_nonneg_right
      (hW.trans (mul_le_mul_of_nonneg_left hHs hu)) hr0)
  have hsplit : y - r ᵥ* (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) =
      (y - r ᵥ* W) + r ᵥ* (W - (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) := by
    simp only [Matrix.vecMul_sub]; abel
  rw [hsplit, WithLp.toLp_add]
  have hL0 : 0 ≤ L := le_trans (by positivity) hHs
  have h3 : ((1 + 5 * u) ^ (n + 1) - 1) * frobNorm W * ‖WithLp.toLp 2 r‖ ≤
      10 * N * u * (√N * ((1 + u) * L)) * ‖WithLp.toLp 2 r‖ := by
    gcongr
    exact hF.trans (mul_le_mul_of_nonneg_left hWn (Real.sqrt_nonneg _))
  have hNs : 1 ≤ N * √N := by nlinarith
  calc _ ≤ ‖WithLp.toLp 2 (y - r ᵥ* W)‖ + u * L * ‖WithLp.toLp 2 r‖ :=
        (norm_add_le _ _).trans (by linarith)
    _ ≤ 10 * N * u * (√N * ((1 + u) * L)) * ‖WithLp.toLp 2 r‖ + u * L * ‖WithLp.toLp 2 r‖ := by
        linarith
    _ ≤ 12 * (N * √N * u) * L * ‖WithLp.toLp 2 r‖ := by
        have hA : 0 ≤ u * L * ‖WithLp.toLp 2 r‖ := by positivity
        have hB : 0 ≤ N * √N * u * L * ‖WithLp.toLp 2 r‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hNs hA, mul_le_mul_of_nonneg_right hu10 hB]

/-! ### The programs -/

variable {Op Tst : Type} [Has ScalarOp Op]

/-- **One entry of a rounded row product**: the entry `i` of $\mathbf{v}^{\mathsf T}\mathbf{A}$
for a stored vector `V` and order-$n$ matrix `A`, accumulated in the pair `Y[2i]` from $0$ by
$n$ rounded complex multiply–adds with the stored pair `O` (the number $1$); the two scratch
pairs `T`, `Z` are caller-owned. The interface is `[n, i] (V, A, O, T, Z) → (Y)`. -/
def rowEntry : Stmt Op Tst := ops% [n, i] (V, A, O, T, Z) → (Y) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * i]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * i + 1]);
  for l < n {
    run Pair.linearCombination [] (V[2 * l], O, A[2 * (i * n + l)], Y[2 * i], T, Z);
    call (Has.inj ScalarOp.copy) [] (Z) → (Y[2 * i]);
    call (Has.inj ScalarOp.copy) [] (Z[1]) → (Y[2 * i + 1])
  }
}

/-- The pair `rowEntry` stores at entry `i`, on the machine `M`, with the stored pair `o`. -/
def rowEntryPair (M : Machine ℝ) (o : ℝ × ℝ) {N : ℕ} (r : Fin N → ℂ)
    (W : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℝ × ℝ :=
  rowEntryWord M o (M.lit 0, M.lit 0) (vecGetD r) (vecGetD fun l => W l i) N

/-- One round of `NLAlib.ShiftedQR.rowEntry`: the rounded multiply–add into `Z` and the copy back to
the entry pair.
A step in the proof of `rowEntry_writes_word`. -/
private theorem rowEntry_round_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n i l : ℕ} {v a o t z y : ℕ × ℕ}
    {r : Fin (n + 1) → ℂ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {oo w : ℝ × ℝ}
    (hi : i < n + 1) (hl1 : l < n + 1)
    (hV : HoldsMatrix v (Matrix.replicateCol (Fin 1) r) m.store) (hA : HoldsMatrix a W m.store)
    (ho : m.store.readBlock o.1 o.2 2 = some [oo.1, oo.2])
    (hw0 : m.store.get y.1 (y.2 + 2 * i) = some w.1)
    (hw1 : m.store.get y.1 (y.2 + 2 * i + 1) = some w.2)
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1)
    (hy : y.2 + 2 * i + 2 ≤ m.store.len y.1) (hl : m.Live [v, a, o, t, z, y])
    (hsep : Fp.Disj (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2 ⊔
        Store.inBlock y.1 (y.2 + 2 * i) 2)
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))
        ⊔ Store.inBlock o.1 o.2 2))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (htY : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 (y.2 + 2 * i) 2))
    (hzY : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock y.1 (y.2 + 2 * i) 2)) :
    Writes .total I τ
      (.seq (.frame [] [⟨0, .var 2 + .const 2 * .var 8⟩, ⟨2, .var 4⟩,
          ⟨1, .var 3 + .const 2 * (.var 1 * .var 0 + .var 8)⟩,
          ⟨5, .var 7 + .const 2 * .var 1⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩]
          (Pair.linearCombination (Op := Op) (Tst := Tst)))
        (.seq (.call (Has.inj ScalarOp.copy) [] [⟨4, .var 6⟩] [⟨5, .var 7 + .const 2 * .var 1⟩])
          (.call (Has.inj ScalarOp.copy) [] [⟨4, .var 6 + .const 1⟩]
            [⟨5, .var 7 + .const 2 * .var 1 + .const 1⟩])))
      ((Env.frame [n + 1, i] [v, a, o, t, z, y]).pushIdx l)
      (Store.inBlock y.1 (y.2 + 2 * i) 2 ⊔ Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get y.1 (y.2 + 2 * i) = some (Pair.linearWords M ((r ⟨l, hl1⟩).re,
          (r ⟨l, hl1⟩).im) oo ((W ⟨l, hl1⟩ ⟨i, hi⟩).re, (W ⟨l, hl1⟩ ⟨i, hi⟩).im) w).1 ∧
        m'.store.get y.1 (y.2 + 2 * i + 1) = some (Pair.linearWords M ((r ⟨l, hl1⟩).re,
          (r ⟨l, hl1⟩).im) oo ((W ⟨l, hl1⟩ ⟨i, hi⟩).re, (W ⟨l, hl1⟩ ⟨i, hi⟩).im) w).2) m := by
  have hv0 := hV.get_re ⟨l, hl1⟩ 0
  have hv1 := hV.get_im ⟨l, hl1⟩ 0
  have ha0 := hA.get_re ⟨l, hl1⟩ ⟨i, hi⟩
  have ha1 := hA.get_im ⟨l, hl1⟩ ⟨i, hi⟩
  simp only [Fin.val_zero, zero_mul, zero_add, Matrix.replicateCol_apply] at hv0 hv1 ha0 ha1
  have ho0 := Store.get_of_readBlock ho (j := 0) (by norm_num) 0
  have ho1 := Store.get_of_readBlock ho (j := 1) (by norm_num) 0
  simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ] at ho0 ho1
  have hVl : Store.inBlock v.1 (v.2 + 2 * l) 2 ≤ Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hAl : Store.inBlock a.1 (a.2 + 2 * (i * (n + 1) + l)) 2 ≤
      Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) := by
    have := Idx.add_lt_mul hi hl1
    exact Fp.inBlock_le_inBlock (by omega) (by omega)
  set R := Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔
    Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock o.1 o.2 2
  have hblocks : Fp.blocks [(v.1, v.2 + 2 * l), o, (a.1, a.2 + 2 * (i * (n + 1) + l)),
      (y.1, y.2 + 2 * i)] [2, 2, 2, 2] ≤ R ⊔ Store.inBlock y.1 (y.2 + 2 * i) 2 := by
    simp only [Fp.blocks_cons, Fp.blocks_nil]
    exact sup_le (hVl.trans (by fp_sub)) (sup_le (by fp_sub)
      (sup_le (hAl.trans (by fp_sub)) (sup_le (by fp_sub) bot_le)))
  have hT : Fp.Disj (Store.inBlock t.1 t.2 2) (R ⊔ Store.inBlock y.1 (y.2 + 2 * i) 2) :=
    Fp.disj_sup_right.mpr ⟨hsep.mono (by fp_sub) le_rfl, htY⟩
  have hZ : Fp.Disj (Store.inBlock z.1 z.2 2) (R ⊔ Store.inBlock y.1 (y.2 + 2 * i) 2) :=
    Fp.disj_sup_right.mpr ⟨hsep.mono (by fp_sub) le_rfl, hzY⟩
  have hlc := Pair.linearCombination_writes (τ := τ) (m := m) hS
    (a := (v.1, v.2 + 2 * l)) (b := o) (x := (a.1, a.2 + 2 * (i * (n + 1) + l)))
    (y := (y.1, y.2 + 2 * i)) (t := t) (z := z) (av := ((r ⟨l, hl1⟩).re, (r ⟨l, hl1⟩).im))
    (bv := oo) (xv := ((W ⟨l, hl1⟩ ⟨i, hi⟩).re, (W ⟨l, hl1⟩ ⟨i, hi⟩).im)) (yv := w)
    (hT.mono le_rfl hblocks) (hZ.mono le_rfl hblocks) htz hv0 hv1 ho0 ho1 ha0 ha1 hw0 hw1 ht hz
  have hlive : v.1 < m.store.length ∧ a.1 < m.store.length ∧ o.1 < m.store.length ∧
      t.1 < m.store.length ∧ z.1 < m.store.length ∧ y.1 < m.store.length := by
    simpa [Mem.Live] using hl
  refine hlc.frame_seq_le rfl
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (by simp [Mem.Live, hlive]) (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hZ₁⟩
  have hz0 := Store.get_of_readBlock hZ₁ (j := 0) (by norm_num) 0
  have hz1 := Store.get_of_readBlock hZ₁ (j := 1) (by norm_num) 0
  simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ] at hz0 hz1
  refine (writes_call_un (hS .copy) (x := z) (z := (y.1, y.2 + 2 * i))
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) trivial hz0 rfl
    (by have := hfr₁.len_eq y.1; dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hY₂⟩
  have hz1' := hfr₂.keep (Store.readsOnly_get _ _ _)
    (hzY.symm.mono (by fp_sub) (by fp_sub)) hz1
  refine (writes_call_un (hS .copy) (x := (z.1, z.2 + 1)) (z := (y.1, y.2 + 2 * i + 1))
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval]) trivial hz1' rfl
    (by have := hfr₁.len_eq y.1; have := hfr₂.len_eq y.1; dsimp only; omega)).mono (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hY₃⟩
  refine ⟨hp₃.trans (hp₂.trans hp₁), ?_, hY₃⟩
  exact hfr₃.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hY₂

/-- One entry of the rounded row product on any scalar machine: with the vector
$\mathbf{r}$ stored at `V`, the order-$(n+1)$ matrix $\mathbf{W}$ at `A`, the pair `oo` at `O`,
and the scratch pairs `T`, `Z` and the entry pair `Y[2i]` apart from each other and from the
inputs, `rowEntry` stores at `Y[2i]` the pair `NLAlib.ShiftedQR.rowEntryPair`, and writes only
that pair and the scratch.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem rowEntry_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n i : ℕ} {v a o t z y : ℕ × ℕ}
    {r : Fin (n + 1) → ℂ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {oo : ℝ × ℝ}
    (hi : i < n + 1)
    (hV : HoldsMatrix v (Matrix.replicateCol (Fin 1) r) m.store) (hA : HoldsMatrix a W m.store)
    (ho : m.store.readBlock o.1 o.2 2 = some [oo.1, oo.2])
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1)
    (hy : y.2 + 2 * i + 2 ≤ m.store.len y.1) (hl : m.Live [v, a, o, t, z, y])
    (hsep : Fp.Disj (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2 ⊔
        Store.inBlock y.1 (y.2 + 2 * i) 2)
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))
        ⊔ Store.inBlock o.1 o.2 2))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (htY : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 (y.2 + 2 * i) 2))
    (hzY : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock y.1 (y.2 + 2 * i) 2)) :
    Writes .total I τ (rowEntry (Op := Op) (Tst := Tst))
      (Env.frame [n + 1, i] [v, a, o, t, z, y])
      (Store.inBlock y.1 (y.2 + 2 * i) 2 ⊔ Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get y.1 (y.2 + 2 * i) = some (rowEntryPair M oo r W ⟨i, hi⟩).1 ∧
        m'.store.get y.1 (y.2 + 2 * i + 1) = some (rowEntryPair M oo r W ⟨i, hi⟩).2) m := by
  set F := Store.inBlock y.1 (y.2 + 2 * i) 2 ⊔ Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2
  set R := Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔
    Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock o.1 o.2 2
  have hFR : Fp.Disj F R := hsep.mono (by fp_sub) le_rfl
  unfold rowEntry
  refine (writes_call_const (hS (.lit 0)) (z := (y.1, y.2 + 2 * i))
    (out := ⟨5, .var 7 + .const 2 * .var 1⟩) rfl trivial
    (by dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, h0⟩
  refine (writes_call_const (hS (.lit 0)) (z := (y.1, y.2 + 2 * i + 1))
    (out := ⟨5, .var 7 + .const 2 * .var 1 + .const 1⟩) rfl trivial
    (by have := hfr₁.len_eq y.1; dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, h1⟩
  have h0' := hfr₂.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm h0
  have hfr₁₂ : m.store.EqOff F m₂.store :=
    (hfr₁.trans' hfr₂).mono (by simp only [F]; fp_sub)
  refine (writes_loop (N := n + 1) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun l m' => m'.pos = m.pos ∧
      m'.store.get y.1 (y.2 + 2 * i) =
        some (rowEntryWord M oo (M.lit 0, M.lit 0) (vecGetD r) (vecGetD fun l => W l ⟨i, hi⟩) l).1 ∧
      m'.store.get y.1 (y.2 + 2 * i + 1) =
        some (rowEntryWord M oo (M.lit 0, M.lit 0) (vecGetD r) (vecGetD fun l => W l ⟨i, hi⟩) l).2)
    ⟨hp₂.trans hp₁, h0', h1⟩ ?_).mono le_rfl fun _ _ h => h
  intro l hl1 m' hfr ⟨hp', hw0, hw1⟩
  have hfr' : m.store.EqOff F m'.store := (hfr₁₂.trans' hfr).mono (sup_le (le_refl F) (le_refl F))
  have hround := rowEntry_round_writes (τ := τ) (m := m') (l := l) hS hi hl1
    (hV.of_eqOff hfr' (hFR.mono le_rfl (by fp_sub)))
    (hA.of_eqOff hfr' (hFR.mono le_rfl (by fp_sub)))
    (hfr'.keep (Store.readsOnly_readBlock _ _ _ _) (hFR.mono le_rfl (by fp_sub)) ho)
    hw0 hw1 (by rw [hfr'.len_eq]; exact ht) (by rw [hfr'.len_eq]; exact hz)
    (by rw [hfr'.len_eq]; exact hy) (hl.congr hfr'.length_eq) hsep htz htY hzY
  refine hround.mono le_rfl fun m'' _ ⟨hp'', hy0, hy1⟩ => ⟨hp''.trans hp', ?_, ?_⟩
  · simpa [rowEntryWord, vecGetD, hl1] using hy0
  · simpa [rowEntryWord, vecGetD, hl1] using hy1

/-- **The rounded row product** $\mathbf{v}^{\mathsf T}\mathbf{A}$ of a stored vector `V` and
order-$n$ matrix `A` into the vector `Y`, entry by entry (`NLAlib.ShiftedQR.rowEntry`), with the
stored pair `O` (the number $1$) and the caller-owned scratch pairs `T`, `Z`. The interface is
`[n] (V, A, O, T, Z) → (Y)`. -/
def rowMul : Stmt Op Tst := ops% [n] (V, A, O, T, Z) → (Y) {
  for i < n {
    run rowEntry [n, i] (V, A, O, T, Z, Y)
  }
}

/-- The vector `rowMul` stores, on the machine `M`, with the stored pair `o`. -/
def rowMulVec (M : Machine ℝ) (o : ℝ × ℝ) {N : ℕ} (r : Fin N → ℂ)
    (W : Matrix (Fin N) (Fin N) ℂ) : Fin N → ℂ :=
  fun i => pairToComplex (rowEntryPair M o r W i)

/-- The rounded row product on any scalar machine: with the vector $\mathbf{r}$ at `V`, the
matrix $\mathbf{W}$ at `A`, the pair `oo` at `O`, and the output vector and the two scratch pairs
apart from each other and from the inputs, `rowMul` stores at `Y` the vector
`NLAlib.ShiftedQR.rowMulVec`, and writes only `Y` and the scratch.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem rowMul_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {v a o t z y : ℕ × ℕ}
    {r : Fin (n + 1) → ℂ} {W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {oo : ℝ × ℝ}
    (hV : HoldsMatrix v (Matrix.replicateCol (Fin 1) r) m.store) (hA : HoldsMatrix a W m.store)
    (ho : m.store.readBlock o.1 o.2 2 = some [oo.1, oo.2])
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1)
    (hy : y.2 + 2 * (1 * (n + 1)) ≤ m.store.len y.1) (hl : m.Live [v, a, o, t, z, y])
    (hsep : Fp.Disj (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2 ⊔
        Store.inBlock y.1 y.2 (2 * (1 * (n + 1))))
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))
        ⊔ Store.inBlock o.1 o.2 2))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (htY : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
    (hzY : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock y.1 y.2 (2 * (1 * (n + 1))))) :
    Writes .total I τ (rowMul (Op := Op) (Tst := Tst)) (Env.frame [n + 1] [v, a, o, t, z, y])
      (Store.inBlock y.1 y.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock t.1 t.2 2 ⊔
        Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix y (Matrix.replicateCol (Fin 1) (rowMulVec M oo r W)) m'.store) m := by
  set Yb := Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))
  set R := Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔
    Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock o.1 o.2 2
  have hreg : ∀ i < n + 1, Store.inBlock y.1 (y.2 + 2 * i) 2 ≤ Yb := fun i hi =>
    Fp.inBlock_le_inBlock (by omega) (by omega)
  unfold rowMul
  refine (writes_loop_disjoint_prefix_scratch (N := n + 1)
    (region := fun i => Store.inBlock y.1 (y.2 + 2 * i) 2)
    (scratch := Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2)
    (result := fun i st => ∃ hi : i < n + 1,
      st.get y.1 (y.2 + 2 * i) = some (rowEntryPair M oo r W ⟨i, hi⟩).1 ∧
      st.get y.1 (y.2 + 2 * i + 1) = some (rowEntryPair M oo r W ⟨i, hi⟩).2)
    rfl (fun i hi => (hreg i hi).trans (by simp only [Yb]; fp_sub)) (by fp_sub)
    (fun i _ j _ hij => by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact Fp.disj_inBlock_of_le (by omega)
      · exact (Fp.disj_inBlock_of_le (by omega)).symm)
    (fun i hi => Fp.disj_sup_left.mpr ⟨htY.mono le_rfl (hreg i hi), hzY.mono le_rfl (hreg i hi)⟩)
    (fun i _ => fun s s' hg ⟨hi, h0, h1⟩ => ⟨hi,
      (hg y.1 (y.2 + 2 * i) ⟨rfl, by omega, by omega⟩).trans h0,
      (hg y.1 (y.2 + 2 * i + 1) ⟨rfl, by omega, by omega⟩).trans h1⟩) ?_).mono le_rfl ?_
  · intro i hi m' hfr
    have hFR : Fp.Disj (Fp.loopPrefix (fun i => Store.inBlock y.1 (y.2 + 2 * i) 2) i ⊔
        (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2)) R := by
      refine Fp.disj_sup_left.mpr ⟨?_, hsep.mono (by fp_sub) le_rfl⟩
      intro b x ⟨j, hj, hjx⟩ hR
      exact hsep b x (Or.inr (hreg j (by omega) b x hjx)) hR
    have hent := rowEntry_writes_word (τ := τ) (m := m') (i := i) hS hi
      (hV.of_eqOff hfr (hFR.mono le_rfl (by fp_sub)))
      (hA.of_eqOff hfr (hFR.mono le_rfl (by fp_sub)))
      (hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hFR.mono le_rfl (by fp_sub)) ho)
      (by rw [hfr.len_eq]; exact ht) (by rw [hfr.len_eq]; exact hz)
      (by rw [hfr.len_eq]; omega) (hl.congr hfr.length_eq)
      (hsep.mono (sup_le (by fp_sub) ((hreg i hi).trans (by fp_sub))) le_rfl) htz
      (htY.mono le_rfl (hreg i hi)) (hzY.mono le_rfl (hreg i hi))
    refine (hent.in_frame
      (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
      (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
      (hl.congr hfr.length_eq)).mono (by fp_sub) fun m'' _ ⟨hp, h0, h1⟩ => ⟨hp, hi, h0, h1⟩
  · intro m' _ ⟨hp, hall⟩
    refine ⟨hp, HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
    · obtain ⟨_, h0, _⟩ := hall i i.isLt
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simpa [rowMulVec, pairToComplex] using h0
    · obtain ⟨_, _, h1⟩ := hall i i.isLt
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simpa [rowMulVec, pairToComplex] using h1

/-- **One rounded step of the row recurrence** $\mathbf{v} \gets
\mathrm{fl}(\mathbf{v}^{\mathsf T}(\mathbf{A} - s))$, in place in `V`: the order-$n$ matrix `A`
copied into the scratch `W`, the shift pair `S` subtracted from its diagonal
(`NLAlib.ShiftedQR.shiftDiagonal`), the rounded row product into the scratch vector `Y`
(`NLAlib.ShiftedQR.rowMul`, with the pair `O` and the scratch pairs `T`, `Z`), and `Y` copied
back. The interface is `[n] (V, A, S, O, W, T, Z, Y) → (V)`. -/
def rowShiftStep : Stmt Op Tst := ops% [n] (V, A, S, O, W, T, Z, Y) → (V) {
  run (unaryMap (Has.inj ScalarOp.copy)) [2 * (n * n)] (A, W);
  run shiftDiagonal [n] (W, S, W);
  run rowMul [n] (V, W, O, T, Z, Y);
  run (unaryMap (Has.inj ScalarOp.copy)) [2 * n] (Y, V)
}

/-- One rounded step of the row recurrence on any scalar machine: with $\mathbf{r}$ at `V`,
$\mathbf{H}$ at `A`, the shift $s$ at `S`, the pair `oo` at `O`, and the scratch views `W`
(a matrix), `T`, `Z` (pairs), `Y` (a vector) apart from each other and from the inputs,
`rowShiftStep` stores at `V` the row product `NLAlib.ShiftedQR.rowMulVec` of $\mathbf{r}$ and the
machine shift `NLAlib.ShiftedQR.machineShiftedPrefix` of $\mathbf{H}$, and writes only `V` and
the scratch.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem rowShiftStep_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {v a s o w t z y : ℕ × ℕ}
    {r : Fin (n + 1) → ℂ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {sh : ℂ} {oo : ℝ × ℝ}
    (hV : HoldsMatrix v (Matrix.replicateCol (Fin 1) r) m.store) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [sh.re, sh.im])
    (ho : m.store.readBlock o.1 o.2 2 = some [oo.1, oo.2])
    (hw : w.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len w.1)
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1)
    (hy : y.2 + 2 * (1 * (n + 1)) ≤ m.store.len y.1) (hl : m.Live [v, a, s, o, w, t, z, y])
    (hsep : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock t.1 t.2 2 ⊔
        Store.inBlock z.1 z.2 2 ⊔ Store.inBlock y.1 y.2 (2 * (1 * (n + 1))))
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))
        ⊔ Store.inBlock s.1 s.2 2 ⊔ Store.inBlock o.1 o.2 2))
    (hwt : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock t.1 t.2 2))
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock z.1 z.2 2))
    (hwy : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (hty : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
    (hzy : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock y.1 y.2 (2 * (1 * (n + 1))))) :
    Writes .total I τ (rowShiftStep (Op := Op) (Tst := Tst))
      (Env.frame [n + 1] [v, a, s, o, w, t, z, y, v])
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock t.1 t.2 2 ⊔
          Store.inBlock z.1 z.2 2 ⊔ Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix v (Matrix.replicateCol (Fin 1)
        (rowMulVec M oo r (machineShiftedPrefix M H sh (n + 1)))) m'.store) m := by
  have hlive : v.1 < m.store.length ∧ a.1 < m.store.length ∧ s.1 < m.store.length ∧
      o.1 < m.store.length ∧ w.1 < m.store.length ∧ t.1 < m.store.length ∧
      z.1 < m.store.length ∧ y.1 < m.store.length := by simpa [Mem.Live] using hl
  unfold rowShiftStep
  have hc1 := unaryMap_writes_of_disj_or_eq (md := .total) (τ := τ) (m := m) (f := id) (hS .copy)
    (Or.inl (hsep.symm.mono (by fp_sub) (by fp_sub))) hA hw
  refine hc1.frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (by simp [Mem.Live, hlive]) (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hW₁⟩
  rw [List.map_id] at hW₁
  have hs₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hsep.mono (by fp_sub) (by fp_sub)) hs
  have hsh := shiftDiagonal_writes_word (τ := τ) (m := m₁) (n := n + 1) (b := w) (a := s) hS
    (by simp [Mem.Live, hfr₁.length_eq, hlive]) hW₁ hs₁ (hsep.mono (by fp_sub) (by fp_sub))
  refine hsh.frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (by simp [Mem.Live, hfr₁.length_eq, hlive]) (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hW₂⟩
  have hfr₁₂ := hfr₁.trans' hfr₂
  have hD : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔
        Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 2 ⊔
          Store.inBlock o.1 o.2 2) := Fp.disj_sup_left.mpr
    ⟨hsep.mono (by fp_sub) le_rfl, hsep.mono (by fp_sub) le_rfl⟩
  have hV₂ := hV.of_eqOff hfr₁₂ (hD.mono le_rfl (by fp_sub))
  have ho₂ := hfr₁₂.keep (Store.readsOnly_readBlock _ _ _ _) (hD.mono le_rfl (by fp_sub)) ho
  have hrm := rowMul_writes_word (τ := τ) (m := m₂) (a := w) hS hV₂ hW₂ ho₂
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact ht) (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hz)
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hy)
    (by simp [Mem.Live, hfr₁.length_eq, hfr₂.length_eq, hlive])
    (Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hsep.mono (by fp_sub) (by fp_sub),
      Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hwt.symm, hwz.symm⟩, hwy.symm⟩⟩,
      hsep.mono (by fp_sub) (by fp_sub)⟩) htz hty hzy
  refine hrm.frame_seq_le (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (by simp [Mem.Live, hfr₁.length_eq, hfr₂.length_eq, hlive]) (by fp_sub) ?_
  intro m₃ hfr₃ ⟨hp₃, hY₃⟩
  have hvroom : v.2 + 2 * (n + 1) ≤ m₃.store.len v.1 := by
    rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
    have := Store.le_len_of_readBlock hV (by positivity)
    simpa using this
  have hY₃' : m₃.store.readBlock y.1 y.2 (2 * (n + 1)) =
      some (matrixWords (Matrix.replicateCol (Fin 1)
        (rowMulVec M oo r (machineShiftedPrefix M H sh (n + 1))))) := by
    simpa [HoldsMatrix] using hY₃
  have hYV : Fp.Disj (Store.inBlock y.1 y.2 (2 * (n + 1)))
      (Store.inBlock v.1 v.2 (2 * (n + 1))) := by
    have := hsep.mono (show Store.inBlock y.1 y.2 (2 * (1 * (n + 1))) ≤ _ by fp_sub)
      (show Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ≤ _ by fp_sub)
    simpa using this
  have hc2 := unaryMap_writes_of_disj_or_eq (md := .total) (τ := τ) (m := m₃) (f := id)
    (hS .copy) (Or.inl hYV) hY₃' hvroom
  refine (hc2.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, Env.frame, IExp.eval])
    (by simp [Mem.Live, hfr₁.length_eq, hfr₂.length_eq, hfr₃.length_eq, hlive])).mono
    (by simp) ?_
  intro m₄ _ ⟨hp₄, hV₄⟩
  refine ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), ?_⟩
  simpa [HoldsMatrix] using hV₄

/-- The rounded row product is accurate entrywise: under the standard model with
$0 \le \boldsymbol{u} \le 1/100$, every entry of `NLAlib.ShiftedQR.rowMulVec` with the pair of
$1$ is within $((1 + 5\boldsymbol{u})^N - 1)\sum_l\lvert r_l\rvert\lvert W_{li}\rvert$ of
$(\mathbf{r}^{\mathsf T}\mathbf{W})_i$. -/
theorem norm_rowMulVec_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) {N : ℕ} (r : Fin N → ℂ) (W : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    ‖rowMulVec M (1, 0) r W i - (r ᵥ* W) i‖ ≤
      ((1 + 5 * u) ^ N - 1) * ∑ l, ‖r l‖ * ‖W l i‖ := by
  have h0 : M.lit 0 = 0 := by simpa using hM.lit 0
  have h := norm_rowEntryWord_sub_le hM hu hu' (vecGetD r) (vecGetD fun l => W l i) N
  have e1 : ∑ j ∈ Finset.range N, vecGetD r j * vecGetD (fun l => W l i) j = (r ᵥ* W) i := by
    rw [Matrix.vecMul, dotProduct, Finset.sum_range fun j =>
      vecGetD r j * vecGetD (fun l => W l i) j]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [vecGetD, l.isLt]
  have e2 : ∑ j ∈ Finset.range N, ‖vecGetD r j‖ * ‖vecGetD (fun l => W l i) j‖ =
      ∑ l, ‖r l‖ * ‖W l i‖ := by
    rw [Finset.sum_range fun j => ‖vecGetD r j‖ * ‖vecGetD (fun l => W l i) j‖]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [vecGetD, l.isLt]
  rw [e1, e2] at h
  simpa [rowMulVec, rowEntryPair, h0] using h

/-- **One rounded step of the row recurrence, as a relative error**: under the standard model
with $0 \le \boldsymbol{u} \le 1/100$ and $5N\boldsymbol{u} \le 1$ ($N = n + 1$), for a shift
$\lvert s\rvert \le C\|\mathbf{H}\|_2$ the vector `rowShiftStep` stores,
$\widehat{\mathbf{r}}' = $ `rowMulVec M (1, 0) r (machineShiftedPrefix M H s N)`, satisfies
$$\|\widehat{\mathbf{r}}' - \mathbf{r}^{\mathsf T}(\mathbf{H} - s)\| \le
12N^{3/2}\boldsymbol{u}\,(1 + C)\|\mathbf{H}\|_2\,\|\mathbf{r}\|.$$
[BanksGarzaVargasSrivastava2022, Lemma 4.5], with the shift rounded. -/
theorem norm_toLp_rowMulVec_sub_le {M : Machine ℝ} {u C : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (hu' : u ≤ 1 / 100) {n : ℕ} (hNu : 5 * ((n + 1 : ℕ) : ℝ) * u ≤ 1)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {s : ℂ} (hs : ‖s‖ ≤ C * specNorm H)
    (r : Fin (n + 1) → ℂ) :
    ‖WithLp.toLp 2 (rowMulVec M (1, 0) r (machineShiftedPrefix M H s (n + 1)) -
        r ᵥ* (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))‖ ≤
      12 * ((n + 1 : ℕ) * √((n + 1 : ℕ) : ℝ) * u) * ((1 + C) * specNorm H) *
        ‖WithLp.toLp 2 r‖ :=
  norm_toLp_sub_vecMul_sub_smul_le hu (by linarith) hNu hs
    (specNorm_machineShiftedPrefix_sub_le hM hu H s) fun i => norm_rowMulVec_sub_le hM hu hu' r _ i

/-- **The start of the row recurrence**: the vector `V` of length $n$ set to
$\mathbf{e}_{n-1}$ (zeros, then the literal $1$ in the last entry) and the pair `O` to the
literals $(1, 0)$. The interface is `[n] () → (V, O)`. -/
def rowInit : Stmt Op Tst := ops% [n] () → (V, O) {
  call (Has.inj (ScalarOp.lit 1)) [] () → (O);
  call (Has.inj (ScalarOp.lit 0)) [] () → (O[1]);
  for i < n {
    call (Has.inj (ScalarOp.lit 0)) [] () → (V[2 * i]);
    call (Has.inj (ScalarOp.lit 0)) [] () → (V[2 * i + 1])
  };
  call (Has.inj (ScalarOp.lit 1)) [] () → (V[2 * n - 2])
}

/-- The vector `rowInit` stores, on the machine `M`: the literal $1$ in the last entry, the
literal $0$ elsewhere. -/
def rowInitVec (M : Machine ℝ) (n : ℕ) : Fin (n + 1) → ℂ :=
  fun i => if i = Fin.last n then ⟨M.lit 1, M.lit 0⟩ else ⟨M.lit 0, M.lit 0⟩

/-- With exact literals $0$ and $1$ the start vector is $\mathbf{e}_n$. -/
theorem rowInitVec_eq {M : Machine ℝ} (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (n : ℕ) :
    rowInitVec M n = Pi.single (Fin.last n) 1 := by
  funext i
  by_cases hi : i = Fin.last n <;> simp [rowInitVec, hi, h0, h1, Complex.ext_iff]

/-- The start of the row recurrence on any scalar machine: `rowInit` stores
`NLAlib.ShiftedQR.rowInitVec` at `V` and the literal pair $(1, 0)$ at `O`, and writes only
these.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem rowInit_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {v o : ℕ × ℕ}
    (hv : v.2 + 2 * (1 * (n + 1)) ≤ m.store.len v.1) (ho : o.2 + 2 ≤ m.store.len o.1)
    (hvo : Fp.Disj (Store.inBlock v.1 v.2 (2 * (1 * (n + 1)))) (Store.inBlock o.1 o.2 2)) :
    Writes .total I τ (rowInit (Op := Op) (Tst := Tst)) (Env.frame [n + 1] [v, o])
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock o.1 o.2 2)
      (fun m' => m'.pos = m.pos ∧
        HoldsMatrix v (Matrix.replicateCol (Fin 1) (rowInitVec M n)) m'.store ∧
        m'.store.readBlock o.1 o.2 2 = some [M.lit 1, M.lit 0]) m := by
  unfold rowInit
  refine (writes_call_const (hS (.lit 1)) (z := o) (out := ⟨1, .var 2⟩) rfl trivial
    (by omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hO0⟩
  refine (writes_call_const (hS (.lit 0)) (z := (o.1, o.2 + 1))
    (out := ⟨1, .var 2 + .const 1⟩) rfl trivial
    (by have := hfr₁.len_eq o.1; dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hO1⟩
  have hO0' := hfr₂.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_le (by omega)).symm hO0
  have hlen₂ : ∀ b, m₂.store.len b = m.store.len b := fun b => by
    rw [hfr₂.len_eq, hfr₁.len_eq]
  refine (writes_loop_disjoint_prefix (N := n + 1) (F := Store.inBlock v.1 v.2 (2 * (1 * (n + 1))))
    (region := fun i => Store.inBlock v.1 (v.2 + 2 * i) 2)
    (result := fun i st => st.get v.1 (v.2 + 2 * i) = some (M.lit 0) ∧
      st.get v.1 (v.2 + 2 * i + 1) = some (M.lit 0)) rfl
    (fun i hi => Fp.inBlock_le_inBlock (by omega) (by omega))
    (fun i _ j _ hij => by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact Fp.disj_inBlock_of_le (by omega)
      · exact (Fp.disj_inBlock_of_le (by omega)).symm)
    (fun i _ => fun s s' hg ⟨h0, h1⟩ =>
      ⟨(hg v.1 (v.2 + 2 * i) ⟨rfl, by omega, by omega⟩).trans h0,
       (hg v.1 (v.2 + 2 * i + 1) ⟨rfl, by omega, by omega⟩).trans h1⟩) ?_).seq_le
    (by fp_sub) ?_
  · intro i hi m' hfr
    have hl' : ∀ b, m'.store.len b = m.store.len b := fun b => by rw [hfr.len_eq, hlen₂]
    refine (writes_call_const (hS (.lit 0)) (z := (v.1, v.2 + 2 * i))
      (out := ⟨0, .var 1 + .const 2 * .var 3⟩) rfl trivial
      (by have := hl' v.1; dsimp only; omega)).seq_le (by fp_sub) ?_
    intro m'' hfr' ⟨hp', h0⟩
    refine (writes_call_const (hS (.lit 0)) (z := (v.1, v.2 + 2 * i + 1))
      (out := ⟨0, .var 1 + .const 2 * .var 3 + .const 1⟩) rfl trivial
      (by have := hl' v.1; have := hfr'.len_eq v.1; dsimp only; omega)).mono (by fp_sub) ?_
    intro m''' hfr'' ⟨hp'', h1⟩
    exact ⟨hp''.trans hp', hfr''.keep (Store.readsOnly_get _ _ _)
      (Fp.disj_inBlock_of_le (by omega)).symm h0, h1⟩
  intro m₃ hfr₃ ⟨hp₃, hall⟩
  have hO0₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (hvo.mono le_rfl (by fp_sub)) hO0'
  have hO1₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (hvo.mono le_rfl (by fp_sub)) hO1
  refine (writes_call_const (hS (.lit 1)) (z := (v.1, v.2 + 2 * n))
    (out := ⟨0, .var 1 + (.const 2 * .var 0 - .const 2)⟩)
    (by simp [Operand.eval, Env.frame, IExp.eval]; omega) trivial
    (by have := hfr₃.len_eq v.1; have := hlen₂ v.1; dsimp only; omega)).mono (by fp_sub) ?_
  intro m₄ hfr₄ ⟨hp₄, hlast⟩
  refine ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), HoldsMatrix.of_get (fun i j => ?_)
    (fun i j => ?_), ?_⟩
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    by_cases hi : i = Fin.last n
    · subst hi; simpa [rowInitVec] using hlast
    · have hin : (i : ℕ) < n := by
        have := i.isLt; have : (i : ℕ) ≠ n := fun h => hi (Fin.ext h); omega
      have := hfr₄.keep (Store.readsOnly_get _ _ _)
        (Fp.disj_inBlock_of_le (by omega)).symm (hall i i.isLt).1
      simpa [rowInitVec, hi] using this
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    by_cases hi : i = Fin.last n
    · subst hi
      have := hfr₄.keep (Store.readsOnly_get _ _ _)
        (Fp.disj_inBlock_of_le (by simp)) (hall (Fin.last n) (by simp)).2
      simpa [rowInitVec] using this
    · have hin : (i : ℕ) < n := by
        have := i.isLt; have : (i : ℕ) ≠ n := fun h => hi (Fin.ext h); omega
      have := hfr₄.keep (Store.readsOnly_get _ _ _)
        (Fp.disj_inBlock_of_le (by omega)).symm (hall i i.isLt).2
      simpa [rowInitVec, hi] using this
  · have h0 := hfr₄.keep (Store.readsOnly_get _ _ _) (hvo.mono (by fp_sub) (by fp_sub)) hO0₃
    have h1 := hfr₄.keep (Store.readsOnly_get _ _ _) (hvo.mono (by fp_sub) (by fp_sub)) hO1₃
    rw [Store.readBlock_eq_some_iff]
    refine ⟨rfl, fun k hk => ?_⟩
    have hk' : k < 2 := hk
    interval_cases k
    · simpa using h0
    · simpa using h1

/-- The words of the entries of a list of complex numbers stored as interleaved pairs. -/
theorem getD_flatMap_pair (zs : List ℂ) {j : ℕ} (hj : j < zs.length) :
    (zs.flatMap fun z => [z.re, z.im]).getD (2 * j) 0 = (zs.getD j 0).re ∧
      (zs.flatMap fun z => [z.re, z.im]).getD (2 * j + 1) 0 = (zs.getD j 0).im := by
  induction zs generalizing j with
  | nil => simp at hj
  | cons z zs ih =>
    cases j with
    | zero => simp
    | succ j =>
      have := ih (j := j) (by simpa using hj)
      rw [List.flatMap_cons, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simpa only [List.cons_append, List.nil_append, List.getD_cons_succ] using this


/-- The pair of entry $j$ of a list of complex numbers stored as interleaved pairs. -/
theorem readBlock_pair_of_flatMap {s : Store ℝ} {b : ℕ × ℕ} {zs : List ℂ}
    (h : s.readBlock b.1 b.2 (2 * zs.length) = some (zs.flatMap fun z => [z.re, z.im]))
    {j : ℕ} (hj : j < zs.length) :
    s.readBlock b.1 (b.2 + 2 * j) 2 = some [(zs.getD j 0).re, (zs.getD j 0).im] := by
  obtain ⟨h0, h1⟩ := getD_flatMap_pair zs hj
  have g0 := Store.get_of_readBlock h (j := 2 * j) (by omega) 0
  have g1 := Store.get_of_readBlock h (j := 2 * j + 1) (by omega) 0
  rw [h0] at g0; rw [h1] at g1
  rw [Store.readBlock_eq_some_iff]
  refine ⟨rfl, fun k hk => ?_⟩
  have hk' : k < 2 := hk
  interval_cases k
  · simpa using g0
  · simpa [Nat.add_assoc] using g1

/-- **The row recurrence**: $k$ rounded steps (`NLAlib.ShiftedQR.rowShiftStep`) in place on
`V` with the shifts `S[2j]`, $j < k$. The interface is `[n, k] (V, A, S, O, W, T, Z, Y) → (V)`. -/
def rowPolyLoop : Stmt Op Tst := ops% [n, k] (V, A, S, O, W, T, Z, Y) → (V) {
  for j < k {
    run rowShiftStep [n] (V, A, S[2 * j], O, W, T, Z, Y, V)
  }
}

/-- The vectors of the rounded row recurrence on the machine `M`: from $\mathbf{r}_0$, step $j$
is the row product `NLAlib.ShiftedQR.rowMulVec` with the machine shift of $\mathbf{H}$ by the
$j$-th shift. -/
def rowPolyVec (M : Machine ℝ) (o : ℝ × ℝ) {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ss : List ℂ) (r₀ : Fin (n + 1) → ℂ) : ℕ → Fin (n + 1) → ℂ
  | 0 => r₀
  | j + 1 => rowMulVec M o (rowPolyVec M o H ss r₀ j)
      (machineShiftedPrefix M H (ss.getD j 0) (n + 1))


/-- The row recurrence on any scalar machine: with $\mathbf{r}_0$ at `V`, $\mathbf{H}$ at
`A`, the shifts `ss` stored as pairs at `S`, the pair `oo` at `O`, the scratch views `W`, `T`,
`Z`, `Y` apart from each other and from the inputs, and `V` apart from the other inputs,
`rowPolyLoop` stores at `V` the vector `NLAlib.ShiftedQR.rowPolyVec` after all the shifts, and
writes only `V` and the scratch.
Shared by the trees of `NLAlib.ShiftedQR.shqrRoutine` and
`NLAlib.ShiftedQR.shqrSmallEigRoutine`, on their scratch. -/
theorem rowPolyLoop_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {v a s o w t z y : ℕ × ℕ}
    {r₀ : Fin (n + 1) → ℂ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ}
    {oo : ℝ × ℝ}
    (hV : HoldsMatrix v (Matrix.replicateCol (Fin 1) r₀) m.store) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) = some (ss.flatMap fun z => [z.re, z.im]))
    (ho : m.store.readBlock o.1 o.2 2 = some [oo.1, oo.2])
    (hw : w.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len w.1)
    (ht : t.2 + 2 ≤ m.store.len t.1) (hz : z.2 + 2 ≤ m.store.len z.1)
    (hy : y.2 + 2 * (1 * (n + 1)) ≤ m.store.len y.1) (hl : m.Live [v, a, s, o, w, t, z, y])
    (hsep : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock t.1 t.2 2 ⊔
        Store.inBlock z.1 z.2 2 ⊔ Store.inBlock y.1 y.2 (2 * (1 * (n + 1))))
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))
        ⊔ Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock o.1 o.2 2))
    (hvin : Fp.Disj (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * ss.length) ⊔
        Store.inBlock o.1 o.2 2))
    (hwt : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock t.1 t.2 2))
    (hwz : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock z.1 z.2 2))
    (hwy : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (hty : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
    (hzy : Fp.Disj (Store.inBlock z.1 z.2 2) (Store.inBlock y.1 y.2 (2 * (1 * (n + 1))))) :
    Writes .total I τ (rowPolyLoop (Op := Op) (Tst := Tst))
      (Env.frame [n + 1, ss.length] [v, a, s, o, w, t, z, y, v])
      (Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock t.1 t.2 2 ⊔
          Store.inBlock z.1 z.2 2 ⊔ Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix v
        (Matrix.replicateCol (Fin 1) (rowPolyVec M oo H ss r₀ ss.length)) m'.store) m := by
  set Sc := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock t.1 t.2 2 ⊔
    Store.inBlock z.1 z.2 2 ⊔ Store.inBlock y.1 y.2 (2 * (1 * (n + 1)))
  set F := Store.inBlock v.1 v.2 (2 * (1 * (n + 1))) ⊔ Sc
  have hFin : Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * ss.length) ⊔ Store.inBlock o.1 o.2 2) :=
    Fp.disj_sup_left.mpr ⟨hvin, hsep.mono le_rfl (by fp_sub)⟩
  unfold rowPolyLoop
  refine writes_loop (N := ss.length) rfl (fun _ => F) (fun _ _ => le_rfl)
    (fun j m' => m'.pos = m.pos ∧
      HoldsMatrix v (Matrix.replicateCol (Fin 1) (rowPolyVec M oo H ss r₀ j)) m'.store)
    ⟨rfl, hV⟩ ?_
  intro j hj m' hfr ⟨hp', hV'⟩
  have hsj := readBlock_pair_of_flatMap
    (hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hFin.mono le_rfl (by fp_sub)) hs) hj
  have hSj : Store.inBlock s.1 (s.2 + 2 * j) 2 ≤ Store.inBlock s.1 s.2 (2 * ss.length) :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hstep := rowShiftStep_writes_word (τ := τ) (m := m') (s := (s.1, s.2 + 2 * j)) hS hV'
    (hA.of_eqOff hfr (hFin.mono le_rfl (by fp_sub))) hsj
    (hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hFin.mono le_rfl (by fp_sub)) ho)
    (by rw [hfr.len_eq]; exact hw) (by rw [hfr.len_eq]; exact ht) (by rw [hfr.len_eq]; exact hz)
    (by rw [hfr.len_eq]; exact hy) (by simpa [Mem.Live, hfr.length_eq] using hl)
    (hsep.mono le_rfl (sup_le (sup_le (sup_le le_sup_left le_sup_right |>.trans
      (by fp_sub)) (hSj.trans (by fp_sub))) (by fp_sub))) hwt hwz hwy htz hty hzy
  refine (hstep.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame, Env.pushIdx])
    (by simp [Operand.evalList, Operand.eval, Env.frame, Env.pushIdx, IExp.eval])
    (by simp only [Mem.Live, List.mem_cons, List.not_mem_nil] at hl ⊢
        rw [hfr.length_eq]; aesop)).mono le_rfl fun m'' _ ⟨hp'', hV''⟩ =>
      ⟨hp''.trans hp', by simpa [rowPolyVec] using hV''⟩

end NLAlib.ShiftedQR
