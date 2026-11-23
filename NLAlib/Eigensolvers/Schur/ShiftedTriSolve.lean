/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.StoredProducts
public import NLAlib.Matrix.Perturbation.ComponentwiseBackward
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Eigensolvers.ShiftedQR.Division

/-!
# Rounded shifted back substitution with a pivot floor

The eigenvector of an upper triangular $\mathbf{T}$ for its $j$-th diagonal entry is
$(\mathbf{x}; 1; \mathbf{0})$ with $(\mathbf{T}_{11} - t_{jj}\mathbf{I})\mathbf{x} =
-\mathbf{t}_{1j}$, $\mathbf{T}_{11}$ the leading block of order $j$ (LAPACK `xTREVC`). The
program `NLAlib.shiftedTriSolve` solves this system by rounded back substitution, $i = j - 1,
\dots, 0$: the pivot $\hat m = \mathrm{fl}(t_{ii} - t_{jj})$, floored to $s_{\min}$ (and the flag
set) when $\mathrm{fl}(\lvert\hat m\rvert^2) \le \mathrm{fl}(s_{\min}^2)$; the sum
$\hat s_i = \mathrm{fl}(t_{ij} + \sum_{i < k < j}t_{ik}\hat x_k)$ by rounded complex
multiply–adds; and $\hat x_i = -\mathrm{fl}(\hat s_i/\hat m)$. Under the standard model the
computed column is a componentwise backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y}
= \mathbf{0}$ (`NLAlib.IsComponentwiseBackwardSolution`), with a diagonal floor only when a pivot
was floored, and no pivot is floored when the diagonal gaps exceed $2s_{\min}$.

## Main definitions

* `NLAlib.shiftedTriSolve`: the program.
* `NLAlib.shiftedTriSolveWord`, `NLAlib.shiftedTriSolveColumn`, `NLAlib.shiftedTriSolveFlag`: the
  words it computes on a machine, the column $(\hat{\mathbf{x}}; 1; \mathbf{0})$ and the flag.

## Main results

* `NLAlib.shiftedTriSolve_writes_word`: the program stores the computed words and the flag.
* `NLAlib.shiftedTriSolve_isComponentwiseBackwardSolution`: the computed column is a componentwise
  backward solution.
* `NLAlib.shiftedTriSolve_flag`: no pivot is floored when the diagonal gaps exceed $2s_{\min}$.
* `NLAlib.shiftedTriSolve_writes`: the program under the standard model.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

/-! ### The program -/

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **Rounded shifted back substitution with a pivot floor**: `[N, j] (T, Sm, Y, G) → (Y, G)`
solves $(\mathbf{T}_{11} - t_{jj}\mathbf{I})\mathbf{x} = -\mathbf{t}_{1j}$ for the leading block
of order $j$ of the stored $\mathbf{T}$ of order $N$ (column-major pairs) into the first $j$
entries of column $j$ of `Y`, $i = j - 1, \dots, 0$: the pivot $\mathrm{fl}(t_{ii} - t_{jj})$,
replaced by the word `Sm` (and the flag `G` set to $1$) when its rounded squared modulus is at
most the rounded square of `Sm`; the sum $\mathrm{fl}(t_{ij} + \sum_{i < k < j}t_{ik}x_k)$ by
rounded complex multiply–adds; the negated rounded quotient. The flag is not cleared.
Algorithm: dense-eigendecomposition -/
def shiftedTriSolve : Impl O Q := opsImpl% [N, j] (T, Sm, Y, G) → (Y, G) {
  let One ← alloc 2;
  let M ← alloc 2;
  let S ← alloc 2;
  let W ← alloc 2;
  let R ← alloc 2;
  let D ← alloc 4;
  let P ← alloc 2;
  call (Has.inj (ScalarOp.lit 1)) [] () → (One);
  call (Has.inj (ScalarOp.lit 0)) [] () → (One[1]);
  call (Has.inj ScalarOp.mul) [] (Sm, Sm) → (P[1]);
  for r < j {
    call (Has.inj ScalarOp.sub) []
      (T[2 * ((j - 1 - r) * N + (j - 1 - r))], T[2 * (j * N + j)]) → (M);
    call (Has.inj ScalarOp.sub) []
      (T[2 * ((j - 1 - r) * N + (j - 1 - r)) + 1], T[2 * (j * N + j) + 1]) → (M[1]);
    call (Has.inj ScalarOp.mul) [] (M, M) → (P);
    call (Has.inj ScalarOp.mul) [] (M[1], M[1]) → (W);
    call (Has.inj ScalarOp.add) [] (P, W) → (P);
    if (Has.inj CmpTst.le) [] (P, P[1]) {
      call (Has.inj ScalarOp.copy) [] (Sm) → (M);
      call (Has.inj (ScalarOp.lit 0)) [] () → (M[1]);
      call (Has.inj IndexOp.lit) [1] () → (G)
    } else { skip };
    call (Has.inj ScalarOp.copy) [] (T[2 * (j * N + (j - 1 - r))]) → (S);
    call (Has.inj ScalarOp.copy) [] (T[2 * (j * N + (j - 1 - r)) + 1]) → (S[1]);
    for l < r {
      run Pair.linearCombination []
        (T[2 * ((j - r + l) * N + (j - 1 - r))], One, Y[2 * (j * N + (j - r + l))], S, W, R);
      call (Has.inj ScalarOp.copy) [] (R) → (S);
      call (Has.inj ScalarOp.copy) [] (R[1]) → (S[1])
    };
    run ShiftedQR.complexDivideWithScratch [] (S, M, D, R);
    call (Has.inj ScalarOp.neg) [] (R) → (Y[2 * (j * N + (j - 1 - r))]);
    call (Has.inj ScalarOp.neg) [] (R[1]) → (Y[2 * (j * N + (j - 1 - r)) + 1])
  }
}

end Program

/-! ### The computed words -/

/-- The entry $(i, k)$ of a square matrix at natural indices, $0$ outside. -/
def entryAt {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) (i k : ℕ) : ℂ :=
  if h : i < N ∧ k < N then T ⟨i, h.1⟩ ⟨k, h.2⟩ else 0

/-- **The words of the shifted back substitution** on the machine `M` for column `j`, after the
rows $j - 1, \dots, j - r$: the computed entries (at natural indices) and whether a pivot was
floored. -/
noncomputable def shiftedTriSolveWord (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : ℕ → (ℕ → ℂ) × Bool
  | 0 => (fun _ => 0, false)
  | r + 1 =>
    let st := shiftedTriSolveWord M T smin j r
    let i := j - 1 - r
    let m : ℂ := ⟨M.sub (entryAt T i i).re (entryAt T j j).re,
      M.sub (entryAt T i i).im (entryAt T j j).im⟩
    let fl := decide (M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ M.mul smin smin)
    let m' : ℂ := if fl then ⟨smin, M.lit 0⟩ else m
    let s := (List.range r).foldl (fun s l =>
      linearComplex M (entryAt T i (j - r + l)) ⟨M.lit 1, M.lit 0⟩ (st.1 (j - r + l)) s)
      (entryAt T i j)
    let q := Pair.divideWords M (s.re, s.im) (m'.re, m'.im)
    (Function.update st.1 i ⟨M.neg q.1, M.neg q.2⟩, st.2 || fl)

/-- **The computed eigenvector column** $(\hat{\mathbf{x}}; 1; \mathbf{0})$ of column `j`. -/
noncomputable def shiftedTriSolveColumn (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < j then (shiftedTriSolveWord M T smin j j).1 i
    else if (i : ℕ) = j then 1 else 0

/-- **The flag of the shifted back substitution**: whether a pivot of column `j` was floored. -/
noncomputable def shiftedTriSolveFlag (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : Bool :=
  (shiftedTriSolveWord M T smin j j).2

/-! ### The rounding of the substitution -/

section Rounding

/-- A list sum over `List.range n` is the `Finset.range` sum. -/
private theorem list_sum_map_range {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]; simp

/-- **A rounded multiply–add chain from any start**: the multiply–adds
$s \mapsto \mathrm{fl}(x_ly_l + \hat 1 s)$ of `NLAlib.linearComplex` from $s_0$ over a list of
length $k$ are within $((1 + 7\boldsymbol{u})^k - 1)(\lvert s_0\rvert + \sum_l\lvert x_l\rvert
\lvert y_l\rvert)$ of $s_0 + \sum_l x_ly_l$, for $0 \le \boldsymbol{u} \le 1/8$.
[Higham2002, Lemma 3.4] -/
theorem Ops.StdModel.norm_foldl_linearComplex_from_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) {ι : Type*} (x y : ι → ℂ)
    (ls : List ι) (s₀ : ℂ) :
    ‖ls.foldl (fun s l => linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s) s₀ -
        (s₀ + (ls.map fun l => x l * y l).sum)‖ ≤
      ((1 + 7 * u) ^ ls.length - 1) * (‖s₀‖ + (ls.map fun l => ‖x l‖ * ‖y l‖).sum) := by
  induction ls using List.reverseRecOn with
  | nil => simp
  | append_singleton ls l ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    set s := ls.foldl (fun s l => linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s) s₀
    set S := (ls.map fun l => x l * y l).sum
    set B := (ls.map fun l => ‖x l‖ * ‖y l‖).sum
    set g := (1 + 7 * u) ^ ls.length - 1
    have hB : 0 ≤ B := List.sum_nonneg fun t ht => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp ht; positivity
    have ht : ‖s₀ + S‖ ≤ ‖s₀‖ + B := (norm_add_le _ _).trans (by
      have := norm_list_sum_map_le (fun l => x l * y l) ls
      simp only [norm_mul] at this
      linarith)
    have hg : 0 ≤ g := by
      have := one_le_pow₀ (M₀ := ℝ) (a := 1 + 7 * u) (by linarith) (n := ls.length)
      simp only [g]; linarith
    have hstep := hM.norm_linearComplex_one_sub_le hu0 hu (x l) (y l) s
    have hs : ‖s‖ ≤ (1 + g) * (‖s₀‖ + B) := by
      have := norm_sub_norm_le s (s₀ + S); nlinarith
    have e : linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s - (s₀ + (S + x l * y l)) =
        (linearComplex M (x l) ⟨M.lit 1, M.lit 0⟩ (y l) s - (x l * y l + s)) +
          (s - (s₀ + S)) := by ring
    rw [e, pow_succ, show (1 + 7 * u) ^ ls.length = 1 + g by simp only [g]; ring]
    refine (norm_add_le _ _).trans ?_
    have hxy := mul_nonneg (norm_nonneg (x l)) (norm_nonneg (y l))
    have hA : 0 ≤ ‖s₀‖ + B := by positivity
    have h6 : 6 * u + 5 * u ^ 2 ≤ 7 * u := by nlinarith
    have h1 : (6 * u + 5 * u ^ 2) * ‖s‖ ≤ 7 * u * ((1 + g) * (‖s₀‖ + B)) :=
      mul_le_mul h6 hs (norm_nonneg _) (by positivity)
    have h2 : 5 * u * (‖x l‖ * ‖y l‖) ≤ (g + 7 * u * (1 + g)) * (‖x l‖ * ‖y l‖) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hxy
    have h3 : ‖s₀‖ + (B + ‖x l‖ * ‖y l‖) = (‖s₀‖ + B) + ‖x l‖ * ‖y l‖ := by ring
    rw [h3]
    nlinarith

/-- A relative error $\boldsymbol{u}$ in each rounded component of $a - b$ is a relative error
$\boldsymbol{u}$ of the complex difference. -/
theorem Ops.StdModel.norm_sub_pair_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (a b : ℂ) :
    ‖(⟨M.sub a.re b.re, M.sub a.im b.im⟩ : ℂ) - (a - b)‖ ≤ u * ‖a - b‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  have h1 := hM.sub a.re b.re
  have h2 := hM.sub a.im b.im
  simp only [id] at h1 h2
  have e1 := mul_self_le_mul_self (abs_nonneg _) h1
  have e2 := mul_self_le_mul_self (abs_nonneg _) h2
  rw [abs_mul_abs_self, mul_mul_mul_comm, abs_mul_abs_self] at e1 e2
  simp only [Complex.sub_re, Complex.sub_im]
  nlinarith [mul_self_nonneg u]

/-- Two-sided bound of a rounded nonnegative number. -/
private theorem rounded_bounds_of_nonneg {u r X : ℝ} (hX : 0 ≤ X) (h : |r - X| ≤ u * |X|) :
    (1 - u) * X ≤ r ∧ r ≤ (1 + u) * X := by
  rw [abs_of_nonneg hX] at h
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- The rounded squared modulus of a pair is within the factors $(1 \mp \boldsymbol{u})^2$ of
the squared modulus. -/
private theorem pivotWord_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (m : ℂ) :
    (1 - u) ^ 2 * ‖m‖ ^ 2 ≤ M.add (M.mul m.re m.re) (M.mul m.im m.im) ∧
      M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ (1 + u) ^ 2 * ‖m‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have ha := rounded_bounds_of_nonneg (mul_self_nonneg m.re) (hM.mul m.re m.re)
  have hb := rounded_bounds_of_nonneg (mul_self_nonneg m.im) (hM.mul m.im m.im)
  simp only [id] at ha hb
  have hab : 0 ≤ M.mul m.re m.re + M.mul m.im m.im := by
    nlinarith [mul_self_nonneg m.re, mul_self_nonneg m.im]
  have hc := rounded_bounds_of_nonneg hab (hM.add (M.mul m.re m.re) (M.mul m.im m.im))
  simp only [id] at hc
  have hre := mul_self_nonneg m.re
  have him := mul_self_nonneg m.im
  constructor <;> nlinarith

/-- A floored pivot: if the rounded squared modulus of $m$ is at most the rounded square of
$s_{\min} \ge 0$ and $m$ is within $\boldsymbol{u}\lvert d\rvert$ of $d$,
$\boldsymbol{u} \le 1/32$, then $\lvert d\rvert \le 2s_{\min}$. -/
private theorem norm_le_two_mul_of_floored {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 32) {d m : ℂ} {smin : ℝ} (hsmin : 0 ≤ smin)
    (hdm : ‖d - m‖ ≤ u * ‖d‖)
    (hle : M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ M.mul smin smin) :
    ‖d‖ ≤ 2 * smin := by
  have hpw := pivotWord_bounds hM hu0 (by linarith) m
  have hsm := rounded_bounds_of_nonneg (mul_self_nonneg smin) (hM.mul smin smin)
  simp only [id] at hsm
  have hmd : (1 - u) * ‖d‖ ≤ ‖m‖ := by
    have := norm_sub_norm_le d m; linarith
  have h1 : (1 - u) ^ 2 * ‖m‖ ^ 2 ≤ (1 + u) * (smin * smin) := by linarith [hpw.1, hsm.2]
  have h2 : ((1 - u) * ‖d‖) ^ 2 ≤ ‖m‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg d)) hmd 2
  have h3 : (1 - u) ^ 4 * ‖d‖ ^ 2 ≤ (1 + u) * (smin * smin) := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (1 - u))
    have e : (1 - u) ^ 2 * ((1 - u) * ‖d‖) ^ 2 = (1 - u) ^ 4 * ‖d‖ ^ 2 := by ring
    linarith
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).mp ?_
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -u) 4
  have hu4 : (1 + u) / 4 ≤ (1 - u) ^ 4 := by
    rw [show 1 - u = 1 + -u by ring]; push_cast at hb; linarith
  by_contra hc
  push_neg at hc
  have h4 := mul_lt_mul_of_pos_left hc (show 0 < (1 - u) ^ 4 by apply pow_pos; linarith)
  have h5 := mul_le_mul_of_nonneg_right hu4 (show 0 ≤ 4 * (smin * smin) by positivity)
  have e : (1 - u) ^ 4 * (2 * smin) ^ 2 = (1 - u) ^ 4 * (4 * (smin * smin)) := by ring
  have e2 : (1 + u) / 4 * (4 * (smin * smin)) = (1 + u) * (smin * smin) := by ring
  linarith

/-- A pivot that is not floored is not zero. -/
private theorem ne_zero_of_not_floored {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1) {m : ℂ} {smin : ℝ}
    (h : ¬ M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ M.mul smin smin) : m ≠ 0 := by
  intro h0
  apply h
  have hpw := pivotWord_bounds hM hu0 hu m
  have hsm := rounded_bounds_of_nonneg (mul_self_nonneg smin) (hM.mul smin smin)
  simp only [id] at hsm
  rw [h0, norm_zero] at hpw
  rw [h0]
  nlinarith [hpw.2, hsm.1, mul_self_nonneg smin]

/-- **The residual of one row of the substitution**: if the rounded sum $\hat s$ is within
$\gamma A$ of the exact sum $R$, $\lvert R\rvert \le A$, the quotient $q$ by the pivot
$m' \ne 0$ is within $8\boldsymbol{u}\lvert\hat s\rvert/\lvert m'\rvert$ of $\hat s/m'$, and the
pivot within $\delta$ of $d$, then $\lvert d(-q) + R\rvert \le (8\boldsymbol{u}(1 + \gamma) +
\gamma)A + \delta\lvert q\rvert$. -/
private theorem norm_row_residual_le {u γ A δ : ℝ} {d m' s R q : ℂ} (hm : m' ≠ 0)
    (hs : ‖s - R‖ ≤ γ * A) (hR : ‖R‖ ≤ A) (hq : ‖q - s / m'‖ ≤ 8 * u * (‖s‖ / ‖m'‖))
    (hd : ‖d - m'‖ ≤ δ) (hγ : 0 ≤ γ) (hu : 0 ≤ u) :
    ‖d * -q + R‖ ≤ (8 * u * (1 + γ) + γ) * A + δ * ‖-q‖ := by
  have e : d * -q + R = -(m' * (q - s / m')) + (d - m') * -q + (R - s) := by
    field_simp; ring
  rw [e]
  have hm0 : 0 < ‖m'‖ := norm_pos_iff.mpr hm
  have h1 : ‖m' * (q - s / m')‖ ≤ 8 * u * ‖s‖ := by
    rw [norm_mul]
    calc ‖m'‖ * ‖q - s / m'‖ ≤ ‖m'‖ * (8 * u * (‖s‖ / ‖m'‖)) :=
          mul_le_mul_of_nonneg_left hq hm0.le
      _ = 8 * u * ‖s‖ := by field_simp
  have h2 : ‖(d - m') * -q‖ ≤ δ * ‖-q‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  have h3 : ‖R - s‖ ≤ γ * A := by rw [norm_sub_rev]; exact hs
  have hsA : ‖s‖ ≤ (1 + γ) * A := by
    have := norm_sub_norm_le s R; nlinarith
  have hA : 0 ≤ A := (norm_nonneg _).trans hR
  have h4 : 8 * u * ‖s‖ ≤ 8 * u * ((1 + γ) * A) := mul_le_mul_of_nonneg_left hsA (by positivity)
  calc ‖-(m' * (q - s / m')) + (d - m') * -q + (R - s)‖
      ≤ ‖m' * (q - s / m')‖ + ‖(d - m') * -q‖ + ‖R - s‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg] at *
        gcongr
        exact (norm_add_le _ _).trans (by rw [norm_neg])
    _ ≤ _ := by nlinarith

end Rounding

/-! ### The rows of the substitution -/

section Rows

variable {M : Machine ℝ} {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {j : ℕ}

/-- Later rows leave an entry computed earlier unchanged. -/
private theorem shiftedTriSolveWord_stable {r r' : ℕ} (hrr : r ≤ r') (hr' : r' ≤ j) {k : ℕ}
    (hk : j - r ≤ k) :
    (shiftedTriSolveWord M T smin j r').1 k = (shiftedTriSolveWord M T smin j r).1 k := by
  induction r', hrr using Nat.le_induction with
  | base => rfl
  | succ r' hrr ih =>
    simp only [shiftedTriSolveWord]
    rw [Function.update_of_ne (by omega), ih (by omega)]

/-- A floored pivot stays flagged. -/
private theorem shiftedTriSolveWord_flag_mono {r r' : ℕ} (hrr : r ≤ r')
    (h : (shiftedTriSolveWord M T smin j r).2 = true) :
    (shiftedTriSolveWord M T smin j r').2 = true := by
  induction r', hrr using Nat.le_induction with
  | base => exact h
  | succ r' hrr ih =>
    simp only [shiftedTriSolveWord, Bool.or_eq_true]
    exact Or.inl ih

/-- $(1 + 7\boldsymbol{u})^r - 1 \le 14r\boldsymbol{u}$ for $7r\boldsymbol{u} \le 1$. -/
private theorem one_add_seven_pow_sub_one_le {u : ℝ} (hu : 0 ≤ u) {r : ℕ}
    (hr : 7 * (r : ℝ) * u ≤ 1) : (1 + 7 * u) ^ r - 1 ≤ 14 * r * u := by
  have hx : 0 ≤ (r : ℝ) * (7 * u) := by positivity
  have h1 : (1 + 7 * u) ^ r ≤ Real.exp (r * (7 * u)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (7 * u)]) r
  have h2 := Real.abs_exp_sub_one_le (x := r * (7 * u))
    (by rw [abs_of_nonneg hx]; linarith)
  rw [abs_of_nonneg hx] at h2
  linarith [(abs_le.mp h2).2]

/-- The two pivot cases of a row: either the pivot is the rounded shift $m \ne 0$, within
$\boldsymbol{u}\lvert d\rvert$ of $d$, or it is the floor $s_{\min} > 0$ with
$\lvert d\rvert \le 2s_{\min} \le \tfrac23\sigma$. -/
private theorem row_le_of_pivot {u γ A ε σ smin : ℝ} {d m m' s R q : ℂ}
    (hs : ‖s - R‖ ≤ γ * A) (hR : ‖R‖ ≤ A) (hγ : 0 ≤ γ) (hu : 0 ≤ u)
    (hcoef : 8 * u * (1 + γ) + γ ≤ ε) (hcoefu : u ≤ ε) (hσ : 0 ≤ σ)
    (hq : ‖q - s / m'‖ ≤ 8 * u * (‖s‖ / ‖m'‖)) (hdm : ‖d - m‖ ≤ u * ‖d‖)
    (hpiv : (m' = m ∧ m ≠ 0) ∨ (m' = (smin : ℂ) ∧ 0 < smin ∧ ‖d‖ ≤ 2 * smin ∧ σ = 3 * smin)) :
    ‖d * -q + R‖ ≤ ε * (‖d‖ * ‖-q‖ + A) + σ * ‖-q‖ := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hR
  have hεA : (8 * u * (1 + γ) + γ) * A ≤ ε * A := mul_le_mul_of_nonneg_right hcoef hA
  have hdq : 0 ≤ ‖d‖ * ‖-q‖ := by positivity
  have hε : 0 ≤ ε := hu.trans hcoefu
  have e : ε * (‖d‖ * ‖-q‖ + A) = ε * (‖d‖ * ‖-q‖) + ε * A := by ring
  rcases hpiv with ⟨rfl, hm0⟩ | ⟨rfl, hsmin, hd2, rfl⟩
  · have hrow := norm_row_residual_le hm0 hs hR hq hdm hγ hu
    have h3 : u * ‖d‖ * ‖-q‖ ≤ ε * (‖d‖ * ‖-q‖) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hcoefu hdq
    have := mul_nonneg hσ (norm_nonneg (-q))
    linarith
  · have hm0 : (smin : ℂ) ≠ 0 := by exact_mod_cast hsmin.ne'
    have hdm' : ‖d - (smin : ℂ)‖ ≤ 3 * smin := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsmin]; linarith
    have hrow := norm_row_residual_le hm0 hs hR hq hdm' hγ hu
    have := mul_nonneg hε hdq
    linarith

/-- **The residual of one computed row**: under the standard model with
$64(N + 1)\boldsymbol{u} \le 1$, $s_{\min} > 0$ and $i < j < N$, the computed entries $\hat x$ of
column $j$ satisfy, at row $i$ with $r = j - 1 - i$,
$\lvert(t_{ii} - t_{jj})\hat x_i + t_{ij} + \sum_{i < k < j}t_{ik}\hat x_k\rvert \le
\varepsilon(\lvert t_{ii} - t_{jj}\rvert\lvert\hat x_i\rvert + \lvert t_{ij}\rvert +
\sum_{i < k < j}\lvert t_{ik}\rvert\lvert\hat x_k\rvert) + \sigma\lvert\hat x_i\rvert$, with
$\sigma = 3s_{\min}$ if a pivot was floored and $0$ otherwise, for any
$\varepsilon \ge (14N + 10)\boldsymbol{u}$. -/
private theorem shiftedTriSolveWord_row_le {u ε : ℝ} (hM : StdModel u id M)
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) (hε : (14 * (N : ℝ) + 10) * u ≤ ε) (hsmin : 0 < smin)
    {i : ℕ} (hij : i < j) (hj : j < N) :
    ‖(entryAt T i i - entryAt T j j) * (shiftedTriSolveWord M T smin j j).1 i +
        (entryAt T i j + ∑ l ∈ Finset.range (j - 1 - i),
          entryAt T i (i + 1 + l) * (shiftedTriSolveWord M T smin j j).1 (i + 1 + l))‖ ≤
      ε *
          (‖entryAt T i i - entryAt T j j‖ * ‖(shiftedTriSolveWord M T smin j j).1 i‖ +
            (‖entryAt T i j‖ + ∑ l ∈ Finset.range (j - 1 - i),
              ‖entryAt T i (i + 1 + l)‖ * ‖(shiftedTriSolveWord M T smin j j).1 (i + 1 + l)‖)) +
        (if (shiftedTriSolveWord M T smin j j).2 then 3 * smin else 0) *
          ‖(shiftedTriSolveWord M T smin j j).1 i‖ := by
  have hu0 : 0 ≤ u := by
    have := hM.lit 1
    simp only [Rat.cast_one, abs_one, mul_one, id] at this
    exact (abs_nonneg _).trans this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set r := j - 1 - i with hr
  have hi : j - 1 - r = i := by omega
  have hjr : j - r = i + 1 := by omega
  set w := (shiftedTriSolveWord M T smin j j).1
  set st := shiftedTriSolveWord M T smin j r
  have hwi : w i = (shiftedTriSolveWord M T smin j (r + 1)).1 i :=
    shiftedTriSolveWord_stable (by omega) le_rfl (by omega)
  have hwk : ∀ l ∈ Finset.range r, w (i + 1 + l) = st.1 (i + 1 + l) := fun l _ =>
    shiftedTriSolveWord_stable (by omega) le_rfl (by omega)
  set d := entryAt T i i - entryAt T j j
  set m : ℂ := ⟨M.sub (entryAt T i i).re (entryAt T j j).re,
    M.sub (entryAt T i i).im (entryAt T j j).im⟩
  set fl0 := decide (M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ M.mul smin smin)
  set m' : ℂ := if fl0 then ⟨smin, M.lit 0⟩ else m
  set s := (List.range r).foldl (fun s l =>
      linearComplex M (entryAt T i (i + 1 + l)) ⟨M.lit 1, M.lit 0⟩ (st.1 (i + 1 + l)) s)
    (entryAt T i j)
  set q := Pair.divideWords M (s.re, s.im) (m'.re, m'.im)
  have hstep : (shiftedTriSolveWord M T smin j (r + 1)) =
      (Function.update st.1 i ⟨M.neg q.1, M.neg q.2⟩, st.2 || fl0) := by
    simp only [shiftedTriSolveWord, hi, hjr, st, q, s, m', fl0, m]
  have hxi : w i = -(⟨q.1, q.2⟩ : ℂ) := by
    rw [hwi, hstep]
    dsimp only
    rw [Function.update_self]
    apply Complex.ext
    · exact hM.neg q.1
    · exact hM.neg q.2
  have hflag : fl0 = true → (shiftedTriSolveWord M T smin j j).2 = true := fun h =>
    shiftedTriSolveWord_flag_mono (r := r + 1) (by omega) (by rw [hstep, h, Bool.or_true])
  -- the chain
  set R := entryAt T i j + ∑ l ∈ Finset.range r, entryAt T i (i + 1 + l) * w (i + 1 + l)
  set A := ‖entryAt T i j‖ + ∑ l ∈ Finset.range r, ‖entryAt T i (i + 1 + l)‖ * ‖w (i + 1 + l)‖
  set γ := (1 + 7 * u) ^ r - 1
  have hu8 : u ≤ 1 / 8 := by nlinarith
  have hchain : ‖s - R‖ ≤ γ * A := by
    have h := hM.norm_foldl_linearComplex_from_sub_le hu0 hu8
      (fun l => entryAt T i (i + 1 + l)) (fun l => st.1 (i + 1 + l)) (List.range r)
      (entryAt T i j)
    rw [list_sum_map_range, list_sum_map_range, List.length_range] at h
    have e1 : R = entryAt T i j + ∑ l ∈ Finset.range r, entryAt T i (i + 1 + l) * st.1 (i + 1 + l) := by
      simp only [R]; congr 1; exact Finset.sum_congr rfl fun l hl => by rw [hwk l hl]
    have e2 : A = ‖entryAt T i j‖ +
        ∑ l ∈ Finset.range r, ‖entryAt T i (i + 1 + l)‖ * ‖st.1 (i + 1 + l)‖ := by
      simp only [A]; congr 1; exact Finset.sum_congr rfl fun l hl => by rw [hwk l hl]
    rw [e1, e2]
    exact h
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => by positivity)
  have hsum : ‖∑ l ∈ Finset.range r, entryAt T i (i + 1 + l) * w (i + 1 + l)‖ ≤
      ∑ l ∈ Finset.range r, ‖entryAt T i (i + 1 + l)‖ * ‖w (i + 1 + l)‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
  have hRA : ‖R‖ ≤ A := (norm_add_le _ _).trans (by simp only [A]; linarith)
  have hγ0 : 0 ≤ γ := by
    have := one_le_pow₀ (M₀ := ℝ) (a := 1 + 7 * u) (by linarith) (n := r); simp only [γ]; linarith
  have hrN : (r : ℝ) ≤ N := by exact_mod_cast (show r ≤ N by omega)
  have hγ : γ ≤ 14 * N * u := (one_add_seven_pow_sub_one_le hu0 (by nlinarith)).trans
    (by nlinarith)
  have hcoef : 8 * u * (1 + γ) + γ ≤ ε := by nlinarith
  have hcoefu : u ≤ ε := by nlinarith
  have hdm : ‖d - m‖ ≤ u * ‖d‖ := by
    rw [norm_sub_rev]; exact hM.norm_sub_pair_sub_le hu0 _ _
  have hσ : 0 ≤ (if (shiftedTriSolveWord M T smin j j).2 then 3 * smin else 0) := by
    split_ifs <;> linarith
  rw [hxi]
  have hu32 : u ≤ 1 / 32 := by nlinarith
  cases hfl : fl0 with
  | false =>
    have hmm : m' = m := by simp only [m', hfl]; rfl
    have hm0 : m ≠ 0 := ne_zero_of_not_floored hM hu0 (by linarith) (smin := smin) (by
      intro h; have h' : fl0 = true := decide_eq_true h; rw [hfl] at h'; exact absurd h' (by decide))
    have hq := NLAlib.Ops.StdModel.norm_complexDivide_sub_le hM hu32 (x := s) (hmm ▸ hm0)
    exact row_le_of_pivot (smin := smin) hchain hRA hγ0 hu0 hcoef hcoefu hσ hq hdm
      (Or.inl ⟨hmm, hm0⟩)
  | true =>
    have hmm : m' = (smin : ℂ) := by
      have h0 : M.lit 0 = 0 := hM.zero
      simp only [m', hfl, if_true]; apply Complex.ext <;> simp [h0]
    have hm0 : m' ≠ 0 := by rw [hmm]; exact_mod_cast hsmin.ne'
    have hq := NLAlib.Ops.StdModel.norm_complexDivide_sub_le hM hu32 (x := s) hm0
    have hle : M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ M.mul smin smin :=
      of_decide_eq_true hfl
    have hd2 : ‖d‖ ≤ 2 * smin :=
      norm_le_two_mul_of_floored hM hu0 (by nlinarith) hsmin.le hdm hle
    have hσ3 : (if (shiftedTriSolveWord M T smin j j).2 then 3 * smin else 0) = 3 * smin :=
      if_pos (hflag hfl)
    exact row_le_of_pivot hchain hRA hγ0 hu0 hcoef hcoefu hσ hq hdm
      (Or.inr ⟨hmm, hsmin, hd2, hσ3⟩)

end Rows

/-! ### The column -/

section Column

/-- A sum over the first $N$ indices, split at $i < j < N$. -/
private theorem sum_range_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) {i j N : ℕ}
    (hij : i < j) (hjN : j < N) :
    ∑ k ∈ Finset.range N, f k = ∑ k ∈ Finset.range i, f k + (f i +
      (∑ l ∈ Finset.range (j - 1 - i), f (i + 1 + l) + (f j +
        ∑ l ∈ Finset.range (N - 1 - j), f (j + 1 + l)))) := by
  have hN : N = i + (1 + ((j - 1 - i) + (1 + (N - 1 - j)))) := by omega
  conv_lhs => rw [hN]
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one, Finset.sum_range_add,
    Finset.sum_range_add, Finset.sum_range_one]
  have hj : i + (1 + (j - 1 - i + 0)) = j := by omega
  rw [add_zero, hj]
  congr 2
  congr 1
  · exact Finset.sum_congr rfl fun l _ => by rw [← add_assoc]
  · congr 2
    funext l
    congr 1
    omega

variable {M : Machine ℝ} {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ}

/-- Below the diagonal the entries of an upper triangular matrix vanish. -/
private theorem entryAt_of_lt (hT : T.IsUpperTriangular) {i k : ℕ} (hki : k < i) :
    entryAt T i k = 0 := by
  unfold entryAt
  split_ifs with h
  · exact hT (show (⟨k, h.2⟩ : Fin N) < ⟨i, h.1⟩ from hki)
  · rfl

end Column

/-! ### The theorems -/

/-- **The computed column is a componentwise backward solution, with any relative
perturbation** $\varepsilon \ge (14N + 10)\boldsymbol{u}$: under the standard model at
$\boldsymbol{u}$ with $64(N + 1)\boldsymbol{u} \le 1$, for an upper triangular $\mathbf{T}$ of
order $N$, $s_{\min} > 0$ and $j < N$, the column $(\hat{\mathbf{x}}; 1; \mathbf{0})$ is a
componentwise backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with
$\varepsilon$ and the diagonal floor $3s_{\min}$ if a pivot was floored, $0$ otherwise (the
per-row residual of the chain, the shift and the division, then
`NLAlib.isComponentwiseBackwardSolution_of_norm_sub_le`). [Higham2002, Theorem 8.5] -/
theorem shiftedTriSolve_isComponentwiseBackwardSolution_of_le {M : Machine ℝ} {u ε : ℝ}
    (hM : StdModel u id M) {N : ℕ} (hu : 64 * ((N : ℝ) + 1) * u ≤ 1)
    (hε : (14 * (N : ℝ) + 10) * u ≤ ε)
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 < smin)
    (j : Fin N) :
    IsComponentwiseBackwardSolution ε
      (if shiftedTriSolveFlag M T smin j then 3 * smin else 0) (T - T j j • 1) 0
      (shiftedTriSolveColumn M T smin j) := by
  have hu0 : 0 ≤ u := by
    have := hM.lit 1
    simp only [Rat.cast_one, abs_one, mul_one, id] at this
    exact (abs_nonneg _).trans this
  set σ := if shiftedTriSolveFlag M T smin j then 3 * smin else 0 with hσdef
  have hσ : 0 ≤ σ := by simp only [σ]; split_ifs <;> linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine isComponentwiseBackwardSolution_of_norm_sub_le (by nlinarith) hσ fun i => ?_
  rw [sub_zero]
  set w := (shiftedTriSolveWord M T smin j j).1
  set yN : ℕ → ℂ := fun k => if k < j then w k else if k = j then 1 else 0
  set cN : ℕ → ℂ := fun k => entryAt T i k - if (i : ℕ) = k then T j j else 0
  have hc : ∀ k : Fin N, (T - T j j • 1) i k = cN k := by
    intro k
    simp only [cN, entryAt, i.isLt, k.isLt, and_self, dif_pos, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Fin.ext_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hmv : ((T - T j j • 1) *ᵥ shiftedTriSolveColumn M T smin j) i =
      ∑ k ∈ Finset.range N, cN k * yN k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => cN k * yN k)]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => by rw [hc]; rfl
  have hab : ∑ k, ‖(T - T j j • 1) i k‖ * ‖shiftedTriSolveColumn M T smin j k‖ =
      ∑ k ∈ Finset.range N, ‖cN k‖ * ‖yN k‖ := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ‖cN k‖ * ‖yN k‖)]
    exact Finset.sum_congr rfl fun k _ => by rw [hc]; rfl
  have hyi : shiftedTriSolveColumn M T smin j i = yN i := rfl
  rw [hmv, hab, hyi]
  have hnn : 0 ≤ ∑ k ∈ Finset.range N, ‖cN k‖ * ‖yN k‖ :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hjj : entryAt T j j = T j j := by simp [entryAt, j.isLt]
  by_cases hij : (i : ℕ) < j
  · have hlo : ∀ k ∈ Finset.range i, cN k = 0 := fun k hk => by
      have hk' := Finset.mem_range.mp hk
      simp only [cN, entryAt_of_lt hT hk', if_neg (show (i : ℕ) ≠ k by omega), sub_zero]
    have hhi : ∀ l ∈ Finset.range (N - 1 - j), yN (j + 1 + l) = 0 := fun l _ => by
      simp only [yN, if_neg (show ¬ j + 1 + l < j by omega),
        if_neg (show j + 1 + l ≠ (j : ℕ) by omega)]
    have hmid : ∀ l ∈ Finset.range (j - 1 - i),
        cN (i + 1 + l) = entryAt T i (i + 1 + l) ∧ yN (i + 1 + l) = w (i + 1 + l) := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      simp only [cN, yN, if_neg (show (i : ℕ) ≠ i + 1 + l by omega), sub_zero,
        if_pos (show i + 1 + l < j by omega), and_self]
    have hci : cN i = entryAt T i i - entryAt T j j := by simp [cN, hjj]
    have hyi' : yN i = w i := by simp [yN, hij]
    have hcj : cN j = entryAt T i j := by
      simp [cN, show (i : ℕ) ≠ j by omega]
    have hyj : yN j = 1 := by simp [yN]
    have h1 : ∑ k ∈ Finset.range i, cN k * yN k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hlo k hk, zero_mul]
    have h2 : ∑ k ∈ Finset.range i, ‖cN k‖ * ‖yN k‖ = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hlo k hk, norm_zero, zero_mul]
    have h3 : ∑ l ∈ Finset.range (N - 1 - j), cN (j + 1 + l) * yN (j + 1 + l) = 0 :=
      Finset.sum_eq_zero fun l hl => by rw [hhi l hl, mul_zero]
    have h4 : ∑ l ∈ Finset.range (N - 1 - j), ‖cN (j + 1 + l)‖ * ‖yN (j + 1 + l)‖ = 0 :=
      Finset.sum_eq_zero fun l hl => by rw [hhi l hl, norm_zero, mul_zero]
    have h5 : ∑ l ∈ Finset.range (j - 1 - i), cN (i + 1 + l) * yN (i + 1 + l) =
        ∑ l ∈ Finset.range (j - 1 - i), entryAt T i (i + 1 + l) * w (i + 1 + l) :=
      Finset.sum_congr rfl fun l hl => by rw [(hmid l hl).1, (hmid l hl).2]
    have h6 : ∑ l ∈ Finset.range (j - 1 - i), ‖cN (i + 1 + l)‖ * ‖yN (i + 1 + l)‖ =
        ∑ l ∈ Finset.range (j - 1 - i), ‖entryAt T i (i + 1 + l)‖ * ‖w (i + 1 + l)‖ :=
      Finset.sum_congr rfl fun l hl => by rw [(hmid l hl).1, (hmid l hl).2]
    rw [sum_range_split _ hij j.isLt, sum_range_split _ hij j.isLt, h1, h2, h3, h4, h5, h6,
      hci, hyi', hcj, hyj]
    have hrow := shiftedTriSolveWord_row_le (T := T) hM hu hε hsmin hij j.isLt
    have e1 : (0 : ℂ) + ((entryAt T i i - entryAt T j j) * w i +
        (∑ l ∈ Finset.range (j - 1 - i), entryAt T i (i + 1 + l) * w (i + 1 + l) +
          (entryAt T i j * 1 + 0))) = (entryAt T i i - entryAt T j j) * w i +
        (entryAt T i j + ∑ l ∈ Finset.range (j - 1 - i), entryAt T i (i + 1 + l) * w (i + 1 + l))
      := by ring
    have e2 : (0 : ℝ) + (‖entryAt T i i - entryAt T j j‖ * ‖w i‖ +
        (∑ l ∈ Finset.range (j - 1 - i), ‖entryAt T i (i + 1 + l)‖ * ‖w (i + 1 + l)‖ +
          (‖entryAt T i j‖ * ‖(1 : ℂ)‖ + 0))) = ‖entryAt T i i - entryAt T j j‖ * ‖w i‖ +
        (‖entryAt T i j‖ + ∑ l ∈ Finset.range (j - 1 - i),
          ‖entryAt T i (i + 1 + l)‖ * ‖w (i + 1 + l)‖) := by rw [norm_one]; ring
    rw [e1, e2]
    exact hrow
  · have hzero : ∀ k ∈ Finset.range N, cN k * yN k = 0 := fun k _ => by
      by_cases hkj : k ≤ j
      · by_cases hki : k < i
        · simp only [cN, entryAt_of_lt hT hki, if_neg (show (i : ℕ) ≠ k by omega), sub_zero,
            zero_mul]
        · have hk : k = j := by omega
          have hik : (i : ℕ) = j := by omega
          subst hk
          have : i = j := Fin.ext hik
          subst this
          simp [cN, hjj]
      · simp only [yN, if_neg (show ¬ k < j by omega), if_neg (show k ≠ (j : ℕ) by omega),
          mul_zero]
    rw [Finset.sum_eq_zero hzero, norm_zero]
    positivity

/-- **The computed column is a componentwise backward solution**: under the standard model at
$\boldsymbol{u}$ with $64(N + 1)\boldsymbol{u} \le 1$, for an upper triangular $\mathbf{T}$ of
order $N$, $s_{\min} > 0$ and $j < N$, the column $(\hat{\mathbf{x}}; 1; \mathbf{0})$ is a
componentwise backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with
the relative perturbation $16(N + 1)\boldsymbol{u}$ and the diagonal floor $3s_{\min}$ if a pivot
was floored, $0$ otherwise. [Higham2002, Theorem 8.5] -/
theorem shiftedTriSolve_isComponentwiseBackwardSolution {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) {N : ℕ} (hu : 64 * ((N : ℝ) + 1) * u ≤ 1)
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 < smin)
    (j : Fin N) :
    IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
      (if shiftedTriSolveFlag M T smin j then 3 * smin else 0) (T - T j j • 1) 0
      (shiftedTriSolveColumn M T smin j) := by
  have hu0 : 0 ≤ u := by
    have := hM.lit 1
    simp only [Rat.cast_one, abs_one, mul_one, id] at this
    exact (abs_nonneg _).trans this
  exact shiftedTriSolve_isComponentwiseBackwardSolution_of_le hM hu (by nlinarith) hT hsmin j

/-- **No pivot is floored when the diagonal is separated**: under the standard model at
$\boldsymbol{u} \le 1/32$, if $\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for every $i < j$,
$s_{\min} \ge 0$, the flag of column $j$ is not set. -/
theorem shiftedTriSolve_flag {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : u ≤ 1 / 32)
    {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} (hsmin : 0 ≤ smin) (j : Fin N)
    (hgap : ∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) :
    shiftedTriSolveFlag M T smin j = false := by
  have hu0 : 0 ≤ u := by
    have := hM.lit 1
    simp only [Rat.cast_one, abs_one, mul_one, id] at this
    exact (abs_nonneg _).trans this
  suffices h : ∀ r ≤ (j : ℕ), (shiftedTriSolveWord M T smin j r).2 = false from h j le_rfl
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [shiftedTriSolveWord, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨ih (by omega), fun hle => ?_⟩
    have hi : j - 1 - r < N := by omega
    have hd := norm_le_two_mul_of_floored hM hu0 hu hsmin
      (d := entryAt T (j - 1 - r) (j - 1 - r) - entryAt T j j)
      (by rw [norm_sub_rev]; exact hM.norm_sub_pair_sub_le hu0 _ _) hle
    have hg := hgap ⟨j - 1 - r, hi⟩ (show (⟨j - 1 - r, hi⟩ : Fin N) < j from
      Fin.lt_def.mpr (by simp only; omega))
    simp only [entryAt, hi, j.isLt, and_self, dif_pos] at hd
    linarith

section Writes

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The program stores the computed words**: on a scalar machine with index literals and exact
comparisons, from a memory holding $\mathbf{T}$ of order $N$ at `t`, the floor $s_{\min}$ at `sm`,
room for `Y` and a flag word at `g`, the four blocks live and apart, and $j < N$, the run writes
only the first $j$ entries of column $j$ of `Y` and the flag: they hold the words of
`NLAlib.shiftedTriSolveWord`, and the flag is the literal $1$ if a pivot was floored and unchanged
otherwise. -/
theorem shiftedTriSolve_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j : ℕ} (hj : j < N) {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (shiftedTriSolve (O := O) (Q := Q)).body
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => (∀ i < j, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) =
            some ((shiftedTriSolveWord M T smin j j).1 i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) =
            some ((shiftedTriSolveWord M T smin j j).1 i).im) ∧
        (shiftedTriSolveFlag M T smin j = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (shiftedTriSolveFlag M T smin j = false →
          μ'.store.get g.1 g.2 = μ.store.get g.1 g.2)) μ := by
  sorry

/-- **Rounded shifted back substitution under the standard model**: on a scalar machine with the
standard model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact
comparisons, from the memory of `NLAlib.shiftedTriSolve_writes_word` with $\mathbf{T}$ upper
triangular, $s_{\min} \ge 0$ and $j < N$, the run stores the first $j$ entries of a column
$\mathbf{y}$ with $y_j = 1$, $y_i = 0$ for $i > j$, that is a componentwise backward solution of
$(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with $16(N + 1)\boldsymbol{u}$ and the
floor $3s_{\min}$ if the flag was set, $0$ if the flag is unchanged; the flag is unchanged when
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i < j$. -/
theorem shiftedTriSolve_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 < smin) (j : Fin N) {τ : Tape ℝ}
    {μ : Mem ℝ} (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (shiftedTriSolve (O := O) (Q := Q)).body
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (yv : Fin N → ℂ) (fl : Bool),
        (∀ i : Fin N, (i : ℕ) < j → μ'.store.get y.1 (y.2 + 2 * (j * N + i)) = some (yv i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) = some (yv i).im) ∧
        yv j = 1 ∧ (∀ i : Fin N, j < i → yv i = 0) ∧
        IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u) (if fl then 3 * smin else 0)
          (T - T j j • 1) 0 yv ∧
        (fl = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (fl = false → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) ∧
        ((∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) → fl = false)) μ := by
  have hu32 : u ≤ 1 / 32 := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hu0 : 0 ≤ u := by
      have := hM.lit 1
      simp only [Rat.cast_one, abs_one, mul_one, id] at this
      exact (abs_nonneg _).trans this
    nlinarith
  refine (shiftedTriSolve_writes_word hS hL hC j.isLt hT hsm hl hroom hap).mono le_rfl
    fun μ' _ ⟨hy, h1, h0⟩ => ⟨shiftedTriSolveColumn M T smin j, shiftedTriSolveFlag M T smin j,
      fun i hi => by simpa only [shiftedTriSolveColumn, hi, if_true] using hy i hi,
      by simp [shiftedTriSolveColumn],
      fun i hi => by simp [shiftedTriSolveColumn, not_lt.mpr hi.le, (Fin.val_ne_of_ne hi.ne')],
      shiftedTriSolve_isComponentwiseBackwardSolution hM hu hTu hsmin j, h1, h0,
      fun hgap => shiftedTriSolve_flag hM hu32 hsmin.le j hgap⟩

end Writes

end NLAlib
