/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.NormEstimate
public import NLAlib.Matrix.FinitePrecision.StoredProducts
public import NLAlib.Ops.Blas.MatrixCorrect
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Compare

/-!
# A posteriori check of a Schur form

`NLAlib.Schur.schurResidualCheck` takes a stored $\mathbf{A}_0$, $\widehat{\mathbf{U}}$,
$\widehat{\mathbf{T}}$ and two words $\theta, \kappa$.

## Main definitions

* `NLAlib.Schur.zeroStrictLower`, `NLAlib.Schur.schurResidualCheck`.

## Main results

* `NLAlib.Schur.zeroStrictLower_writes`.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops
open scoped Matrix

variable {O Q : Type}

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **Zero the strict lower triangle** of a stored square matrix: the literal $0$ in both words
of every entry $(i, j)$ with $i > j$. The interface is `[N] (T) → (T)`. -/
def zeroStrictLower : Impl O Q := opsImpl% [N] (T) → (T) {
  for j < N {
    for i < N - (j + 1) {
      call (Has.inj (ScalarOp.lit 0)) [] () → (T[2 * (j * N + (j + 1 + i))]);
      call (Has.inj (ScalarOp.lit 0)) [] () → (T[2 * (j * N + (j + 1 + i)) + 1])
    }
  }
}

/-- **The stored residual** $\mathbf{D} = \mathrm{fl}(\mathbf{A}_0 -
\mathrm{fl}(\mathrm{fl}(\mathbf{U}\mathbf{T})\mathbf{U}^{\mathsf H}))$ of square matrices of
order $N$: two products (`NLAlib.matMulOn`), the conjugate transpose of $\mathbf{U}$ into scratch,
and an entrywise rounded subtraction. The interface is `[N] (A0, U, T) → (D)`. -/
def residualWords : Impl O Q := opsImpl% [N] (A0, U, T) → (D) {
  let W ← alloc (2 * (N * N));
  let V ← alloc (2 * (N * N));
  run (matMulOn (O := O) (Q := Q)).body [N, N, N, N, N, N, 0] (U, T, W);
  run (PairMatrix.conjTranspose (Op := O) (Tst := Q)).body [N, N] (U, V);
  run (matMulOn (O := O) (Q := Q)).body [N, N, N, N, N, N, 0] (W, V, D);
  for t < 2 * (N * N) { call (Has.inj ScalarOp.sub) [] (A0[t], D[t]) → (D[t]) }
}

/-- **The residual check of a Schur form**: zero the strict lower triangle of $\mathbf{T}$, form
the stored residual $\mathbf{D}$ of $\mathbf{A}_0 - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}$
(`NLAlib.Schur.residualWords`), the rounded Frobenius norms $\hat r$ of $\mathbf{D}$, $\hat a$
of $\mathbf{A}_0$, $\hat w$ of $\mathbf{U}$ and $\hat t$ of $\mathbf{T}$, the guard
$\hat g = \mathrm{fl}(\mathrm{fl}(\hat w^2)\hat t\kappa)$ for the rounding of the products, and
write the flag $0$ if $\mathrm{fl}(\hat r + \hat g) \le \mathrm{fl}(\theta\hat a)$ and $1$
otherwise. The words are `P[0]` $= \theta$ and `P[1]` $= \kappa$. The interface is
`[N] (A0, U, T, P) → (T, Fl)`. -/
def schurResidualCheck : Impl O Q := opsImpl% [N] (A0, U, T, P) → (T, Fl) {
  let D ← alloc (2 * (N * N));
  let S ← alloc 4;
  run (zeroStrictLower (O := O) (Q := Q)).body [N] (T, T);
  run (residualWords (O := O) (Q := Q)).body [N] (A0, U, T, D);
  run (frobNormStage (O := O) (Q := Q)).body [N] (D, S);
  run (frobNormStage (O := O) (Q := Q)).body [N] (A0, S[1]);
  run (frobNormStage (O := O) (Q := Q)).body [N] (U, S[2]);
  run (frobNormStage (O := O) (Q := Q)).body [N] (T, S[3]);
  call (Has.inj ScalarOp.mul) [] (S[2], S[2]) → (S[2]);
  call (Has.inj ScalarOp.mul) [] (S[2], S[3]) → (S[2]);
  call (Has.inj ScalarOp.mul) [] (S[2], P[1]) → (S[2]);
  call (Has.inj ScalarOp.add) [] (S, S[2]) → (S);
  call (Has.inj ScalarOp.mul) [] (S[1], P) → (S[1]);
  if (Has.inj CmpTst.le) [] (S, S[1]) {
    call (Has.inj IndexOp.lit) [0] () → (Fl)
  } else {
    call (Has.inj IndexOp.lit) [1] () → (Fl)
  }
}

end Program

section Steps

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The upper triangle of a square matrix, the strict lower triangle replaced by zeros. -/
def upperPart {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if j < i then 0 else T i j

theorem upperPart_isUpperTriangular {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) :
    (upperPart T).IsUpperTriangular := fun i j hij => by
  simp [upperPart, show j < i from hij]

theorem upperPart_apply_of_le {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) {i j : Fin N}
    (h : i ≤ j) : upperPart T i j = T i j := by
  simp [upperPart, not_lt.mpr h]

theorem upperPart_eq_self {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} (h : T.IsUpperTriangular) :
    upperPart T = T := by
  ext i j
  by_cases hij : j < i
  · simp [upperPart, hij, h hij]
  · simp [upperPart, hij]

omit [Has IndexOp O] [Has CmpTst Q] in
/-- **Zeroing the strict lower triangle**, on every tape, when the literal $0$ is exact: the run
writes only the block and stores the upper part of $\mathbf{T}$. -/
theorem zeroStrictLower_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (h0 : M.lit 0 = 0) {τ : Tape ℝ} {μ : Mem ℝ} {N : ℕ} {t : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : HoldsMatrix t T μ.store) :
    Writes .total I τ (zeroStrictLower (O := O) (Q := Q)).body (Env.frame [N] [t, t])
      (Store.inBlock t.1 t.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix t (upperPart T) μ'.store) μ := by
  let C := EntryCodec.pair ℝ
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 * N + (p.2 + 1 + p.1))
      {p | p.2 < N ∧ p.1 < N - (p.2 + 1)} := by
    rintro ⟨i, j⟩ ⟨hj, hi⟩ ⟨i', j'⟩ ⟨hj', hi'⟩ he
    simp only at he hi hi' hj hj'
    have hd := congrArg (· / N) he
    have hm := congrArg (· % N) he
    simp only [Idx.div_add (show j + 1 + i < N by omega),
      Idx.div_add (show j' + 1 + i' < N by omega)] at hd
    simp only [Idx.mod_add (show j + 1 + i < N by omega),
      Idx.mod_add (show j' + 1 + i' < N by omega)] at hm
    exact Prod.ext (by omega) hd
  unfold zeroStrictLower
  refine Writes.mono (writes_fillEntryRegion (md := .total) (I := I) (τ := τ) (m := μ)
    (ρ := Env.frame [N] [t, t]) C t.1 t.2 N (fun i j => j * N + (j + 1 + i))
    (fun j => N - (j + 1)) hinj rfl (fun j => rfl) (fun _ _ => (M.lit 0, M.lit 0))
    (fun _ _ => μ.pos) rfl (fun _ _ => rfl) ?_) ?_ ?_
  · intro j hj i hi m' hfr hpos
    have hk : j + 1 + i < N := by omega
    have hr := Store.lt_len_of_get (hT.get_im ⟨j + 1 + i, hk⟩ ⟨j, hj⟩)
    simp only at hr
    have hz0 : t.2 + 2 * (j * N + (j + 1 + i)) < m'.store.len t.1 := by
      rw [hfr.len_eq]; omega
    have hz1 : t.2 + 2 * (j * N + (j + 1 + i)) + 1 < m'.store.len t.1 := by
      rw [hfr.len_eq]; omega
    refine (writes_call_const (hS (.lit 0)) (z := (t.1, t.2 + 2 * (j * N + (j + 1 + i)))) rfl
      trivial hz0).seq_le (fun b x hx => ?_) fun m₁ hfr₁ h₁ => ?_
    · obtain ⟨h1, h2, h3⟩ := hx
      exact ⟨h1, by change _ ≤ _ at h2 ⊢; simp only at h2 ⊢; change t.2 + 2 * _ ≤ x; omega,
        by change x < t.2 + 2 * _ + 2; simp only at h3; omega⟩
    refine (writes_call_const (hS (.lit 0))
      (z := (t.1, t.2 + 2 * (j * N + (j + 1 + i)) + 1)) rfl trivial
      (by rw [hfr₁.len_eq]; exact hz1)).mono (fun b x hx => ?_) fun m₂ hfr₂ h₂ => ?_
    · obtain ⟨h1, h2, h3⟩ := hx
      exact ⟨h1, by change t.2 + 2 * _ ≤ x; simp only at h2; omega,
        by change x < t.2 + 2 * _ + 2; simp only at h3; omega⟩
    refine ⟨fun z => ?_, h₂.1.trans (h₁.1.trans hpos)⟩
    change m₂.store.get t.1 (t.2 + 2 * (j * N + (j + 1 + i)) + z) =
      some (C.words (M.lit 0, M.lit 0) z)
    fin_cases z
    · simp only [Fin.zero_eta, Fin.isValue, add_zero]
      rw [hfr₂.get_eq (Store.not_inBlock_of (Or.inr (Or.inl (by simp))))]
      exact h₁.2
    · exact h₂.2
  · exact C.regionFp_le_inBlock t.1 t.2 N (N * N) _ _ fun j hj i hi =>
      Idx.add_lt_mul hj (show j + 1 + i < N by omega)
  · rintro μ' hfr ⟨hreg, hpos⟩
    have hlow : ∀ (i j : Fin N), j < i → ∀ z : Fin 2,
        μ'.store.get t.1 (t.2 + 2 * (j * N + i) + z) = some 0 := by
      intro i j hji z
      have h := hreg j j.isLt (i - (j + 1)) (by simp only; omega) z
      simp only at h
      rw [show (j : ℕ) + 1 + (i - (j + 1)) = i by omega] at h
      rw [h]
      fin_cases z <;> simp [C, EntryCodec.pair, h0]
    have hup : ∀ (i j : Fin N), ¬ j < i → ∀ z : ℕ, z < 2 →
        μ'.store.get t.1 (t.2 + 2 * (j * N + i) + z) =
          μ.store.get t.1 (t.2 + 2 * (j * N + i) + z) := by
      intro i j hji z hz
      refine hfr.get_eq ?_
      rintro ⟨r, c, ⟨hc, hr⟩ | ⟨-, hr⟩, -, h2, h3⟩
      · change t.2 + 2 * (c * N + (c + 1 + r)) ≤ _ at h2
        change _ < t.2 + 2 * (c * N + (c + 1 + r)) + 2 at h3
        simp only at hr
        have he : c * N + (c + 1 + r) = j * N + i := by omega
        have hd := congrArg (· / N) he
        have hm := congrArg (· % N) he
        simp only [Idx.div_add (show c + 1 + r < N by omega), Idx.div_add i.isLt] at hd
        simp only [Idx.mod_add (show c + 1 + r < N by omega), Idx.mod_add i.isLt] at hm
        omega
      · omega
    refine ⟨hpos, HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
    · by_cases hji : j < i
      · simpa [upperPart, hji] using hlow i j hji 0
      · simpa [upperPart, hji, hT.get_re i j] using hup i j hji 0 (by omega)
    · by_cases hji : j < i
      · simpa [upperPart, hji] using hlow i j hji 1
      · simpa [upperPart, hji, hT.get_im i j] using hup i j hji 1 (by omega)

omit [Has IndexOp O] [Has CmpTst Q] in
/-- **The stored conjugate transpose**: `NLAlib.Ops.PairMatrix.conjTranspose` of a stored square
$\mathbf{U}$ into a block apart from it stores $\mathbf{U}^{\mathsf H}$ under the standard model
(negation is exact), on every tape. -/
theorem conjTranspose_writes_holdsMatrix {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ} {N : ℕ}
    {x y : ℕ × ℕ} {U : Matrix (Fin N) (Fin N) ℂ} (hU : HoldsMatrix x U μ.store)
    (hl : μ.Live [x, y]) (hy : y.2 + 2 * (N * N) ≤ μ.store.len y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock y.1 y.2 (2 * (N * N)))) :
    Writes .total I τ (PairMatrix.conjTranspose (Op := O) (Tst := Q)).body
      (Env.frame [N, N] [x, y]) (Store.inBlock y.1 y.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix y Uᴴ μ'.store) μ := by
  let E : ℕ → ℕ → ℝ × ℝ := fun i j =>
    if hi : i < N then if hj : j < N then ((U ⟨i, hi⟩ ⟨j, hj⟩).re, (U ⟨i, hi⟩ ⟨j, hj⟩).im)
      else (0, 0) else (0, 0)
  have hE : μ.store.HoldsEntries (EntryCodec.pair ℝ) ⟨x.1, x.2, N, N, N⟩ E := by
    intro i hi j hj z
    fin_cases z
    · simpa [E, hi, hj] using hU.get_re ⟨i, hi⟩ ⟨j, hj⟩
    · simpa [E, hi, hj, Nat.add_assoc] using hU.get_im ⟨i, hi⟩ ⟨j, hj⟩
  refine (PairMatrix.writes_conjTranspose hS E hl hE hy hxy).mono le_rfl ?_
  rintro μ' - ⟨hout, hpos⟩
  refine ⟨hpos, HoldsMatrix.of_get (fun i j => ?_) (fun i j => ?_)⟩
  · simpa [E, Matrix.conjTranspose_apply] using hout i i.isLt j j.isLt 0
  · have h := hout i i.isLt j j.isLt 1
    simp only [E, j.isLt, i.isLt, dite_true] at h
    rw [show (M.neg (U j i).im) = -(U j i).im by simpa using hM.neg (U j i).im] at h
    simpa [Matrix.conjTranspose_apply, Nat.add_assoc] using h

omit [Has IndexOp O] [Has CmpTst Q] in
/-- **An in-place subtraction loop**: the loop of $N$ rounds whose round $t$ replaces the cell
$o + t$ of the buffer $b$ by the machine difference of the cell $o' + t$ of $b'$ (a block apart)
and its old word; it writes only the block and keeps the tape position. -/
theorem writes_loop_sub_cells {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    {τ : Tape ℝ} {ρ : Env} {m : Mem ℝ} {n : IExp} {N b o b' o' : ℕ} {X Y : Operand}
    (hn : n.eval ρ.idx = some N)
    (hXY : ∀ t < N, Operand.evalList (ρ.pushIdx t) [Y, X] = some [(b', o' + t), (b, o + t)])
    (hX : ∀ t < N, Operand.evalList (ρ.pushIdx t) [X] = some [(b, o + t)])
    (hl : m.Live [(b, o), (b', o')]) (hv : ∀ t < N, ∃ w, m.store.get b (o + t) = some w)
    (hv' : ∀ t < N, ∃ w, m.store.get b' (o' + t) = some w)
    (hd : Fp.Disj (Store.inBlock b o N) (Store.inBlock b' o' N)) :
    Writes .total I τ (.loop n (.call (Has.inj ScalarOp.sub) [] [Y, X] [X])) ρ
      (Store.inBlock b o N)
      (fun m' => m'.pos = m.pos ∧ ∀ t < N, ∀ v w, m.store.get b' (o' + t) = some v →
        m.store.get b (o + t) = some w → m'.store.get b (o + t) = some (M.sub v w)) m := by
  refine (writes_loop hn (fun i => Store.inBlock b o i)
    (fun i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun i m' => m'.pos = m.pos ∧ ∀ t < i, ∀ v w, m.store.get b' (o' + t) = some v →
      m.store.get b (o + t) = some w → m'.store.get b (o + t) = some (M.sub v w))
    ⟨rfl, fun t ht => absurd ht (by omega)⟩
    fun i hi m' hfr ⟨hpos, hdone⟩ => ?_).mono le_rfl fun _ _ h => h
  have hlen := hfr.len_eq b
  obtain ⟨w, hw⟩ := hv i hi
  obtain ⟨v, hv₀⟩ := hv' i hi
  have hroom : o + i < m.store.len b := Store.lt_len_of_get hw
  have hw' : m'.store.get b (o + i) = some w := by
    rw [hfr.2 b (o + i) (by simp [Store.inBlock]), hw]
  have hv₁ : m'.store.get b' (o' + i) = some v := by
    rw [hfr.2 b' (o' + i) fun h => hd b' (o' + i)
      (Fp.inBlock_le_inBlock le_rfl (by omega) _ _ h) ⟨rfl, by omega, by omega⟩, hv₀]
  have hl' : m'.Live [(b', o' + i), (b, o + i), (b, o + i)] := by
    have h0 := hl.congr hfr.length_eq
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h0 (b', o') (by simp)
    · exact h0 (b, o) (by simp)
    · exact h0 (b, o) (by simp)
  refine (writes_call_bin (hS .sub) (hXY i hi) (hX i hi) trivial hv₁ hw' rfl
    fun _ => ⟨hl', show o + i < m'.store.len b by rw [hlen]; exact hroom⟩).mono
    (show Store.inBlock b (o + i) 1 ≤ Store.inBlock b o (i + 1) from
      Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m'' hfr' ⟨hp, hg⟩
  refine ⟨hp.trans hpos, fun t ht v' w' hv' hw'' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
  · rw [hfr'.2 b (o + t) (by simp [Store.inBlock]; omega)]
    exact hdone t ht v' w' hv' hw''
  · rw [hg]
    rw [hv₀] at hv'
    rw [hw] at hw''
    cases hv'; cases hw''; rfl

/-- **The entrywise machine difference** of two complex matrices: the machine subtraction of the
real and of the imaginary words, as the subtraction loop of `NLAlib.Schur.residualWords` stores
it. -/
def subWord (M : Machine ℝ) {m q : ℕ} (A B : Matrix (Fin m) (Fin q) ℂ) :
    Matrix (Fin m) (Fin q) ℂ :=
  Matrix.of fun i j => ⟨M.sub (A i j).re (B i j).re, M.sub (A i j).im (B i j).im⟩

/-- **The error of an entrywise rounded difference**: under the standard model at
$\boldsymbol{u} \ge 0$, $\|\mathrm{fl}(\mathbf{A} - \mathbf{B}) - (\mathbf{A} - \mathbf{B})\|_{\mathsf F}
\le \boldsymbol{u}\|\mathbf{A} - \mathbf{B}\|_{\mathsf F}$. -/
theorem _root_.NLAlib.Ops.StdModel.frobNorm_subWord_sub_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) {m q : ℕ} (A B : Matrix (Fin m) (Fin q) ℂ) :
    frobNorm (subWord M A B - (A - B)) ≤ u * frobNorm (A - B) := by
  have hu : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  rw [show u * frobNorm (A - B) = ‖((u : ℝ) : ℂ)‖ * frobNorm (A - B) by
    rw [Complex.norm_real, Real.norm_of_nonneg hu], ← frobNorm_smul]
  refine frobNorm_le_of_norm_apply_le fun i j => ?_
  have h1 := hM.sub (A i j).re (B i j).re
  have h2 := hM.sub (A i j).im (B i j).im
  simp only [id] at h1 h2
  set z := A i j - B i j with hz
  have hre : (subWord M A B - (A - B)) i j =
      ⟨M.sub (A i j).re (B i j).re - z.re, M.sub (A i j).im (B i j).im - z.im⟩ := by
    apply Complex.ext <;> simp [subWord, z]
  have hz' : (((u : ℝ) : ℂ) • (A - B)) i j = ((u : ℝ) : ℂ) * z := rfl
  rw [hre, hz', norm_mul, Complex.norm_real, Real.norm_of_nonneg hu]
  have hzr : z.re = (A i j).re - (B i j).re := by simp [z]
  have hzi : z.im = (A i j).im - (B i j).im := by simp [z]
  rw [← hzr] at h1
  rw [← hzi] at h2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only
  have e1 := sq_abs (M.sub (A i j).re (B i j).re - z.re)
  have e2 := sq_abs (M.sub (A i j).im (B i j).im - z.im)
  have f1 := sq_abs z.re
  have f2 := sq_abs z.im
  have g1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have g2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [mul_pow] at g1 g2
  nlinarith

omit [Has IndexOp O] [Has CmpTst Q] in
/-- **The stored residual**, on every tape: from stored square $\mathbf{A}_0$, $\mathbf{U}$,
$\mathbf{T}$ and an output block apart from them, `NLAlib.Schur.residualWords` writes only the
output and stores the entrywise machine difference of $\mathbf{A}_0$ and the stored product
$\mathrm{fl}(\mathrm{fl}(\mathbf{U}\mathbf{T})\mathbf{U}^{\mathsf H})$ (standard model:
negation exact). -/
theorem residualWords_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) {τ : Tape ℝ} {μ : Mem ℝ} {N : ℕ} {a0 uo t d : ℕ × ℕ}
    {A₀ U T : Matrix (Fin N) (Fin N) ℂ} (hA : HoldsMatrix a0 A₀ μ.store)
    (hU : HoldsMatrix uo U μ.store) (hT : HoldsMatrix t T μ.store)
    (hl : μ.Live [a0, uo, t, d]) (hd : d.2 + 2 * (N * N) ≤ μ.store.len d.1)
    (hda : Fp.Disj (Store.inBlock d.1 d.2 (2 * (N * N))) (Store.inBlock a0.1 a0.2 (2 * (N * N))))
    (hdu : Fp.Disj (Store.inBlock uo.1 uo.2 (2 * (N * N))) (Store.inBlock d.1 d.2 (2 * (N * N))))
    (hdt : Fp.Disj (Store.inBlock t.1 t.2 (2 * (N * N))) (Store.inBlock d.1 d.2 (2 * (N * N)))) :
    Writes .total I τ (residualWords (O := O) (Q := Q)).body (Env.frame [N] [a0, uo, t, d])
      (Store.inBlock d.1 d.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix d (subWord M A₀ (matMulWord M (matMulWord M U T) Uᴴ)) μ'.store) μ := by
  have hlt : ∀ z ∈ [a0, uo, t, d], z.1 < μ.store.length := hl
  have ha0 := hlt a0 (by simp)
  have huo := hlt uo (by simp)
  have ht := hlt t (by simp)
  have hd1 := hlt d (by simp)
  unfold residualWords
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0),
    .const 2 * (.var 0 * .var 0)] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * (N * N), 2 * (N * N)]) rfl
    (fun hBelow ⟨hp, hW⟩ => ⟨hp, hW.of_below hBelow hd1⟩) ?_
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hW : s₁.len L = 2 * (N * N) := by simpa using hlens 0 (by simp)
  have hV : s₁.len (L + 1) = 2 * (N * N) := by simpa using hlens 1 (by simp)
  have hA₁ := hA.of_below hBelow ha0
  have hU₁ := hU.of_below hBelow huo
  have hT₁ := hT.of_below hBelow ht
  have hd₁ : d.2 + 2 * (N * N) ≤ s₁.len d.1 := by
    rw [(hBelow d.1 hd1).1]; exact hd
  have hall : ∀ (s : Store ℝ), s.length = s₁.length → ∀ zs : List (ℕ × ℕ),
      zs ⊆ [a0, uo, t, d, (L, 0), (L + 1, 0)] → ∀ p : ℕ, (⟨s, p⟩ : Mem ℝ).Live zs := by
    intro s hs zs hzs p z hz
    have := hzs hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    change z.1 < s.length
    rw [hs, hlen]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  have hab : ∀ b o n, L ≤ b →
      Store.inBlock b o n ≤ Store.inBlock d.1 d.2 (2 * (N * N)) ⊔ Fp.above L :=
    fun b o n hb _ _ hi => Or.inr (hi.1 ▸ hb)
  have hdL : ∀ (b o n : ℕ), L ≤ b → Fp.Disj (Store.inBlock b o n)
      (Store.inBlock d.1 d.2 (2 * (N * N))) := fun b o n hb => Fp.disj_inBlock_of_ne (by omega)
  -- the product `W = fl(U T)`
  refine (matMulOn_writes_word (M := M) hS (μ := ⟨s₁, μ.pos⟩) (x := uo) (y := t) (z := (L, 0))
    hU₁ hT₁ (hall _ rfl _ (by simp) _) (by simp [hW]) (Fp.disj_inBlock_of_ne (by omega))
    (Fp.disj_inBlock_of_ne (by omega))).frame_seq_le rfl rfl (hall _ rfl _ (by simp) _)
    (hab _ _ _ le_rfl) fun m₁ hfr₁ ⟨hp₁, hW₁⟩ => ?_
  have hU₂ := hU₁.of_eqOff hfr₁ (Fp.disj_inBlock_of_ne (by simp; omega))
  -- the conjugate transpose `V = Uᴴ`
  refine (conjTranspose_writes_holdsMatrix (M := M) hS hM (y := (L + 1, 0)) hU₂
    (hall _ hfr₁.length_eq _ (by simp) _) (by rw [hfr₁.len_eq]; simp [hV])
    (Fp.disj_inBlock_of_ne (by simp; omega))).frame_seq_le rfl rfl
    (hall _ hfr₁.length_eq _ (by simp) _) (hab _ _ _ (by omega)) fun m₂ hfr₂ ⟨hp₂, hV₂⟩ => ?_
  have hW₂ := hW₁.of_eqOff hfr₂ (Fp.disj_inBlock_of_ne (by simp))
  have h12 := hfr₂.length_eq.trans hfr₁.length_eq
  -- the product `fl(W V)` into `D`
  refine (matMulOn_writes_word (M := M) hS (μ := m₂) (x := (L, 0)) (y := (L + 1, 0)) (z := d)
    hW₂ hV₂ (hall _ h12 _ (by simp) _) (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hd₁)
    (hdL _ _ _ le_rfl) (hdL _ _ _ (by omega))).frame_seq_le rfl rfl
    (hall _ h12 _ (by simp) _) (fun _ _ h => Or.inl h) fun m₃ hfr₃ ⟨hp₃, hD₃⟩ => ?_
  have hA₃ : HoldsMatrix a0 A₀ m₃.store :=
    ((hA₁.of_eqOff hfr₁ (Fp.disj_inBlock_of_ne (by simp; omega))).of_eqOff hfr₂
      (Fp.disj_inBlock_of_ne (by simp; omega))).of_eqOff hfr₃ hda
  have h123 := hfr₃.length_eq.trans h12
  -- the subtraction loop
  refine (writes_loop_sub_cells hS (N := 2 * (N * N)) (b := d.1) (o := d.2) (b' := a0.1)
    (o' := a0.2) rfl (fun _ _ => rfl) (fun _ _ => rfl) (hall _ h123 _ (by simp) _)
    (fun t ht => ⟨_, Store.get_of_readBlock hD₃ ht 0⟩)
    (fun t ht => ⟨_, Store.get_of_readBlock hA₃ ht 0⟩) hda).mono (fun _ _ h => Or.inl h) ?_
  rintro m₄ - ⟨hp₄, hsub⟩
  refine ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), HoldsMatrix.of_get (fun i j => ?_)
    (fun i j => ?_)⟩
  · have hlt := Idx.add_lt_mul (Idx.add_lt_mul j.isLt i.isLt) (show 0 < 2 by omega)
    exact hsub _ (by omega) _ _ (hA₃.get_re i j) (hD₃.get_re i j)
  · have hlt := Idx.add_lt_mul (Idx.add_lt_mul j.isLt i.isLt) (show 1 < 2 by omega)
    have h := hsub (2 * (j * N + i) + 1) (by omega) _ _
      (by rw [← Nat.add_assoc]; exact hA₃.get_im i j)
      (by rw [← Nat.add_assoc]; exact hD₃.get_im i j)
    rw [← Nat.add_assoc] at h
    exact h

end Steps

end NLAlib.Schur
