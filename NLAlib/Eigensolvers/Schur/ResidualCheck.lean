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
public import NLAlib.Ops.Logic.IndexLiteral

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

/-- **The four norms of the check**: the rounded Frobenius norms (`NLAlib.Schur.frobNormStage`)
of $\mathbf{D}$, $\mathbf{A}_0$, $\mathbf{U}$ and $\mathbf{T}$ into `S[0]`, …, `S[3]`. The
interface is `[N] (A0, U, T, D) → (S)`. -/
def checkNorms : Impl O Q := opsImpl% [N] (A0, U, T, D) → (S) {
  run (frobNormStage (O := O) (Q := Q)).body [N] (D, S);
  run (frobNormStage (O := O) (Q := Q)).body [N] (A0, S[1]);
  run (frobNormStage (O := O) (Q := Q)).body [N] (U, S[2]);
  run (frobNormStage (O := O) (Q := Q)).body [N] (T, S[3])
}

/-- **The decision of the check**: from the norms $\hat r, \hat a, \hat w, \hat t$ in `S` and the
words $\theta, \kappa$ in `P`, the guard $\hat g = \mathrm{fl}(\mathrm{fl}(\mathrm{fl}(\hat w\hat
w)\hat t)\kappa)$ into `S[2]`, $\mathrm{fl}(\hat r + \hat g)$ into `S[0]`,
$\mathrm{fl}(\hat a\theta)$ into `S[1]`, and the flag: the literal $0$ if `S[0] ≤ S[1]` (an exact
comparison), the literal $1$ otherwise. The interface is `[] (S, P) → (S, Fl)`. -/
def checkDecide : Impl O Q := opsImpl% [] (S, P) → (S, Fl) {
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

/-- **The residual check of a Schur form**: zero the strict lower triangle of $\mathbf{T}$
(`NLAlib.Schur.zeroStrictLower`), form the stored residual $\mathbf{D}$ of
$\mathbf{A}_0 - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}$ (`NLAlib.Schur.residualWords`), the
rounded Frobenius norms $\hat r$ of $\mathbf{D}$, $\hat a$ of $\mathbf{A}_0$, $\hat w$ of
$\mathbf{U}$ and $\hat t$ of $\mathbf{T}$ (`NLAlib.Schur.checkNorms`), and write the flag $0$ if
$\mathrm{fl}(\hat r + \hat g) \le \mathrm{fl}(\theta\hat a)$ for the guard $\hat g =
\mathrm{fl}(\mathrm{fl}(\hat w^2)\hat t\kappa)$ of the rounding of the products, and $1$ otherwise
(`NLAlib.Schur.checkDecide`). The words are `P[0]` $= \theta$ and `P[1]` $= \kappa$. The
interface is `[N] (A0, U, T, P) → (T, Fl)`. -/
def schurResidualCheck : Impl O Q := opsImpl% [N] (A0, U, T, P) → (T, Fl) {
  let D ← alloc (2 * (N * N));
  let S ← alloc 4;
  run (zeroStrictLower (O := O) (Q := Q)).body [N] (T, T);
  run (residualWords (O := O) (Q := Q)).body [N] (A0, U, T, D);
  run (checkNorms (O := O) (Q := Q)).body [N] (A0, U, T, D, S);
  run (checkDecide (O := O) (Q := Q)).body [] (S, P, S, Fl)
}

end Program

/-- The guard of the check: $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(w w)t)\kappa)$. -/
noncomputable def checkGuard (M : Machine ℝ) (w t κ : ℝ) : ℝ :=
  M.mul (M.mul (M.mul w w) t) κ

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

omit [Has IndexOp O] [Has CmpTst Q] in
/-- **The four norms of the check**, on every tape, with any two-sided norm estimate for the
order $N$ in place of `NLAlib.Schur.frobNormStage`'s contract: the run writes only the four
words of `S` and stores there estimates of $\|\mathbf{D}\|_{\mathsf F}$,
$\|\mathbf{A}_0\|_{\mathsf F}$, $\|\mathbf{U}\|_{\mathsf F}$ and $\|\mathbf{T}\|_{\mathsf F}$
within the factors $c_1$, $c_2$. -/
theorem checkNorms_writes {I : Interp O Q ℝ} {c₁ c₂ : ℝ} {N : ℕ}
    (hNm : FrobNormEstimateContract c₁ c₂ N (frobNormStage (O := O) (Q := Q)) I) {τ : Tape ℝ}
    {μ : Mem ℝ} {a0 uo t d s : ℕ × ℕ} {A₀ U T D : Matrix (Fin N) (Fin N) ℂ}
    (hA : HoldsMatrix a0 A₀ μ.store) (hU : HoldsMatrix uo U μ.store)
    (hT : HoldsMatrix t T μ.store) (hD : HoldsMatrix d D μ.store)
    (hl : μ.Live [a0, uo, t, d, s]) (hs : s.2 + 4 ≤ μ.store.len s.1) (ha : a0.1 ≠ s.1)
    (hu : uo.1 ≠ s.1) (ht : t.1 ≠ s.1) (hd : d.1 ≠ s.1) :
    Writes .total I τ (checkNorms (O := O) (Q := Q)).body (Env.frame [N] [a0, uo, t, d, s])
      (Store.inBlock s.1 s.2 4)
      (fun μ' => ∃ r a w x : ℝ, μ'.store.get s.1 s.2 = some r ∧
        μ'.store.get s.1 (s.2 + 1) = some a ∧ μ'.store.get s.1 (s.2 + 2) = some w ∧
        μ'.store.get s.1 (s.2 + 3) = some x ∧
        c₁ * frobNorm D ≤ r ∧ r ≤ c₂ * frobNorm D ∧ c₁ * frobNorm A₀ ≤ a ∧
        a ≤ c₂ * frobNorm A₀ ∧ c₁ * frobNorm U ≤ w ∧ w ≤ c₂ * frobNorm U ∧
        c₁ * frobNorm T ≤ x ∧ x ≤ c₂ * frobNorm T) μ := by
  have hlv : ∀ (m : Mem ℝ), m.store.length = μ.store.length → ∀ zs : List (ℕ × ℕ),
      (∀ z ∈ zs, z.1 = a0.1 ∨ z.1 = uo.1 ∨ z.1 = t.1 ∨ z.1 = d.1 ∨ z.1 = s.1) → m.Live zs := by
    intro m hm zs hzs z hz
    rw [hm]
    rcases hzs z hz with h | h | h | h | h <;> rw [h]
    exacts [hl a0 (by simp), hl uo (by simp), hl t (by simp), hl d (by simp), hl s (by simp)]
  have hk : ∀ k, k < 4 → Store.inBlock s.1 (s.2 + k) 1 ≤ Store.inBlock s.1 s.2 4 :=
    fun k hk => Fp.inBlock_le_inBlock (by omega) (by omega)
  have hkeep : ∀ {b : ℕ × ℕ} {X : Matrix (Fin N) (Fin N) ℂ} {m m' : Mem ℝ} {k : ℕ},
      b.1 ≠ s.1 → HoldsMatrix b X m.store →
      m.store.EqOff (Store.inBlock s.1 (s.2 + k) 1) m'.store → HoldsMatrix b X m'.store :=
    fun hb hX hfr => hX.of_eqOff hfr (Fp.disj_inBlock_of_ne (Ne.symm hb))
  have hget : ∀ {m m' : Mem ℝ} {k j : ℕ}, k ≠ j →
      m.store.EqOff (Store.inBlock s.1 (s.2 + k) 1) m'.store →
      m'.store.get s.1 (s.2 + j) = m.store.get s.1 (s.2 + j) :=
    fun hkj hfr => hfr.get_eq fun h => hkj (by obtain ⟨-, h1, h2⟩ := h; omega)
  refine (hNm D le_rfl hD (hlv μ rfl _ (by simp)) (by simpa using (by omega : s.2 + 1 ≤
    μ.store.len s.1)) hd).frame_seq_le rfl rfl (hlv μ rfl _ (by simp))
    (hk 0 (by omega) |> fun h => by simpa using h) fun m₁ hfr₁ ⟨r, hr, hr1, hr2⟩ => ?_
  have hl₁ := fun zs h => hlv m₁ hfr₁.length_eq zs h
  refine (hNm (s := (s.1, s.2 + 1)) A₀ le_rfl (hkeep (k := 0) ha hA (by simpa using hfr₁))
    (hl₁ _ (by simp)) (by simp only; rw [hfr₁.len_eq]; omega) ha).frame_seq_le rfl rfl
    (hl₁ _ (by simp)) (hk 1 (by omega))
    fun m₂ hfr₂ ⟨a, ha', ha1, ha2⟩ => ?_
  have hl₂ := fun zs h => hlv m₂ (hfr₂.length_eq.trans hfr₁.length_eq) zs h
  have hU₂ := hkeep hu (hkeep (k := 0) hu hU (by simpa using hfr₁)) hfr₂
  refine (hNm (s := (s.1, s.2 + 2)) U le_rfl hU₂ (hl₂ _ (by simp))
    (by simp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega)
    hu).frame_seq_le rfl rfl (hl₂ _ (by simp)) (hk 2 (by omega))
    fun m₃ hfr₃ ⟨w, hw, hw1, hw2⟩ => ?_
  have hl₃ := fun zs h => hlv m₃
    (hfr₃.length_eq.trans (hfr₂.length_eq.trans hfr₁.length_eq)) zs h
  have hT₃ := hkeep ht (hkeep ht (hkeep (k := 0) ht hT (by simpa using hfr₁)) hfr₂) hfr₃
  refine (hNm (s := (s.1, s.2 + 3)) T le_rfl hT₃ (hl₃ _ (by simp))
    (by simp only; rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; omega) ht).in_frame rfl rfl
    (hl₃ _ (by simp)) |>.mono (hk 3 (by omega)) fun m₄ hfr₄ ⟨x, hx, hx1, hx2⟩ => ?_
  refine ⟨r, a, w, x, ?_, ?_, ?_, hx, hr1, hr2, ha1, ha2, hw1, hw2, hx1, hx2⟩
  · have h := (hget (k := 3) (j := 0) (by omega) hfr₄).trans
      ((hget (k := 2) (j := 0) (by omega) hfr₃).trans (hget (k := 1) (j := 0) (by omega) hfr₂))
    simp only [add_zero] at h
    rw [h, hr]
  · rw [hget (k := 3) (j := 1) (by omega) hfr₄, hget (k := 2) (j := 1) (by omega) hfr₃]
    exact ha'
  · rw [hget (k := 3) (j := 2) (by omega) hfr₄]
    exact hw

omit [Has IndexOp O] in
/-- **The decision of the check**, on every tape: from the norms $\hat r, \hat a, \hat w, \hat t$
in the four cells of `S` and the words $\theta, \kappa$ in `P` (another buffer), the run writes
only `S` and the flag (another buffer), and stores the literal $0$ in the flag if
$\mathrm{fl}(\hat r + \hat g) \le \mathrm{fl}(\hat a\theta)$, the literal $1$ otherwise. -/
theorem checkDecide_writes [Has IndexOp O] {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ}
    {s p f : ℕ × ℕ} {r a w x θ κ : ℝ} (hr : μ.store.get s.1 s.2 = some r)
    (ha : μ.store.get s.1 (s.2 + 1) = some a) (hw : μ.store.get s.1 (s.2 + 2) = some w)
    (hx : μ.store.get s.1 (s.2 + 3) = some x) (hθ : μ.store.get p.1 p.2 = some θ)
    (hκ : μ.store.get p.1 (p.2 + 1) = some κ) (hs : s.2 + 4 ≤ μ.store.len s.1)
    (hf : f.2 < μ.store.len f.1) (hsp : s.1 ≠ p.1) (hsf : s.1 ≠ f.1)
    (hl : μ.Live [s, p, f]) :
    Writes .total I τ (checkDecide (O := O) (Q := Q)).body (Env.frame [] [s, p, s, f])
      (Store.inBlock s.1 s.2 4 ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 =
        some (if M.add r (checkGuard M w x κ) ≤ M.mul a θ then M.lit 0 else M.lit 1)) μ := by
  have hlv : ∀ (m : Mem ℝ), m.store.length = μ.store.length → ∀ zs : List (ℕ × ℕ),
      (∀ z ∈ zs, z.1 = s.1 ∨ z.1 = p.1 ∨ z.1 = f.1) → m.Live zs := by
    intro m hm zs hzs z hz
    rw [hm]
    rcases hzs z hz with h | h | h <;> rw [h]
    exacts [hl s (by simp), hl p (by simp), hl f (by simp)]
  have hk : ∀ k, k < 4 → Store.inBlock s.1 (s.2 + k) 1 ≤
      Store.inBlock s.1 s.2 4 ⊔ Store.inBlock f.1 f.2 1 :=
    fun k hk _ _ h => Or.inl (Fp.inBlock_le_inBlock (by omega) (by omega) _ _ h)
  -- cells other than the one written are kept
  have hget : ∀ {m m' : Mem ℝ} {b o : ℕ}, m.store.EqOff (Store.inBlock s.1 (s.2 + 2) 1) m'.store →
      (b ≠ s.1 ∨ o ≠ s.2 + 2) → m'.store.get b o = m.store.get b o :=
    fun hfr h => hfr.get_eq fun hi => by obtain ⟨h1, h2, h3⟩ := hi; omega
  unfold checkDecide
  -- the guard
  refine (writes_call_bin (hS .mul) (x := (s.1, s.2 + 2)) (y := (s.1, s.2 + 2))
    (z := (s.1, s.2 + 2)) rfl rfl trivial hw hw rfl fun _ =>
      ⟨hlv μ rfl _ (by simp), by simp only; omega⟩).seq_le (hk 2 (by omega))
    fun m₁ hfr₁ ⟨_, h₁⟩ => ?_
  have hl₁ := hlv m₁ hfr₁.length_eq
  refine (writes_call_bin (hS .mul) (x := (s.1, s.2 + 2)) (y := (s.1, s.2 + 3))
    (z := (s.1, s.2 + 2)) (v := x) rfl rfl trivial h₁ (by rw [hget hfr₁ (by omega), hx]) rfl
    fun _ =>
      ⟨hl₁ _ (by simp), by simp only; rw [hfr₁.len_eq]; omega⟩).seq_le (hk 2 (by omega))
    fun m₂ hfr₂ ⟨_, h₂⟩ => ?_
  have hl₂ := hlv m₂ (hfr₂.length_eq.trans hfr₁.length_eq)
  have hget₂ : ∀ {b o : ℕ}, (b ≠ s.1 ∨ o ≠ s.2 + 2) → m₂.store.get b o = μ.store.get b o :=
    fun h => (hget hfr₂ h).trans (hget hfr₁ h)
  refine (writes_call_bin (hS .mul) (x := (s.1, s.2 + 2)) (y := (p.1, p.2 + 1))
    (z := (s.1, s.2 + 2)) (v := κ) rfl rfl trivial h₂ (by rw [hget₂ (by omega), hκ]) rfl fun _ =>
      ⟨hl₂ _ (by simp), by simp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega⟩).seq_le
    (hk 2 (by omega)) fun m₃ hfr₃ ⟨_, h₃⟩ => ?_
  have hl₃ := hlv m₃ (hfr₃.length_eq.trans (hfr₂.length_eq.trans hfr₁.length_eq))
  have hget₃ : ∀ {b o : ℕ}, (b ≠ s.1 ∨ o ≠ s.2 + 2) → m₃.store.get b o = μ.store.get b o :=
    fun h => (hget hfr₃ h).trans (hget₂ h)
  have hlen₃ : ∀ b, m₃.store.len b = μ.store.len b := fun b => by
    rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
  -- the sum and the threshold
  refine (writes_call_bin (hS .add) (x := (s.1, s.2)) (y := (s.1, s.2 + 2))
    (z := (s.1, s.2)) (u := r) rfl rfl trivial (by rw [hget₃ (by omega)]; exact hr) h₃ rfl fun _ =>
      ⟨hl₃ _ (by simp), by simp only; rw [hlen₃]; omega⟩).seq_le
    (by simpa using hk 0 (by omega)) fun m₄ hfr₄ ⟨_, h₄⟩ => ?_
  have hl₄ := hlv m₄ (hfr₄.length_eq.trans (hfr₃.length_eq.trans (hfr₂.length_eq.trans
    hfr₁.length_eq)))
  have hget₄ : ∀ {b o : ℕ}, (b ≠ s.1 ∨ (o ≠ s.2 + 2 ∧ o ≠ s.2)) →
      m₄.store.get b o = μ.store.get b o := fun h => by
    rw [hfr₄.get_eq fun hi => by obtain ⟨h1, h2, h3⟩ := hi; omega]
    exact hget₃ (by omega)
  refine (writes_call_bin (hS .mul) (x := (s.1, s.2 + 1)) (y := (p.1, p.2))
    (z := (s.1, s.2 + 1)) (u := a) (v := θ) rfl rfl trivial (by rw [hget₄ (by omega)]; exact ha)
    (by rw [hget₄ (by omega)]; exact hθ) rfl fun _ =>
      ⟨hl₄ _ (by simp), by simp only; rw [hfr₄.len_eq, hlen₃]; omega⟩).seq_le
    (hk 1 (by omega)) fun m₅ hfr₅ ⟨_, h₅⟩ => ?_
  have h₄' : m₅.store.get s.1 s.2 = some (M.add r (checkGuard M w x κ)) := by
    rw [hfr₅.get_eq fun hi => by obtain ⟨-, h2, -⟩ := hi; simp only at h2; omega]
    exact h₄
  have hl₅ := hlv m₅ (hfr₅.length_eq.trans (hfr₄.length_eq.trans (hfr₃.length_eq.trans
    (hfr₂.length_eq.trans hfr₁.length_eq))))
  have hlen₅ : f.2 < m₅.store.len f.1 := by rw [hfr₅.len_eq, hfr₄.len_eq, hlen₃]; exact hf
  refine writes_ite rfl rfl (hC.test_le (x := (s.1, s.2)) (y := (s.1, s.2 + 1)) h₄' h₅) ?_
  by_cases hc : M.add r (checkGuard M w x κ) ≤ M.mul a θ
  · simp only [id, hc, decide_true, if_true]
    refine (writes_indexLit hL (n := 0) rfl rfl hlen₅).mono (fun _ _ h => Or.inr h)
      fun m' _ h => ?_
    simpa using h.2
  · simp only [id, hc, decide_false, Bool.false_eq_true, if_false]
    refine (writes_indexLit hL (n := 1) rfl rfl hlen₅).mono (fun _ _ h => Or.inr h)
      fun m' _ h => ?_
    simpa using h.2

/-- **The entrywise machine difference** of two complex matrices: the machine subtraction of the
real and of the imaginary words, as the subtraction loop of `NLAlib.Schur.residualWords` stores
it. -/
def subWord (M : Machine ℝ) {m q : ℕ} (A B : Matrix (Fin m) (Fin q) ℂ) :
    Matrix (Fin m) (Fin q) ℂ :=
  Matrix.of fun i j => ⟨M.sub (A i j).re (B i j).re, M.sub (A i j).im (B i j).im⟩

/-- **The error of an entrywise rounded difference**: under the standard model at
$\boldsymbol{u} \ge 0$,
$\|\mathrm{fl}(\mathbf{A} - \mathbf{B}) - (\mathbf{A} - \mathbf{B})\|_{\mathsf F}
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

/-- **The outcome of the residual check** of $(\mathbf{A}_0, \mathbf{U}, \mathbf{T})$ at the words
$\theta, \kappa$, with norm estimates within the factors $c_1, c_2$: the block `t` holds the upper
part $\mathbf{T}'$ of $\mathbf{T}$, and there are estimates $\hat r, \hat a, \hat w, \hat t$ of the
Frobenius norms of the stored residual of $(\mathbf{A}_0, \mathbf{U}, \mathbf{T}')$, of
$\mathbf{A}_0$, $\mathbf{U}$ and $\mathbf{T}'$ with the flag the literal $0$ if
$\mathrm{fl}(\hat r + \hat g) \le \mathrm{fl}(\hat a\theta)$ and the literal $1$ otherwise. -/
def ResidualCheckOutcome (M : Machine ℝ) (c₁ c₂ θ κ : ℝ) {N : ℕ}
    (A₀ U T : Matrix (Fin N) (Fin N) ℂ) (t f : ℕ × ℕ) (μ' : Mem ℝ) : Prop :=
  HoldsMatrix t (upperPart T) μ'.store ∧ ∃ r a w x : ℝ,
    c₁ * frobNorm (subWord M A₀ (matMulWord M (matMulWord M U (upperPart T)) Uᴴ)) ≤ r ∧
    r ≤ c₂ * frobNorm (subWord M A₀ (matMulWord M (matMulWord M U (upperPart T)) Uᴴ)) ∧
    c₁ * frobNorm A₀ ≤ a ∧ a ≤ c₂ * frobNorm A₀ ∧ c₁ * frobNorm U ≤ w ∧ w ≤ c₂ * frobNorm U ∧
    c₁ * frobNorm (upperPart T) ≤ x ∧ x ≤ c₂ * frobNorm (upperPart T) ∧
    μ'.store.get f.1 f.2 =
      some (if M.add r (checkGuard M w x κ) ≤ M.mul a θ then M.lit 0 else M.lit 1)

section Check

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The residual check on every tape**: on a scalar machine with the standard model, index
literals and exact comparisons, with a two-sided norm estimate for the order $N$ (the contract of
`NLAlib.Schur.frobNormStage` with the factors $c_1, c_2$), from stored $\mathbf{A}_0$,
$\mathbf{U}$, $\mathbf{T}$, the words $\theta, \kappa$ and room for the flag, pairwise apart,
`NLAlib.Schur.schurResidualCheck` writes only $\mathbf{T}$ and the flag and ends in
`NLAlib.Schur.ResidualCheckOutcome`. No hypothesis on the matrices. -/
theorem schurResidualCheck_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I)
    {c₁ c₂ : ℝ} {N : ℕ} (hNm : FrobNormEstimateContract c₁ c₂ N (frobNormStage (O := O) (Q := Q)) I)
    {τ : Tape ℝ} {μ : Mem ℝ} {a0 uo t p f : ℕ × ℕ} {A₀ U T : Matrix (Fin N) (Fin N) ℂ}
    {θ κ : ℝ} (hA : HoldsMatrix a0 A₀ μ.store) (hU : HoldsMatrix uo U μ.store)
    (hT : HoldsMatrix t T μ.store) (hp : μ.store.readBlock p.1 p.2 2 = some [θ, κ])
    (hl : μ.Live [a0, uo, t, p, f]) (hf : f.2 < μ.store.len f.1)
    (hap : Fp.Apart [a0, uo, t, p, f] [2 * (N * N), 2 * (N * N), 2 * (N * N), 2, 1]) :
    Writes .total I τ (schurResidualCheck (O := O) (Q := Q)).body
      (Env.frame [N] [a0, uo, t, p, t, f])
      (Store.inBlock t.1 t.2 (2 * (N * N)) ⊔ Store.inBlock f.1 f.2 1)
      (ResidualCheckOutcome M c₁ c₂ θ κ A₀ U T t f) μ := by
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
    and_true] at hap
  obtain ⟨⟨hau, hat, hapw, haf⟩, ⟨hut, hup, huf⟩, ⟨htp, htf⟩, hpf⟩ := hap
  have hlt : ∀ z ∈ [a0, uo, t, p, f], z.1 < μ.store.length := hl
  have ha0 := hlt a0 (by simp)
  have huo := hlt uo (by simp)
  have ht := hlt t (by simp)
  have hp1 := hlt p (by simp)
  have hf1 := hlt f (by simp)
  unfold schurResidualCheck
  change Writes .total I τ (Stmt.allocs [.const 2 * (.var 0 * .var 0), .const 4] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [2 * (N * N), 4]) rfl
    (fun hBelow h => ?keep) ?_
  case keep =>
    obtain ⟨hT', r, a, w, x, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    exact ⟨hT'.of_below hBelow ht, r, a, w, x, h1, h2, h3, h4, h5, h6, h7, h8,
      ((hBelow f.1 hf1).2 f.2).trans h9⟩
  intro s₁ hlen hlens hBelow
  set L := μ.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen
  have hD : s₁.len L = 2 * (N * N) := by simpa using hlens 0 (by simp)
  have hSl : s₁.len (L + 1) = 4 := by simpa using hlens 1 (by simp)
  have hall : ∀ (s : Store ℝ), s.length = s₁.length → ∀ zs : List (ℕ × ℕ),
      zs ⊆ [a0, uo, t, p, f, (L, 0), (L + 1, 0)] → ∀ q : ℕ, (⟨s, q⟩ : Mem ℝ).Live zs := by
    intro s hs zs hzs q z hz
    have := hzs hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    change z.1 < s.length
    rw [hs, hlen]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  have hne : ∀ {b o n b' o' n' : ℕ}, b ≠ b' →
      Fp.Disj (Store.inBlock b o n) (Store.inBlock b' o' n') := fun h => Fp.disj_inBlock_of_ne h
  set G := Store.inBlock t.1 t.2 (2 * (N * N)) ⊔ Store.inBlock f.1 f.2 1 ⊔ Fp.above L
  have hGt : Store.inBlock t.1 t.2 (2 * (N * N)) ≤ G := fun _ _ h => Or.inl (Or.inl h)
  have hGL : ∀ b o n, L ≤ b → Store.inBlock b o n ≤ G := fun b o n hb _ _ hi => Or.inr (hi.1 ▸ hb)
  have hA₁ := hA.of_below hBelow ha0
  have hU₁ := hU.of_below hBelow huo
  have hT₁ := hT.of_below hBelow ht
  have hθ₁ : s₁.get p.1 p.2 = some θ := by
    rw [(hBelow p.1 hp1).2]; simpa using Store.get_of_readBlock hp (j := 0) (by omega) 0
  have hκ₁ : s₁.get p.1 (p.2 + 1) = some κ := by
    rw [(hBelow p.1 hp1).2]; simpa using Store.get_of_readBlock hp (j := 1) (by omega) 0
  -- the upper part
  refine (zeroStrictLower_writes (O := O) (Q := Q) (μ := ⟨s₁, μ.pos⟩) hS hM.zero hT₁).frame_seq_le
    rfl rfl (hall _ rfl _ (by simp) _) hGt fun m₁ hfr₁ ⟨_, hT₂⟩ => ?_
  have hA₂ := hA₁.of_eqOff hfr₁ hat.symm
  have hU₂ := hU₁.of_eqOff hfr₁ hut.symm
  have hl₁ := hall _ hfr₁.length_eq
  -- the residual
  refine (residualWords_writes (O := O) (Q := Q) (d := (L, 0)) hS hM hA₂ hU₂ hT₂
    (hl₁ _ (by simp) _) (by rw [hfr₁.len_eq]; simp [hD]) (hne (by simp; omega))
    (hne (by simp; omega)) (hne (by simp; omega))).frame_seq_le rfl rfl
    (hl₁ _ (by simp) _) (hGL _ _ _ le_rfl) fun m₂ hfr₂ ⟨_, hD₂⟩ => ?_
  have hl₂ := hall _ (hfr₂.length_eq.trans hfr₁.length_eq)
  have hkL : ∀ {b : ℕ × ℕ} {X : Matrix (Fin N) (Fin N) ℂ} {m m' : Mem ℝ} {o n : ℕ},
      b.1 < L → HoldsMatrix b X m.store → m.store.EqOff (Store.inBlock L o n) m'.store →
      HoldsMatrix b X m'.store := fun hb hX hfr => hX.of_eqOff hfr (hne (by omega))
  have hkL1 : ∀ {b : ℕ × ℕ} {X : Matrix (Fin N) (Fin N) ℂ} {m m' : Mem ℝ} {o n : ℕ},
      b.1 < L → HoldsMatrix b X m.store → m.store.EqOff (Store.inBlock (L + 1) o n) m'.store →
      HoldsMatrix b X m'.store := fun hb hX hfr => hX.of_eqOff hfr (hne (by omega))
  -- the norms
  refine (checkNorms_writes (O := O) (Q := Q) (s := (L + 1, 0)) hNm
    (hkL ha0 hA₂ hfr₂) (hkL huo hU₂ hfr₂) (hkL ht hT₂ hfr₂) hD₂ (hl₂ _ (by simp) _)
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; simp [hSl]) (by simp; omega) (by simp; omega)
    (by simp; omega) (by simp)).frame_seq_le rfl rfl (hl₂ _ (by simp) _)
    (hGL _ _ _ (by omega)) fun m₃ hfr₃ ⟨r, a, w, x, hr, ha, hw, hx, h1, h2, h3, h4, h5, h6, h7,
      h8⟩ => ?_
  have hl₃ := hall _ (hfr₃.length_eq.trans (hfr₂.length_eq.trans hfr₁.length_eq))
  have hgetp : ∀ o, o < p.2 + 2 → p.2 ≤ o → m₃.store.get p.1 o = s₁.get p.1 o := by
    intro o ho ho'
    rw [hfr₃.get_eq fun h => by obtain ⟨h, -⟩ := h; simp at h; omega,
      hfr₂.get_eq fun h => by obtain ⟨h, -⟩ := h; simp at h; omega,
      hfr₁.get_eq fun h => htp _ _ h ⟨rfl, by omega, by omega⟩]
  -- the decision
  refine (checkDecide_writes (O := O) (Q := Q) (s := (L + 1, 0)) (p := p) (f := f) hS hL hC hr
    ha hw hx (by rw [hgetp _ (by omega) le_rfl]; exact hθ₁)
    (by rw [hgetp _ (by omega) (by omega)]; exact hκ₁)
    (by rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]; simp [hSl])
    (by rw [hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq, (hBelow f.1 hf1).1]; exact hf)
    (by simp; omega) (by simp; omega) (hl₃ _ (by simp) _)).in_frame rfl rfl
    (hl₃ _ (by simp) _) |>.mono (sup_le (hGL _ _ _ (by omega))
      (fun _ _ h => Or.inl (Or.inr h))) fun m₄ hfr₄ hflag => ?_
  have hT₄ : HoldsMatrix t (upperPart T) m₄.store :=
    ((hkL ht hT₂ hfr₂).of_eqOff hfr₃ (hne (by simp; omega))).of_eqOff hfr₄
      (Fp.disj_sup_left.mpr ⟨hne (by simp; omega), htf.symm⟩)
  exact ⟨hT₄, r, a, w, x, h1, h2, h3, h4, h5, h6, h7, h8, hflag⟩

end Check

/-! ### The numbers of the check -/

section Numbers

/-- **The rounding of the reconstructed product**: under the standard model at $\boldsymbol{u}$
with $64(N + 1)^3\boldsymbol{u} \le 1$, the stored
$\mathrm{fl}(\mathrm{fl}(\mathbf{U}\mathbf{T})\mathbf{U}^{\mathsf H})$ of square matrices of order
$N$ is within $24(N + 1)^2\boldsymbol{u}\|\mathbf{U}\|_{\mathsf F}^2\|\mathbf{T}\|_{\mathsf F}$ of
$\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}$ in the Frobenius norm. -/
theorem _root_.NLAlib.Ops.StdModel.frobNorm_matMulWord_conjTranspose_sub_le {M : Machine ℝ}
    {u : ℝ} (hM : StdModel u id M) {N : ℕ} (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1)
    (U T : Matrix (Fin N) (Fin N) ℂ) :
    frobNorm (matMulWord M (matMulWord M U T) Uᴴ - U * T * Uᴴ) ≤
      24 * ((N : ℝ) + 1) ^ 2 * u * (frobNorm U ^ 2 * frobNorm T) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
  have hsq : √(N : ℝ) ≤ (N : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hu32 : 32 * ((N : ℝ) + 1) * u ≤ 1 := by
    have : 32 * ((N : ℝ) + 1) * u ≤ 64 * ((N : ℝ) + 1) ^ 3 * u := by
      have h2 : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
      have : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ 3 := by nlinarith
      nlinarith
    linarith
  have hc : √(N : ℝ) * (8 * ((N : ℝ) + 1) * u) ≤ 8 * ((N : ℝ) + 1) ^ 2 * u := by
    have := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 8 * ((N : ℝ) + 1) * u)
    nlinarith
  have hc8 : 8 * ((N : ℝ) + 1) ^ 2 * u ≤ 1 / 8 := by
    have : ((N : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) ^ 3 := by nlinarith
    nlinarith
  set W := matMulWord M U T
  have hFr : ∀ X : Matrix (Fin N) (Fin N) ℂ, frobNorm X ≤ √(N : ℝ) * specNorm X := fun X => by
    simpa using frobNorm_le_sqrt_card_mul_specNorm X
  have hW : frobNorm (W - U * T) ≤ 8 * ((N : ℝ) + 1) ^ 2 * u * (frobNorm U * frobNorm T) := by
    refine (hFr _).trans ?_
    have := hM.specNorm_matMulWord_sub_le (p := N) hu32 U T
    have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg (N : ℝ))
    nlinarith [mul_nonneg (frobNorm_nonneg U) (frobNorm_nonneg T)]
  have hM2 : frobNorm (matMulWord M W Uᴴ - W * Uᴴ) ≤
      8 * ((N : ℝ) + 1) ^ 2 * u * (frobNorm W * frobNorm U) := by
    refine (hFr _).trans ?_
    have := hM.specNorm_matMulWord_sub_le (p := N) hu32 W Uᴴ
    rw [frobNorm_conjTranspose] at this
    have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg (N : ℝ))
    nlinarith [mul_nonneg (frobNorm_nonneg W) (frobNorm_nonneg U)]
  have hWn : frobNorm W ≤ 2 * (frobNorm U * frobNorm T) := by
    have h1 : frobNorm W ≤ frobNorm (U * T) + frobNorm (W - U * T) := by
      have := frobNorm_add_le (U * T) (W - U * T); rwa [add_sub_cancel] at this
    have h2 := frobNorm_mul_le U T
    nlinarith [mul_nonneg (frobNorm_nonneg U) (frobNorm_nonneg T)]
  have e : matMulWord M W Uᴴ - U * T * Uᴴ = (matMulWord M W Uᴴ - W * Uᴴ) + (W - U * T) * Uᴴ := by
    rw [Matrix.sub_mul]; abel
  rw [e]
  refine (frobNorm_add_le _ _).trans ?_
  have h3 : frobNorm ((W - U * T) * Uᴴ) ≤ frobNorm (W - U * T) * frobNorm U := by
    have := frobNorm_mul_le (W - U * T) Uᴴ; rwa [frobNorm_conjTranspose] at this
  have hP : 0 ≤ frobNorm U * frobNorm T := mul_nonneg (frobNorm_nonneg U) (frobNorm_nonneg T)
  have hU0 := frobNorm_nonneg U
  have hk : 0 ≤ 8 * ((N : ℝ) + 1) ^ 2 * u := by positivity
  have h4 : 8 * ((N : ℝ) + 1) ^ 2 * u * (frobNorm W * frobNorm U) ≤
      8 * ((N : ℝ) + 1) ^ 2 * u * (2 * (frobNorm U * frobNorm T) * frobNorm U) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWn hU0) hk
  have h5 : frobNorm (W - U * T) * frobNorm U ≤
      8 * ((N : ℝ) + 1) ^ 2 * u * (frobNorm U * frobNorm T) * frobNorm U :=
    mul_le_mul_of_nonneg_right hW hU0
  nlinarith

/-- A rounded product of nonnegative numbers is at least $(1 - \boldsymbol{u})$ times the exact
one and at most $(1 + \boldsymbol{u})$ times it. -/
theorem _root_.NLAlib.Ops.StdModel.mul_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 - u) * (a * b) ≤ M.mul a b ∧ M.mul a b ≤ (1 + u) * (a * b) := by
  have h := hM.mul a b
  simp only [id, abs_of_nonneg (mul_nonneg ha hb)] at h
  constructor <;> linarith [abs_le.mp h]

/-- A rounded sum of nonnegative numbers is at least $(1 - \boldsymbol{u})$ times the exact one
and at most $(1 + \boldsymbol{u})$ times it. -/
theorem _root_.NLAlib.Ops.StdModel.add_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 - u) * (a + b) ≤ M.add a b ∧ M.add a b ≤ (1 + u) * (a + b) := by
  have h := hM.add a b
  simp only [id, abs_of_nonneg (add_nonneg ha hb)] at h
  constructor <;> linarith [abs_le.mp h]

theorem checkGuard_bounds {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu1 : u ≤ 1)
    {w t κ : ℝ} (hw : 0 ≤ w) (ht : 0 ≤ t) (hκ : 0 ≤ κ) :
    (1 - u) ^ 3 * (w * w * t * κ) ≤ checkGuard M w t κ ∧
      checkGuard M w t κ ≤ (1 + u) ^ 3 * (w * w * t * κ) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  obtain ⟨a1, a2⟩ := hM.mul_bounds hw hw
  have hww : 0 ≤ M.mul w w := le_trans (by nlinarith) a1
  obtain ⟨b1, b2⟩ := hM.mul_bounds hww ht
  have hwt : 0 ≤ M.mul (M.mul w w) t := le_trans (by nlinarith [mul_nonneg hww ht]) b1
  obtain ⟨c1, c2⟩ := hM.mul_bounds hwt hκ
  have h1u : 0 ≤ 1 - u := by linarith
  unfold checkGuard
  constructor
  · have e1 : (1 - u) * (w * w) * t ≤ M.mul w w * t := mul_le_mul_of_nonneg_right a1 ht
    have e2 : (1 - u) * ((1 - u) * (w * w) * t) ≤ M.mul (M.mul w w) t :=
      le_trans (mul_le_mul_of_nonneg_left e1 h1u) b1
    have e3 : (1 - u) * ((1 - u) * (w * w) * t) * κ ≤ M.mul (M.mul w w) t * κ :=
      mul_le_mul_of_nonneg_right e2 hκ
    have e4 := mul_le_mul_of_nonneg_left e3 h1u
    have e5 : (1 - u) ^ 3 * (w * w * t * κ) = (1 - u) * ((1 - u) * ((1 - u) * (w * w) * t) * κ) :=
      by ring
    linarith
  · have e1 : M.mul w w * t ≤ (1 + u) * (w * w) * t := mul_le_mul_of_nonneg_right a2 ht
    have e2 : M.mul (M.mul w w) t ≤ (1 + u) * ((1 + u) * (w * w) * t) :=
      b2.trans (mul_le_mul_of_nonneg_left e1 (by linarith))
    have e3 : M.mul (M.mul w w) t * κ ≤ (1 + u) * ((1 + u) * (w * w) * t) * κ :=
      mul_le_mul_of_nonneg_right e2 hκ
    nlinarith [mul_le_mul_of_nonneg_left e3 (by linarith : (0 : ℝ) ≤ 1 + u)]

/-- **The check is sound**: under the standard model at $\boldsymbol{u}$ with
$64(N + 1)^3\boldsymbol{u} \le 1$, $\kappa \ge 32(N + 1)^2\boldsymbol{u}$ and $\theta \ge 0$, let
$\hat r, \hat w, \hat t$ be at least $15/16$ times the Frobenius norms of the stored residual
$\mathrm{fl}(\mathbf{A}_0 - \mathrm{fl}(\mathrm{fl}(\mathbf{U}\mathbf{T})\mathbf{U}^{\mathsf H}))$,
of $\mathbf{U}$ and of $\mathbf{T}$, and $0 \le \hat a \le (17/16)\|\mathbf{A}_0\|_{\mathsf F}$.
If $\mathrm{fl}(\hat r + \hat g) \le \mathrm{fl}(\hat a\theta)$ for the guard $\hat g$ of
$(\hat w, \hat t, \kappa)$, then
$\|\mathbf{A}_0 - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_{\mathsf F} \le
2\theta\|\mathbf{A}_0\|_{\mathsf F}$, exactly. No hypothesis on $\mathbf{U}$, $\mathbf{T}$. -/
theorem frobNorm_sub_mul_mul_le_of_check {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {N : ℕ} (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) {κ θ : ℝ}
    (hκ : 32 * ((N : ℝ) + 1) ^ 2 * u ≤ κ) (hθ : 0 ≤ θ) {A₀ U T : Matrix (Fin N) (Fin N) ℂ}
    {r a w t : ℝ}
    (hr : 15 / 16 * frobNorm (subWord M A₀ (matMulWord M (matMulWord M U T) Uᴴ)) ≤ r)
    (ha0 : 0 ≤ a) (ha : a ≤ 17 / 16 * frobNorm A₀) (hw : 15 / 16 * frobNorm U ≤ w)
    (ht : 15 / 16 * frobNorm T ≤ t) (hpass : M.add r (checkGuard M w t κ) ≤ M.mul a θ) :
    frobNorm (A₀ - U * T * Uᴴ) ≤ 2 * θ * frobNorm A₀ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hu64 : u ≤ 1 / 64 := by
    have : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := one_le_pow₀ hN1
    nlinarith
  set Mh := matMulWord M (matMulWord M U T) Uᴴ
  set D := subWord M A₀ Mh
  set x := frobNorm (A₀ - Mh)
  set E := frobNorm (Mh - U * T * Uᴴ)
  set P := ((N : ℝ) + 1) ^ 2 * u * (frobNorm U ^ 2 * frobNorm T)
  have hP : 0 ≤ P := by positivity
  have hE : E ≤ 24 * P := by
    have := hM.frobNorm_matMulWord_conjTranspose_sub_le hu U T
    simp only [P, E, Mh]; linarith
  have hx : (1 - u) * x ≤ frobNorm D := by
    have h1 : x ≤ frobNorm D + frobNorm (D - (A₀ - Mh)) := by
      have := frobNorm_sub_le D (D - (A₀ - Mh)); rwa [sub_sub_cancel] at this
    have h2 := hM.frobNorm_subWord_sub_le A₀ Mh
    simp only [D] at h1 ⊢; nlinarith
  have hU0 := frobNorm_nonneg U
  have hT0 := frobNorm_nonneg T
  have hw0 : 0 ≤ w := le_trans (by positivity) hw
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  obtain ⟨hg, -⟩ := checkGuard_bounds hM (by linarith) hw0 ht0 hκ0
  set g := checkGuard M w t κ
  -- the guard covers the product error
  have hww : 15 / 16 * frobNorm U * (15 / 16 * frobNorm U) ≤ w * w :=
    mul_le_mul hw hw (by positivity) hw0
  have hwwt : 15 / 16 * frobNorm U * (15 / 16 * frobNorm U) * (15 / 16 * frobNorm T) ≤
      w * w * t := mul_le_mul hww ht (by positivity) (mul_nonneg hw0 hw0)
  have hwwtk : 15 / 16 * frobNorm U * (15 / 16 * frobNorm U) * (15 / 16 * frobNorm T) *
      (32 * ((N : ℝ) + 1) ^ 2 * u) ≤ w * w * t * κ :=
    mul_le_mul hwwt hκ (by positivity) (by positivity)
  have hu3 : 61 / 64 ≤ (1 - u) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ 3 - u)]
  have hgE : E ≤ g := by
    have : 24 * P ≤ (1 - u) ^ 3 * (w * w * t * κ) := by
      have e : 15 / 16 * frobNorm U * (15 / 16 * frobNorm U) * (15 / 16 * frobNorm T) *
          (32 * ((N : ℝ) + 1) ^ 2 * u) = 3375 / 128 * P := by simp only [P]; ring
      rw [e] at hwwtk
      have h0 : 0 ≤ w * w * t * κ := by positivity
      nlinarith
    linarith
  -- the pass
  have hg0 : 0 ≤ g := le_trans (frobNorm_nonneg _) hgE
  obtain ⟨hs, -⟩ := hM.add_bounds hr0 hg0
  obtain ⟨-, hth⟩ := hM.mul_bounds ha0 hθ
  have hA0 := frobNorm_nonneg A₀
  have hrx : 15 / 16 * ((1 - u) * x) ≤ r := le_trans (by nlinarith [frobNorm_nonneg D]) hr
  have hR : frobNorm (A₀ - U * T * Uᴴ) ≤ x + E := by
    have := frobNorm_add_le (A₀ - Mh) (Mh - U * T * Uᴴ)
    rwa [sub_add_sub_cancel] at this
  have hsum : (1 - u) * (r + g) ≤ (1 + u) * (a * θ) := hs.trans (hpass.trans hth)
  have haθ : a * θ ≤ 17 / 16 * frobNorm A₀ * θ := mul_le_mul_of_nonneg_right ha hθ
  have hx0 : 0 ≤ x := frobNorm_nonneg _
  nlinarith [mul_nonneg hu0 (mul_nonneg hA0 hθ), mul_nonneg hu0 hx0, mul_nonneg hu0 hg0,
    mul_nonneg hu0 hr0]

/-- **A near-orthonormal square factor bounds the middle factor**: if
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le e \le 1$ then
$(1 - e)^2\|\mathbf{T}\|_{\mathsf F} \le
(1 + e)\|\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_{\mathsf F}$. -/
theorem frobNorm_le_of_specNorm_conjTranspose_mul_self_sub_one_le {N : ℕ}
    {U T : Matrix (Fin N) (Fin N) ℂ} {e : ℝ} (he : specNorm (Uᴴ * U - 1) ≤ e) (he1 : e ≤ 1) :
    (1 - e) ^ 2 * frobNorm T ≤ (1 + e) * frobNorm (U * T * Uᴴ) := by
  set G := Uᴴ * U
  have hG : specNorm G ≤ 1 + e := by
    have := specNorm_add_le (G - 1) 1
    rw [sub_add_cancel] at this
    linarith [specNorm_one_le (n := Fin N) (𝕜 := ℂ)]
  have hU2 : specNorm U ^ 2 ≤ 1 + e := by rw [← specNorm_conjTranspose_mul_self]; exact hG
  have he0 : 0 ≤ e := (specNorm_nonneg _).trans he
  have hl : ∀ X : Matrix (Fin N) (Fin N) ℂ, (1 - e) * frobNorm X ≤ frobNorm (G * X) := by
    intro X
    have h1 : frobNorm X ≤ frobNorm (G * X) + frobNorm ((G - 1) * X) := by
      have := frobNorm_sub_le (G * X) ((G - 1) * X)
      rwa [show G * X - (G - 1) * X = X by rw [Matrix.sub_mul, Matrix.one_mul]; abel] at this
    have h2 := frobNorm_mul_le_specNorm_mul_frobNorm (G - 1) X
    nlinarith [frobNorm_nonneg X]
  have hr : ∀ X : Matrix (Fin N) (Fin N) ℂ, (1 - e) * frobNorm X ≤ frobNorm (X * G) := by
    intro X
    have h1 : frobNorm X ≤ frobNorm (X * G) + frobNorm (X * (G - 1)) := by
      have := frobNorm_sub_le (X * G) (X * (G - 1))
      rwa [show X * G - X * (G - 1) = X by rw [Matrix.mul_sub, Matrix.mul_one]; abel] at this
    have h2 := frobNorm_mul_le_frobNorm_mul_specNorm X (G - 1)
    nlinarith [frobNorm_nonneg X]
  have hGTG : frobNorm (G * T * G) ≤ (1 + e) * frobNorm (U * T * Uᴴ) := by
    have e1 : G * T * G = Uᴴ * (U * T * Uᴴ) * U := by simp only [G, Matrix.mul_assoc]
    rw [e1]
    have h1 := frobNorm_mul_le_frobNorm_mul_specNorm (Uᴴ * (U * T * Uᴴ)) U
    have h2 := frobNorm_mul_le_specNorm_mul_frobNorm Uᴴ (U * T * Uᴴ)
    rw [specNorm_conjTranspose] at h2
    have hU0 := specNorm_nonneg U
    calc _ ≤ frobNorm (Uᴴ * (U * T * Uᴴ)) * specNorm U := h1
      _ ≤ specNorm U * frobNorm (U * T * Uᴴ) * specNorm U :=
          mul_le_mul_of_nonneg_right h2 hU0
      _ = specNorm U ^ 2 * frobNorm (U * T * Uᴴ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hU2 (frobNorm_nonneg _)
  have h1 := hl T
  have h2 := hr (G * T)
  have h3 : (1 - e) * ((1 - e) * frobNorm T) ≤ (1 - e) * frobNorm (G * T) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

/-- The factors of an accurate Schur form with a near-orthonormal $\mathbf{U}$: if
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le 1/2$ and
$\|\mathbf{A}_0 - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_{\mathsf F} \le
(\theta/8)\|\mathbf{A}_0\|_{\mathsf F}$ with $\theta \le 1$, then
$\|\mathbf{U}\|_{\mathsf F}^2 \le (3/2)(N + 1)$ and
$\|\mathbf{T}\|_{\mathsf F} \le (27/4)\|\mathbf{A}_0\|_{\mathsf F}$. -/
theorem frobNorm_factors_le_of_frobNorm_sub_mul_mul_le {N : ℕ} {θ : ℝ} (hθ1 : θ ≤ 1)
    {A₀ U T : Matrix (Fin N) (Fin N) ℂ} (hUU : specNorm (Uᴴ * U - 1) ≤ 1 / 2)
    (hR : frobNorm (A₀ - U * T * Uᴴ) ≤ θ / 8 * frobNorm A₀) :
    frobNorm U ^ 2 ≤ 3 / 2 * ((N : ℝ) + 1) ∧ frobNorm T ≤ 27 / 4 * frobNorm A₀ := by
  have hF0 := frobNorm_nonneg A₀
  constructor
  · have h1 := frobNorm_sq_le_card_mul_specNorm_sq U
    have h2 : specNorm U ^ 2 ≤ 3 / 2 := by
      rw [← specNorm_conjTranspose_mul_self]
      have := specNorm_add_le (Uᴴ * U - 1) 1
      rw [sub_add_cancel] at this
      linarith [specNorm_one_le (n := Fin N) (𝕜 := ℂ)]
    simp only [Fintype.card_fin] at h1
    nlinarith [sq_nonneg (specNorm U), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  · have hUTU : frobNorm (U * T * Uᴴ) ≤ 9 / 8 * frobNorm A₀ := by
      have := frobNorm_sub_le A₀ (A₀ - U * T * Uᴴ)
      rw [sub_sub_cancel] at this
      nlinarith
    have := frobNorm_le_of_specNorm_conjTranspose_mul_self_sub_one_le (T := T) hUU (by norm_num)
    nlinarith

/-- The two terms of the check at an accurate Schur form: with the hypotheses of
`NLAlib.Schur.check_le_of_frobNorm_sub_mul_mul_le`, $\hat r + \hat g \le
(2/5)\theta\|\mathbf{A}_0\|_{\mathsf F}$. -/
theorem add_checkGuard_le_of_frobNorm_sub_mul_mul_le {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) {N : ℕ} (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) {κ θ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 64 * ((N : ℝ) + 1) ^ 2 * u) (hθ1 : θ ≤ 1)
    (huθ : 4096 * ((N : ℝ) + 1) ^ 3 * u ≤ θ) {A₀ U T : Matrix (Fin N) (Fin N) ℂ}
    (hUU : specNorm (Uᴴ * U - 1) ≤ 1 / 2)
    (hR : frobNorm (A₀ - U * T * Uᴴ) ≤ θ / 8 * frobNorm A₀) {r w t : ℝ}
    (hr : r ≤ 17 / 16 * frobNorm (subWord M A₀ (matMulWord M (matMulWord M U T) Uᴴ)))
    (hw0 : 0 ≤ w) (hw : w ≤ 17 / 16 * frobNorm U) (ht0 : 0 ≤ t)
    (ht : t ≤ 17 / 16 * frobNorm T) :
    r + checkGuard M w t κ ≤ 2 / 5 * (θ * frobNorm A₀) := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hu64 : u ≤ 1 / 64 := by
    have : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := one_le_pow₀ hN1
    nlinarith
  obtain ⟨hU2, hT⟩ := frobNorm_factors_le_of_frobNorm_sub_mul_mul_le hθ1 hUU hR
  set F := frobNorm A₀
  have hF0 : 0 ≤ F := frobNorm_nonneg _
  set X := ((N : ℝ) + 1) ^ 3 * u * F
  have hX : 4096 * X ≤ θ * F := by simp only [X]; nlinarith
  have hX0 : 0 ≤ X := by positivity
  have hU0 := frobNorm_nonneg U
  have hT0 := frobNorm_nonneg T
  have hUT : frobNorm U ^ 2 * frobNorm T ≤ 3 / 2 * ((N : ℝ) + 1) * (27 / 4 * F) :=
    mul_le_mul hU2 hT hT0 (by positivity)
  have hk : 0 ≤ ((N : ℝ) + 1) ^ 2 * u := by positivity
  have e3 : ((N : ℝ) + 1) ^ 2 * u * (3 / 2 * ((N : ℝ) + 1) * (27 / 4 * F)) = 81 / 8 * X := by
    simp only [X]; ring
  have hPX : ((N : ℝ) + 1) ^ 2 * u * (frobNorm U ^ 2 * frobNorm T) ≤ 81 / 8 * X := by
    rw [← e3]; exact mul_le_mul_of_nonneg_left hUT hk
  -- the residual
  set Mh := matMulWord M (matMulWord M U T) Uᴴ
  have hE := hM.frobNorm_matMulWord_conjTranspose_sub_le hu U T
  have hx : frobNorm (A₀ - Mh) ≤ θ / 8 * F + 243 * X := by
    have := frobNorm_add_le (A₀ - U * T * Uᴴ) (U * T * Uᴴ - Mh)
    rw [sub_add_sub_cancel, frobNorm_sub_comm (U * T * Uᴴ)] at this
    linarith only [this, hR, hE, hPX]
  have hD : frobNorm (subWord M A₀ Mh) ≤ (1 + u) * frobNorm (A₀ - Mh) := by
    have h1 := frobNorm_add_le (subWord M A₀ Mh - (A₀ - Mh)) (A₀ - Mh)
    rw [sub_add_cancel] at h1
    have h2 := hM.frobNorm_subWord_sub_le A₀ Mh
    linarith only [h1, h2]
  have hr' : r ≤ 17 / 16 * (65 / 64 * (θ / 8 * F + 243 * X)) := by
    refine hr.trans (mul_le_mul_of_nonneg_left (hD.trans ?_) (by norm_num))
    exact mul_le_mul (by linarith only [hu64]) hx (frobNorm_nonneg _) (by norm_num)
  -- the guard
  obtain ⟨-, hg⟩ := checkGuard_bounds hM (by linarith only [hu64]) hw0 ht0 hκ0
  have hww : w * w ≤ 17 / 16 * frobNorm U * (17 / 16 * frobNorm U) :=
    mul_le_mul hw hw hw0 (by positivity)
  have hwwt : w * w * t ≤ 17 / 16 * frobNorm U * (17 / 16 * frobNorm U) * (17 / 16 * frobNorm T) :=
    mul_le_mul hww ht ht0 (by positivity)
  have hwwtk : w * w * t * κ ≤
      17 / 16 * frobNorm U * (17 / 16 * frobNorm U) * (17 / 16 * frobNorm T) *
        (64 * ((N : ℝ) + 1) ^ 2 * u) := mul_le_mul hwwt hκ hκ0 (by positivity)
  have e2 : 17 / 16 * frobNorm U * (17 / 16 * frobNorm U) * (17 / 16 * frobNorm T) *
      (64 * ((N : ℝ) + 1) ^ 2 * u) =
        4913 / 64 * (((N : ℝ) + 1) ^ 2 * u * (frobNorm U ^ 2 * frobNorm T)) := by ring
  have hu3 : (1 + u) ^ 3 ≤ 21 / 20 := by
    nlinarith [mul_nonneg (sq_nonneg u) hu0]
  have h0 : 0 ≤ w * w * t * κ := by positivity
  have h1 : w * w * t * κ ≤ 4913 / 64 * (81 / 8 * X) := by
    linarith only [hwwtk, e2, hPX]
  have hg' : checkGuard M w t κ ≤ 21 / 20 * (4913 / 64 * (81 / 8 * X)) :=
    calc checkGuard M w t κ ≤ (1 + u) ^ 3 * (w * w * t * κ) := hg
      _ ≤ 21 / 20 * (w * w * t * κ) := mul_le_mul_of_nonneg_right hu3 h0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hθF : 0 ≤ θ * F := le_trans (by positivity) hX
  calc r + checkGuard M w t κ ≤ 17 / 16 * (65 / 64 * (θ / 8 * F + 243 * X)) +
        21 / 20 * (4913 / 64 * (81 / 8 * X)) := add_le_add hr' hg'
    _ = 1105 / 8192 * (θ * F) + 11042163 / 10240 * X := by ring
    _ ≤ 2 / 5 * (θ * F) := by linarith only [hX, hθF]

/-- **The check accepts an accurate Schur form**: under the standard model at $\boldsymbol{u}$
with $64(N + 1)^3\boldsymbol{u} \le 1$, $0 \le \kappa \le 64(N + 1)^2\boldsymbol{u}$,
$\theta \le 1$ and $4096(N + 1)^3\boldsymbol{u} \le \theta$, let
$\|\mathbf{U}^{\mathsf H}\mathbf{U} - \mathbf{I}\|_2 \le 1/2$ and
$\|\mathbf{A}_0 - \mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf H}\|_{\mathsf F} \le
(\theta/8)\|\mathbf{A}_0\|_{\mathsf F}$; let $\hat r, \hat w, \hat t \ge 0$ be at most $17/16$
times the Frobenius norms of the stored residual, of $\mathbf{U}$ and of $\mathbf{T}$ and
$\hat a \ge (15/16)\|\mathbf{A}_0\|_{\mathsf F}$. Then $\mathrm{fl}(\hat r + \hat g) \le
\mathrm{fl}(\hat a\theta)$. -/
theorem check_le_of_frobNorm_sub_mul_mul_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    {N : ℕ} (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) {κ θ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 64 * ((N : ℝ) + 1) ^ 2 * u) (hθ1 : θ ≤ 1) (huθ : 4096 * ((N : ℝ) + 1) ^ 3 * u ≤ θ)
    {A₀ U T : Matrix (Fin N) (Fin N) ℂ} (hUU : specNorm (Uᴴ * U - 1) ≤ 1 / 2)
    (hR : frobNorm (A₀ - U * T * Uᴴ) ≤ θ / 8 * frobNorm A₀) {r a w t : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 17 / 16 * frobNorm (subWord M A₀ (matMulWord M (matMulWord M U T) Uᴴ)))
    (ha : 15 / 16 * frobNorm A₀ ≤ a) (hw0 : 0 ≤ w) (hw : w ≤ 17 / 16 * frobNorm U) (ht0 : 0 ≤ t)
    (ht : t ≤ 17 / 16 * frobNorm T) :
    M.add r (checkGuard M w t κ) ≤ M.mul a θ := by
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hu64 : u ≤ 1 / 64 := by
    have : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 := one_le_pow₀ hN1
    nlinarith
  have hθ0 : 0 ≤ θ := le_trans (by positivity) huθ
  have hF0 := frobNorm_nonneg A₀
  have hθF : 0 ≤ θ * frobNorm A₀ := mul_nonneg hθ0 hF0
  have hsum := add_checkGuard_le_of_frobNorm_sub_mul_mul_le hM hu hκ0 hκ hθ1 huθ hUU hR hr hw0
    hw ht0 ht
  have hg0 : 0 ≤ checkGuard M w t κ := by
    obtain ⟨h, -⟩ := checkGuard_bounds hM (by linarith only [hu64]) hw0 ht0 hκ0
    exact (mul_nonneg (pow_nonneg (by linarith only [hu64]) 3) (by positivity)).trans h
  obtain ⟨-, hs⟩ := hM.add_bounds hr0 hg0
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  obtain ⟨hth, -⟩ := hM.mul_bounds ha0 hθ0
  have hlhs : (1 + u) * (r + checkGuard M w t κ) ≤ 65 / 64 * (2 / 5 * (θ * frobNorm A₀)) :=
    mul_le_mul (by linarith only [hu64]) hsum (add_nonneg hr0 hg0) (by norm_num)
  have haθ : 15 / 16 * (θ * frobNorm A₀) ≤ a * θ := by
    have := mul_le_mul_of_nonneg_right ha hθ0
    linarith only [this, show 15 / 16 * frobNorm A₀ * θ = 15 / 16 * (θ * frobNorm A₀) by ring]
  have hrhs : 63 / 64 * (15 / 16 * (θ * frobNorm A₀)) ≤ (1 - u) * (a * θ) :=
    mul_le_mul (by linarith only [hu64]) haθ (by linarith only [hθF])
      (by linarith only [hu64])
  refine hs.trans (le_trans ?_ hth)
  linarith only [hlhs, hrhs, hθF]

end Numbers

/-! ### Soundness and completeness of the outcome -/

section Outcome

variable {M : Machine ℝ} {u θ κ : ℝ} {N : ℕ} {A₀ U T : Matrix (Fin N) (Fin N) ℂ} {t f : ℕ × ℕ}
  {μ' : Mem ℝ}

/-- The flag of a check is the literal $0$ or the literal $1$, and the latter is positive under
the standard model at $\boldsymbol{u} < 1$. -/
theorem ResidualCheckOutcome.flag_cases {c₁ c₂ : ℝ}
    (h : ResidualCheckOutcome M c₁ c₂ θ κ A₀ U T t f μ') :
    μ'.store.get f.1 f.2 = some (M.lit 0) ∨ μ'.store.get f.1 f.2 = some (M.lit 1) := by
  obtain ⟨-, r, a, w, x, -, -, -, -, -, -, -, -, hf⟩ := h
  split_ifs at hf
  exacts [Or.inl hf, Or.inr hf]

/-- **A passed check is sound** (on every tape): with the norm factors $(15/16, 17/16)$, under
the standard model at $\boldsymbol{u}$ with $64(N + 1)^3\boldsymbol{u} \le 1$,
$\kappa \ge 32(N + 1)^2\boldsymbol{u}$ and $\theta \ge 0$, a flag $0$ implies
$\|\mathbf{A}_0 - \mathbf{U}\mathbf{T}'\mathbf{U}^{\mathsf H}\|_{\mathsf F} \le
2\theta\|\mathbf{A}_0\|_{\mathsf F}$ for the stored upper part $\mathbf{T}'$. -/
theorem ResidualCheckOutcome.frobNorm_sub_le (hM : StdModel u id M)
    (h : ResidualCheckOutcome M (15 / 16) (17 / 16) θ κ A₀ U T t f μ')
    (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) (hκ : 32 * ((N : ℝ) + 1) ^ 2 * u ≤ κ) (hθ : 0 ≤ θ)
    (h0 : μ'.store.get f.1 f.2 = some 0) :
    frobNorm (A₀ - U * upperPart T * Uᴴ) ≤ 2 * θ * frobNorm A₀ := by
  obtain ⟨-, r, a, w, x, h1, -, h3, h4, h5, -, h7, -, hf⟩ := h
  have hu0 : 0 ≤ u := by simpa using (abs_nonneg _).trans (hM.lit 1)
  have hu1 : u < 1 := by
    have : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 3 :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    nlinarith
  have hl1 : M.lit 1 ≠ 0 := by
    intro he; have := hM.lit 1; rw [he] at this; norm_num at this; linarith
  split_ifs at hf with hc
  · exact frobNorm_sub_mul_mul_le_of_check hM hu hκ hθ h1
      (le_trans (by positivity) h3) h4 h5 h7 hc
  · rw [h0] at hf; exact absurd (Option.some.inj hf).symm hl1

/-- **An accurate Schur form passes** the check: with the norm factors $(15/16, 17/16)$, under
the standard model at $\boldsymbol{u}$ with $64(N + 1)^3\boldsymbol{u} \le 1$,
$0 \le \kappa \le 64(N + 1)^2\boldsymbol{u}$, $\theta \le 1$ and
$4096(N + 1)^3\boldsymbol{u} \le \theta$, if $\|\mathbf{U}^{\mathsf H}\mathbf{U} -
\mathbf{I}\|_2 \le 1/2$ and $\|\mathbf{A}_0 - \mathbf{U}\mathbf{T}'\mathbf{U}^{\mathsf H}\|_{\mathsf
F} \le (\theta/8)\|\mathbf{A}_0\|_{\mathsf F}$ for the upper part $\mathbf{T}'$, the flag is $0$. -/
theorem ResidualCheckOutcome.flag_eq_zero (hM : StdModel u id M)
    (h : ResidualCheckOutcome M (15 / 16) (17 / 16) θ κ A₀ U T t f μ')
    (hu : 64 * ((N : ℝ) + 1) ^ 3 * u ≤ 1) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 64 * ((N : ℝ) + 1) ^ 2 * u)
    (hθ1 : θ ≤ 1) (huθ : 4096 * ((N : ℝ) + 1) ^ 3 * u ≤ θ) (hUU : specNorm (Uᴴ * U - 1) ≤ 1 / 2)
    (hR : frobNorm (A₀ - U * upperPart T * Uᴴ) ≤ θ / 8 * frobNorm A₀) :
    μ'.store.get f.1 f.2 = some 0 := by
  obtain ⟨-, r, a, w, x, h1, h2, h3, h4, h5, h6, h7, h8, hf⟩ := h
  have hc := check_le_of_frobNorm_sub_mul_mul_le hM hu hκ0 hκ hθ1 huθ hUU hR
    (le_trans (by positivity) h1) h2 h3 (le_trans (by positivity) h5) h6
    (le_trans (by positivity) h7) h8
  rw [hf, if_pos hc]
  exact congrArg some hM.zero

end Outcome

end NLAlib.Schur
