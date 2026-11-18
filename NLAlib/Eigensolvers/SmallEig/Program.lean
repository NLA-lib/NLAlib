/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Core
public import NLAlib.Eigensolvers.SmallEig.Perturb
public import NLAlib.Ops.Blas.Fill

/-!
# The small-eigenvalue program

The algorithm `Eig` of [BanksGarzaVargasSrivastava2025, Theorem 1.1] as a fixed program
`[d, nq, T] (Bk, Q) → (Ev)` over scalar arithmetic, index literals, draws of a Gaussian stream and
the polar disk sampler, with no eigenvalue oracle: a block of order at most $1$ is copied; for a
larger one the output words are set to zero (so that they are stored even when the core stops
early), the block is copied to scratch, perturbed by a scaled complex Gaussian matrix
(`NLAlib.SmallEig.ginibrePerturb`), reduced to Hessenberg form (`NLAlib.hessenbergReduceLast`), and
deflated by the core (`NLAlib.SmallEig.smallEigCore` at the bottom width $1$) with the threshold
word `Q[6]` and the words `Q`. The program has the interface of a small-eigenvalue routine
(`NLAlib.ShiftedQR.RandomSmallEigContract`), so the shifted QR algorithm can run it in the place
of its kernel.

## Main definitions

* `NLAlib.SmallEig.smallEigProg`: the program.
* `NLAlib.SmallEig.smallEigDims`, `NLAlib.SmallEig.SmallEigInput`,
  `NLAlib.SmallEig.SmallEigSpectrum`: the dimensions, the memory of the input and the memory of
  the output of a run.

## Main results

* `NLAlib.SmallEig.smallEigProg_terminates`: termination on every tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The small-eigenvalue program in Schur mode** ([BanksGarzaVargasSrivastava2025, Theorem 1.1],
`Eig`, with the base case of order at most $1$, every loop capped, and the Schur form): for
$d \le 1$ keep the block and write the identity accumulator (`NLAlib.SmallEig.identityLeaf`);
otherwise write the identity accumulator, copy the threshold word `Q[6]` to scratch `Th`, perturb
the block in place (`NLAlib.SmallEig.ginibrePerturb` with the Gaussian stream `sG` and the scale
word `Q[0]`), reduce it to Hessenberg form recording the rotations
(`NLAlib.hessenbergReduceLast` into a scoped log of $d$ slots of $d$ entries), replay them on the
accumulator (`NLAlib.givensReplayColumns`), and run the core in Schur mode at the bottom width
$1$ with the threshold word `Th`, the $n_q$ words `Q`, the cap $T$ and the log shape
$(T + d, d)$, into the block, the accumulator and a scratch failure word. The output is the
triangular block $\widehat{\mathbf{T}}_b$ in `Bk` and its accumulator $\widehat{\mathbf{U}}_b$ in
`Ub`; the eigenvalues are the diagonal of $\widehat{\mathbf{T}}_b$. The interface is
`[d, nq, T] (Bk, Q) → (Bk, Ub)`, that of a Schur leaf (`NLAlib.Schur.RandomSchurLeafContract`).
Algorithm: small-eig -/
def smallEigProg (sG : ℕ) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Bk, Ub) {
  run (identityLeaf (O := O) (Q := Q)).body [d, nq, T] (Bk, Qw, Bk, Ub);
  ifPos d - 1 {
    let Fl ← alloc 1;
    let Th ← alloc 1;
    let Lg ← alloc (d * (1 + 5 * d));
    call (Has.inj ScalarOp.copy) [] (Qw[6]) → (Th);
    run (ginibrePerturb (O := O) (Q := Q) sG).body [d, nq] (Bk, Qw, Bk);
    run (slottedLogOpen (O := O) (Q := Q)).body [d, d] (Lg);
    run (hessenbergReduceLast (O := O) (Q := Q)).body [d, d, 0] (Bk, Bk, Lg);
    run (givensReplayColumns (O := O) (Q := Q)).body [d, 0, 0, d, d, d] (Lg, Ub, Ub);
    run (smallEigCore (O := O) (Q := Q) sG).body [d, 1, nq, T, T, T + d, d]
      (Bk, Th, Qw, Ub, Bk, Ub, Fl)
  }
}

end Program

/-- The dimensions of a run at the order $n + 1$: the order, the number of words of
`NLAlib.SmallEig.smallEigParams` and the cap `NLAlib.SmallEig.smallEigCap`. -/
noncomputable def smallEigDims (n nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℕ :=
  [n + 1, (smallEigParams nmax S δ φ c₁ c₂).length, smallEigCap nmax S δ φ c₁ c₂]

/-- **The memory holding the input** of the small-eigenvalue program: $\mathbf{M}$ at `w`, the
words `NLAlib.SmallEig.smallEigParams` at `q`, room for the $2(n + 1)$ output words at `o`, the
views live and the output apart from the matrix and the words. -/
def SmallEigInput {n : ℕ} (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) (w q o : ℕ × ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  HoldsMatrix w M μ.store ∧
    μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
      some (smallEigParams nmax S δ φ c₁ c₂) ∧
    μ.Live [w, q, o] ∧ o.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len o.1 ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))

/-- **The memory holding the spectrum of a nearby matrix**: the output at `o` lists all
eigenvalues, with multiplicity, of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$. -/
def SmallEigSpectrum {n : ℕ} (w o : ℕ × ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (δ : ℝ)
    (μ' : Mem ℝ) : Prop :=
  ∃ (Tb Ub E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HoldsMatrix w Tb μ'.store ∧
    HoldsMatrix o Ub μ'.store ∧ Tb.IsUpperTriangular ∧ specNorm E ≤ δ ∧
    IsEigenvalueListing (M + E) (fun i => Tb i i)

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

end Theorems

section Termination

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- Two near-unitary updates of the accumulator compose: if $\mathbf{X}'$ is within $e_1$ of
a unitary $\mathbf{V}_1$ and $\mathbf{U}'$ within $e_2\|\mathbf{X}'\|_2$ of $\mathbf{X}'\mathbf{V}$
for a unitary $\mathbf{V}$, $e_2 \ge 0$, then $\mathbf{U}'$ is within $(1 + e_1)(1 + e_2) - 1$ of
the unitary $\mathbf{V}_1\mathbf{V}$. -/
theorem specNorm_sub_mul_le_of_near {N : ℕ} {X' V₁ U' V : Matrix (Fin N) (Fin N) ℂ}
    (hV₁ : HasOrthonormalCols V₁) (hV : HasOrthonormalCols V) {e₁ e₂ : ℝ} (he₂ : 0 ≤ e₂)
    (h₁ : specNorm (X' - V₁) ≤ e₁) (h₂ : specNorm (U' - X' * V) ≤ e₂ * specNorm X') :
    specNorm (U' - V₁ * V) ≤ (1 + e₁) * (1 + e₂) - 1 := by
  have hX : specNorm X' ≤ 1 + e₁ := by
    have e : X' = (X' - V₁) + V₁ := by abel
    have := specNorm_add_le (X' - V₁) V₁
    rw [← e] at this
    linarith [hV₁.specNorm_le_one]
  have e : U' - V₁ * V = (U' - X' * V) + (X' - V₁) * V := by
    simp only [Matrix.sub_mul]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  rw [hV.specNorm_mul_right]
  nlinarith [mul_le_mul_of_nonneg_left hX he₂]

/-- The accumulator bound of `NLAlib.SmallEig.smallEigProg`: the replay of the reduction (within
$(1 + 24\boldsymbol{u})^{(n+1)^2} - 1$ of a unitary) and the core (relative error
$(1 + 24\boldsymbol{u})^{R_c} - 1$) leave the accumulator within
$(1 + 24\boldsymbol{u})^{R} - 1$ of a unitary, $R$ = `NLAlib.SmallEig.smallEigLeafRotations`-type
count at $k_{\max} \ge n + 1$. -/
theorem smallEigProg_accumulator_le {u : ℝ} (hu0 : 0 ≤ u) {n kmax T : ℕ} (hdk : n + 1 ≤ kmax)
    {X' V₁ U' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hV₁ : HasOrthonormalCols V₁)
    (hV : HasOrthonormalCols V)
    (h₁ : specNorm (X' - V₁) ≤ (1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1)
    (h₂ : specNorm (U' - X' * V) ≤ ((1 + 24 * u) ^ (2 * (n + 1) * ((T + (n + 1)) * (n + 1) +
      2 * 1 * (1 + 2))) * (1 + 0) ^ (n + 1) - 1) * specNorm X') :
    specNorm (U' - V₁ * V) ≤
      (1 + 24 * u) ^ (kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)) - 1 := by
  have h1u : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have he₁ := h₁
  have hb := specNorm_sub_mul_le_of_near hV₁ hV (e₂ := (1 + 24 * u) ^ (2 * (n + 1) *
    ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2))) - 1) (by
      have := one_le_pow₀ (M₀ := ℝ) (n := 2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2)))
        h1u
      linarith) he₁ (by simpa using h₂)
  refine hb.trans ?_
  rw [add_sub_cancel, add_sub_cancel, ← pow_add]
  have h2' : (T + (n + 1)) * (n + 1) ≤ (T + kmax) * kmax := Nat.mul_le_mul (by omega) hdk
  have h3' : 2 * (n + 1) * ((T + (n + 1)) * (n + 1) + 2 * 1 * (1 + 2)) ≤
      2 * (kmax + 1) * ((T + kmax) * kmax + 6) := Nat.mul_le_mul (by omega) (by omega)
  have := pow_le_pow_right₀ h1u (Nat.add_le_add (Nat.mul_le_mul hdk hdk) h3')
  linarith

/-- The planes of the closed log of the reduction (`NLAlib.hessenbergReduceLastSlots` padded with
rejected slots) are in the order or the zero fill. -/
theorem hessenbergReduceLastSlots_closed_planes (M : Machine ℝ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (w : ℕ) :
    ∀ e ∈ slotEntries w ([] ++ (hessenbergReduceLastSlots M A).map some ++
      List.replicate (N - ([] ++ (hessenbergReduceLastSlots M A).map some).length) none),
      e.1 + 1 < N ∨ e = (0, 0, 0) := by
  intro e he
  rw [List.nil_append, slotEntries_append_replicate_none] at he
  simp only [slotEntries, List.mem_flatMap, List.mem_map] at he
  obtain ⟨_, ⟨es, hes, rfl⟩, he⟩ := he
  simp only [Option.map_some, Option.getD_some, padEntries, List.mem_append,
    List.mem_replicate] at he
  rcases he with he | ⟨-, rfl⟩
  · exact hessenbergReduceLastSlots_plane M A es hes e he
  · exact Or.inr rfl

/-- The core call of `NLAlib.SmallEig.smallEigProg` (`NLAlib.ShiftedQR.solveRoundedWith_terminates`
with the decoupler and the order-one leaf terminating) from an accumulator $\mathbf{X}'$ within
$(1 + 24\boldsymbol{u})^{(n+1)^2} - 1$ of the unitary $\mathbf{V}_1$: the run is total and leaves
the accumulator near a unitary (`NLAlib.SmallEig.smallEigProg_accumulator_le`). The frame is given
by its evaluations. -/
theorem smallEigProg_core_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : u ≤ 1 / 100) (hL : IsIndexLit M I)
    {n kmax : ℕ} (hdk : n + 1 ≤ kmax) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {T : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length) {ρ : Env}
    {ds : List IExp} {args : List Operand} {a t p uo f : ℕ × ℕ}
    (hd : IExp.evalList ρ.idx ds = some [n + 1, 1, qs.length, T, T, T + (n + 1), n + 1])
    (ha : Operand.evalList ρ args = some [a, t, p, uo, a, uo, f]) {tape : Tape ℝ} {μ : Mem ℝ}
    {H X' V₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ} (hl : μ.Live [a, t, p, uo, f])
    (hr : μ.Room [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * ((n + 1) * (n + 1)), 1])
    (hap : Fp.Apart [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hX : HoldsMatrix uo X' μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 qs.length = some qs)
    (hV₁ : HasOrthonormalCols V₁)
    (hX'b : specNorm (X' - V₁) ≤ (1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) :
    Writes .total I tape (.frame ds args (smallEigCore (O := O) (Q := Q) sG).body) ρ
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ Tb Ub V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a Tb μ'.store ∧
        HoldsMatrix uo Ub μ'.store ∧ HasOrthonormalCols V ∧
        specNorm (Ub - V) ≤
          (1 + 24 * u) ^ (kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)) - 1) μ := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have h0 : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have hD : TerminatingDecouplerRoutine n 1 T T qs (T + (n + 1)) (n + 1)
      (smallEigDecoupler (O := O) (Q := Q) sG) I :=
    smallEigDecoupler_terminatingDecouplerRoutine (O := O) (Q := Q) (sG := sG) (F := T)
      hS hL (nmax := n) hNat hC hQ hSmp hDisk hqs hlen (by omega) (by omega)
  have hLeaf : TerminatingLeafRoutine 0 (min 1 (n + 1)) qs T (identityLeaf (O := O) (Q := Q)) I :=
    by rw [show min 1 (n + 1) = 1 by omega]; exact identityLeaf_terminates hS h0 h1 qs T
  refine ((solveRoundedWith_terminates (n := n) (k := 1) (F := T) (T := T) (ns := T + (n + 1))
    (w := n + 1) (εL := 0) hS hM hu hL hNat hQ hC le_rfl _ hD _ hLeaf (tape := tape)
    (H := H) (U := X') hl hr hap hA hX ht hp).in_frame hd ha
    (fun x hx => hl x (by simp at hx ⊢; tauto))).mono le_rfl ?_
  rintro μ' - ⟨U', Tm, V, hTm, hU', hV, hb⟩
  exact ⟨Tm, U', _ * V, hTm, hU', hasOrthonormalCols_iff.mpr
    ((hV₁.conjTranspose_mul_mul V V).trans (hasOrthonormalCols_iff.mp hV)),
    smallEigProg_accumulator_le hu0 hdk hV₁ hV hX'b hb⟩

/-- **The memory of a core call of `NLAlib.SmallEig.smallEigProg`**: the block $\mathbf{H}$ at
`w`, the threshold word `qs[6]` at `(L + 1, 0)`, the words `qs` at `p`, the accumulator
$\mathbf{X}$ at `ub` and the failure word at `(L, 0)`, live, with room and apart: the precondition
of `NLAlib.ShiftedQR.solveRoundedWith_pwrites` and `NLAlib.ShiftedQR.solveRoundedWith_terminates`
at these views. -/
def SmallEigCoreReady {n : ℕ} (qs : List ℝ) (w p ub : ℕ × ℕ) (L : ℕ)
    (H X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [w, (L + 1, 0), p, ub, (L, 0)] ∧
    μ.Room [w, (L + 1, 0), p, ub, (L, 0)]
      [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [w, (L + 1, 0), p, ub, (L, 0)]
      [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * ((n + 1) * (n + 1)), 1] ∧
    HoldsMatrix w H μ.store ∧ HoldsMatrix ub X μ.store ∧
    μ.store.get (L + 1) 0 = some (qs.getD 6 0) ∧ μ.store.readBlock p.1 p.2 qs.length = some qs

/-- The order-$(n + 1) \ge 2$ branch of `NLAlib.SmallEig.smallEigProg` after the perturbation,
up to the core: open the scoped log at `(L + 2, 0)`, reduce the block recording the rotations
and replay them on the identity accumulator. On every tape the run writes only the block, the
accumulator and the scratch above `L`, stores the rounded Hessenberg form
`NLAlib.hessenbergReduceLastWord` of $\mathbf{A}$ and an accumulator within
$(1 + 24\boldsymbol{u})^{(n+1)^2} - 1$ of the exact unitary of the recorded rotations, and leaves
the memory of the core call (`NLAlib.SmallEig.SmallEigCoreReady`). The frames are given by their
evaluations. -/
theorem smallEigProg_reduce_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : u ≤ 1 / 100) (hL : IsIndexLit M I)
    {n : ℕ} (hn1 : 1 ≤ n) (hNat : IsExactNatLit id M (n + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) {qs : List ℝ} (hlen : 12 ≤ qs.length) {ρ : Env}
    {ds₁ ds₂ ds₃ : List IExp} {as₁ as₂ as₃ : List Operand} {w p ub : ℕ × ℕ} {L : ℕ}
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [n + 1, n + 1])
    (ha₁ : Operand.evalList ρ as₁ = some [(L + 2, 0)])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [n + 1, n + 1, 0])
    (ha₂ : Operand.evalList ρ as₂ = some [w, w, (L + 2, 0)])
    (hd₃ : IExp.evalList ρ.idx ds₃ = some [n + 1, 0, 0, n + 1, n + 1, n + 1])
    (ha₃ : Operand.evalList ρ as₃ = some [(L + 2, 0), ub, ub])
    {tape : Tape ℝ} {μ : Mem ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hwL : w.1 < L) (hpL : p.1 < L) (huL : ub.1 < L) (hlen₂ : μ.store.length = L + 3)
    (hFl : μ.store.len L = 1) (hTh : μ.store.len (L + 1) = 1)
    (hLg : μ.store.len (L + 2) = (n + 1) * (1 + 5 * (n + 1)))
    (hB : HoldsMatrix w A μ.store)
    (hU : HoldsMatrix ub (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) μ.store)
    (hp : μ.store.readBlock p.1 p.2 qs.length = some qs)
    (hThv : μ.store.get (L + 1) 0 = some (qs.getD 6 0))
    (hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))))
    (hpwu : Fp.Disj (Store.inBlock p.1 p.2 qs.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I tape
      (.seq (.frame ds₁ as₁ (slottedLogOpen (O := O) (Q := Q)).body)
        (.seq (.frame ds₂ as₂ (hessenbergReduceLast (O := O) (Q := Q)).body)
          (.frame ds₃ as₃ (givensReplayColumns (O := O) (Q := Q)).body))) ρ
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) ⊔ Fp.above L)
      (fun μ' => ∃ X' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        SmallEigCoreReady qs w p ub L (hessenbergReduceLastWord M A) X' μ' ∧
        specNorm (X' - givensLog (n + 1) (hessenbergReduceLastSlots M A).flatten) ≤
          (1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1) μ := by
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hab : ∀ b o' k, L ≤ b → Store.inBlock b o' k ≤ Store.inBlock w.1 w.2
      (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) ⊔
        Fp.above L := fun b o' k hb _ _ hi => Or.inr (hi.1 ▸ hb)
  have hnew : ∀ {b o k b' o' k' : ℕ}, b < L → L ≤ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') :=
    fun hb hb' => Fp.disj_inBlock_of_ne (by omega)
  refine (slottedLogOpen_writes (τ := tape) (μ := μ) (ns := n + 1) (w := n + 1)
    (lg := (L + 2, 0)) hS hM (by simp [Mem.Live, hlen₂]) (by simp [hLg])).frame_seq_le hd₁ ha₁
    (by simp [Mem.Live, hlen₂]) (hab _ _ _ (by omega)) ?_
  rintro μ₃ hfr₃ ⟨-, hlog₃⟩
  have hlen₃ : μ₃.store.length = L + 3 := by rw [hfr₃.length_eq]; exact hlen₂
  refine (hessenbergReduceLast_writes_word (τ := tape) (m := μ₃) (L := []) hS hC hL hNat
    (by omega) (by omega) hlog₃ (by simp; omega) (by omega) (by simp [Mem.Live, hlen₃]; omega)
    (hB.of_eqOff hfr₃ (hnew hwL (by omega)).symm) (hnew hwL (by omega))).frame_seq_le hd₂ ha₂
    (by simp [Mem.Live, hlen₃]; omega)
    (sup_le (le_sup_left.trans le_sup_left) (hab _ _ _ (by omega))) ?_
  rintro μ₄ hfr₄ ⟨-, hH₄, hlog₄⟩
  have hU₄ := (hU.of_eqOff hfr₃ (hnew huL (by omega)).symm).of_eqOff hfr₄
    (Fp.disj_sup_left.mpr ⟨hwu, (hnew huL (by omega)).symm⟩)
  have hlen₄ : μ₄.store.length = L + 3 := by rw [hfr₄.length_eq]; exact hlen₃
  refine ((givensReplayColumns_specNorm_sub_le (τ := tape) (μ := μ₄) (lo := 0) (d := n + 1) hS hM
    hu0 hu hQ hC (by omega) (hessenbergReduceLastSlots_closed_planes M A (n + 1))
    (Or.inr (by omega)) hlog₄.close
    (by simp [length_hessenbergReduceLastSlots]; omega) hU₄ (by simp [Mem.Live, hlen₄]; omega)
    (hnew huL (show L ≤ L + 2 by omega)).symm).in_frame hd₃ ha₃
    (by simp [Mem.Live, hlen₄]; omega)).mono (le_sup_right.trans le_sup_left) ?_
  rintro μ₅ hfr₅ ⟨X', hX', hX'b⟩
  have hlen₅ : μ₅.store.length = L + 3 := by rw [hfr₅.length_eq]; exact hlen₄
  have hlenB : ∀ b, μ₅.store.len b = μ.store.len b := fun b => by
    rw [hfr₅.len_eq, hfr₄.len_eq, hfr₃.len_eq]
  have hdwp := (hpwu.mono le_rfl le_sup_left).symm
  have hp₅ := hfr₅.keep (Store.readsOnly_readBlock _ _ _ _) (hpwu.mono le_rfl le_sup_right).symm
    (hfr₄.keep (Store.readsOnly_readBlock _ _ _ _)
      (Fp.disj_sup_left.mpr ⟨hdwp, (hnew hpL (by omega)).symm⟩)
      (hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) (hnew hpL (by omega)).symm hp))
  have hTh₅ := hfr₅.keep (Store.readsOnly_get _ _ _) (hnew huL (by omega))
    (hfr₄.keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨hnew hwL (by omega), Fp.disj_inBlock_of_ne (by omega)⟩)
      (hfr₃.keep (Store.readsOnly_get _ _ _) (Fp.disj_inBlock_of_ne (by omega)) hThv))
  have hH₅ := hH₄.of_eqOff hfr₅ hwu.symm
  refine ⟨X', ⟨by simp [Mem.Live, hlen₅]; omega, ?_, ?_, hH₅, hX', hTh₅, hp₅⟩, ?_⟩
  · simp only [Mem.Room]
    refine ⟨Store.le_len_of_readBlock hH₅ (by positivity), by simp [hlenB, hTh],
      Store.le_len_of_readBlock hp₅ (by omega), Store.le_len_of_readBlock hX' (by positivity),
      by simp [hlenB, hFl], trivial⟩
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨hnew hwL (by omega), hdwp, hwu, hnew hwL le_rfl⟩,
      ⟨(hnew hpL (by omega)).symm, (hnew huL (by omega)).symm, Fp.disj_inBlock_of_ne (by omega)⟩,
      ⟨hpwu.mono le_rfl le_sup_right, hnew hpL le_rfl⟩, hnew huL le_rfl⟩
  · have hc : 0 ≤ (1 + 24 * u) ^ ((n + 1) * (n + 1)) - 1 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := (n + 1) * (n + 1)) (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
      linarith
    rw [embedBlock_zero_self, List.nil_append, slotEntries_append_replicate_none,
      givensLog_slotEntries_map_some, Matrix.one_mul] at hX'b
    exact hX'b.trans (mul_le_of_le_one_right hc specNorm_one_le)

/-- The order-$(n + 1) \ge 2$ branch of `NLAlib.SmallEig.smallEigProg` after the perturbation:
the reduction and the replay (`NLAlib.SmallEig.smallEigProg_reduce_writes`), then the core: the
run is total, writes only the block, the accumulator and the scratch above `L`, and leaves the
accumulator near a unitary. The frames are given by their evaluations. -/
theorem smallEigProg_reduce_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : u ≤ 1 / 100) (hL : IsIndexLit M I)
    {n kmax : ℕ} (hn1 : 1 ≤ n) (hdk : n + 1 ≤ kmax) (hNat : IsExactNatLit id M (n + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {T : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs)
    (hlen : 12 ≤ qs.length) {ρ : Env} {ds₁ ds₂ ds₃ ds₄ : List IExp}
    {as₁ as₂ as₃ as₄ : List Operand} {w p ub : ℕ × ℕ} {L : ℕ}
    (hd₁ : IExp.evalList ρ.idx ds₁ = some [n + 1, n + 1])
    (ha₁ : Operand.evalList ρ as₁ = some [(L + 2, 0)])
    (hd₂ : IExp.evalList ρ.idx ds₂ = some [n + 1, n + 1, 0])
    (ha₂ : Operand.evalList ρ as₂ = some [w, w, (L + 2, 0)])
    (hd₃ : IExp.evalList ρ.idx ds₃ = some [n + 1, 0, 0, n + 1, n + 1, n + 1])
    (ha₃ : Operand.evalList ρ as₃ = some [(L + 2, 0), ub, ub])
    (hd₄ : IExp.evalList ρ.idx ds₄ = some [n + 1, 1, qs.length, T, T, T + (n + 1), n + 1])
    (ha₄ : Operand.evalList ρ as₄ = some [w, (L + 1, 0), p, ub, w, ub, (L, 0)])
    {tape : Tape ℝ} {μ : Mem ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hwL : w.1 < L) (hpL : p.1 < L) (huL : ub.1 < L) (hlen₂ : μ.store.length = L + 3)
    (hFl : μ.store.len L = 1) (hTh : μ.store.len (L + 1) = 1)
    (hLg : μ.store.len (L + 2) = (n + 1) * (1 + 5 * (n + 1)))
    (hB : HoldsMatrix w A μ.store)
    (hU : HoldsMatrix ub (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) μ.store)
    (hp : μ.store.readBlock p.1 p.2 qs.length = some qs)
    (hThv : μ.store.get (L + 1) 0 = some (qs.getD 6 0))
    (hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))))
    (hpwu : Fp.Disj (Store.inBlock p.1 p.2 qs.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))))) :
    Writes .total I tape
      (.seq (.frame ds₁ as₁ (slottedLogOpen (O := O) (Q := Q)).body)
        (.seq (.frame ds₂ as₂ (hessenbergReduceLast (O := O) (Q := Q)).body)
          (.seq (.frame ds₃ as₃ (givensReplayColumns (O := O) (Q := Q)).body)
            (.frame ds₄ as₄ (smallEigCore (O := O) (Q := Q) sG).body)))) ρ
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) ⊔ Fp.above L)
      (fun μ' => ∃ Tb Ub V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix w Tb μ'.store ∧
        HoldsMatrix ub Ub μ'.store ∧ HasOrthonormalCols V ∧
        specNorm (Ub - V) ≤
          (1 + 24 * u) ^ (kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)) - 1) μ := by
  have hab : ∀ b o' k, L ≤ b → Store.inBlock b o' k ≤ Store.inBlock w.1 w.2
      (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) ⊔
        Fp.above L := fun b o' k hb _ _ hi => Or.inr (hi.1 ▸ hb)
  rw [← Writes.seq_assoc_iff, ← Writes.seq_assoc_iff]
  refine (Writes.seq_assoc_iff.mpr (smallEigProg_reduce_writes hS hM hu hL hn1 hNat hC hQ hlen
    hd₁ ha₁ hd₂ ha₂ hd₃ ha₃ hwL hpL huL hlen₂ hFl hTh hLg hB hU hp hThv hwu hpwu)).seq_le le_rfl ?_
  rintro μ₅ hfr₅ ⟨X', ⟨hl, hr, hap, hH, hX', hTh₅, hp₅⟩, hX'b⟩
  refine (smallEigProg_core_terminates hS hM hu hL hdk hNat hC hQ hSmp hDisk hqs hlen hd₄ ha₄
    hl hr hap hH hX' hTh₅ hp₅ (hasOrthonormalCols_givensLog _ _) hX'b).mono
    (sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left))
      (hab _ _ _ le_rfl)) fun _ _ h => h

/-- **The small-eigenvalue program in Schur mode terminates, with its accumulator near a unitary
on every tape** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], every loop capped): for blocks
of order at most $k_{\max}$, the words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`), on a scalar machine with the standard model, index
literals and exact natural literals up to $k_{\max} + 1$, exact comparisons and conversion, draws
that store the tape entry and an exact polar sampler, `NLAlib.SmallEig.smallEigProg` is a
terminating Schur leaf (`NLAlib.ShiftedQR.TerminatingLeafRoutine`) with the accumulator error
$(1 + 24\boldsymbol{u})^{k^2 + 2(k+1)((T + k)k + 6)} - 1$ at $k = k_{\max}$: the replay of the
reduction and the replays of the core's rounds (`NLAlib.ShiftedQR.solveRoundedWith_terminates`
at the bottom width $1$, whose leaf is exact). -/
theorem smallEigProg_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu : u ≤ 1 / 100) (hL : IsIndexLit M I) {kmax : ℕ}
    (hNat : IsExactNatLit id M (kmax + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {T : ℕ} {qs : List ℝ}
    (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length) :
    TerminatingLeafRoutine
      ((1 + 24 * u) ^ (kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)) - 1) kmax qs T
      (smallEigProg (O := O) (Q := Q) sG) I := by
  intro d w p ub tape μ B hd hB hp hl hroom hwu hpwu
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have h0 : M.lit 0 = 0 := by simpa using hNat 0 (by omega)
  have h1 : M.lit 1 = 1 := by simpa using hNat 1 (by omega)
  have hwl : w.1 < μ.store.length := hl w (by simp)
  have hpl : p.1 < μ.store.length := hl p (by simp)
  have hul : ub.1 < μ.store.length := hl ub (by simp)
  set R := kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)
  have hR0 : 0 ≤ (1 + 24 * u) ^ R - 1 := by
    have := one_le_pow₀ (M₀ := ℝ) (n := R) (by linarith : (1 : ℝ) ≤ 1 + 24 * u); linarith
  unfold smallEigProg
  have hl4 : μ.Live [w, p, w, ub] := fun x hx => hl x (by simp at hx ⊢; tauto)
  refine (identityLeaf_writes (O := O) (Q := Q) (τ := tape) hS h0 (fun _ => h1) hl hroom
    hwu).frame_seq_le rfl rfl hl4 le_sup_right ?_
  rintro μ₀ hfr₀ ⟨-, hU₀⟩
  have hB₀ : HoldsMatrix w B μ₀.store := hB.of_eqOff hfr₀ hwu.symm
  have hp₀ := hfr₀.keep (Store.readsOnly_readBlock _ _ _ _)
    (hpwu.mono le_rfl le_sup_right).symm hp
  refine writes_ifPos (n := d - 1) rfl ?_
  split_ifs with hd1
  swap
  · exact ⟨B, 1, 1, hB₀, hU₀, hasOrthonormalCols_one, by simpa using hR0⟩
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hdk : n + 1 ≤ kmax := hd
  have hl₀ : μ₀.Live [w, p, ub] := fun x hx => hfr₀.length_eq ▸ hl x hx
  change Writes .total I tape (Stmt.allocs [.const 1, .const 1,
    .var 0 * (.const 1 + .const 5 * .var 0)] _) _ _ _ μ₀
  refine writes_allocs_preserving_post (ns := [1, 1, (n + 1) * (1 + 5 * (n + 1))]) rfl
    (fun hBelow ⟨Tb, Ub, V, h₁, h₂, h₃, h₄⟩ => ⟨Tb, Ub, V, h₁.of_below hBelow (hl₀ w (by simp)),
      h₂.of_below hBelow (hl₀ ub (by simp)), h₃, h₄⟩) ?_
  intro s₁ hlen₁ hlens hBelow
  set L := μ₀.store.length with hLdef
  simp only [List.length_cons, List.length_nil] at hlen₁
  have hwL : w.1 < L := hl₀ w (by simp)
  have hpL : p.1 < L := hl₀ p (by simp)
  have huL : ub.1 < L := hl₀ ub (by simp)
  have hFl : s₁.len L = 1 := by simpa using hlens 0 (by simp)
  have hTh : s₁.len (L + 1) = 1 := by simpa using hlens 1 (by simp)
  have hLg : s₁.len (L + 2) = (n + 1) * (1 + 5 * (n + 1)) := by simpa using hlens 2 (by simp)
  set F := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))
  have hab : ∀ b o' k, L ≤ b → Store.inBlock b o' k ≤ F ⊔ Fp.above L :=
    fun b o' k hb _ _ hi => Or.inr (hi.1 ▸ hb)
  have hnew : ∀ {b o k b' o' k' : ℕ}, b < L → L ≤ b' →
      Fp.Disj (Store.inBlock b o k) (Store.inBlock b' o' k') :=
    fun hb hb' => Fp.disj_inBlock_of_ne (by omega)
  have hp₁ := hBelow.readBlock_of hpL hp₀
  have hB₁ := hB₀.of_below hBelow hwL
  have hU₁ := hU₀.of_below hBelow huL
  -- the threshold word
  refine (writes_call_un (hS .copy) (x := (p.1, p.2 + 6)) (z := (L + 1, 0)) rfl rfl trivial
    (Store.get_of_readBlock hp₁ (j := 6) (by omega) 0) rfl (by simp [hTh])).seq_le
    (hab _ _ _ (by omega)) ?_
  rintro μ₁ hfr₁ ⟨-, hTh₁⟩
  have hlen₁' : μ₁.store.length = L + 3 := by rw [hfr₁.length_eq]; exact hlen₁
  have hB₂ := hB₁.of_eqOff hfr₁ (hnew hwL (by omega)).symm
  have hU₂ := hU₁.of_eqOff hfr₁ (hnew huL (by omega)).symm
  have hp₂ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hnew hpL (by omega)).symm hp₁
  -- the perturbation
  refine (ginibrePerturb_writes_word hS hL hSmp (sG := sG) (nq := qs.length) (τ := tape)
    (a := w) (q := p) (by simp [Mem.Live, hlen₁']; omega) hB₂
    (by simpa using Store.get_of_readBlock hp₂ (j := 0) (by omega) 0)).frame_seq_le rfl rfl
    (by simp [Mem.Live, hlen₁']; omega) (le_sup_left.trans le_sup_left) ?_
  rintro μ₂ hfr₂ ⟨-, hB₃⟩
  have hdwp := (hpwu.mono le_rfl le_sup_left).symm
  have hdwu := hwu
  have hU₃ := hU₂.of_eqOff hfr₂ hdwu
  have hp₃ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) hdwp hp₂
  have hTh₃ : μ₂.store.get (L + 1) 0 = some (qs.getD 6 0) :=
    hfr₂.keep (Store.readsOnly_get _ _ _) (hnew hwL (by omega)) hTh₁
  have hlen₂ : μ₂.store.length = L + 3 := by rw [hfr₂.length_eq]; exact hlen₁'
  exact smallEigProg_reduce_terminates hS hM hu hL hn1 hdk (hNat.mono (by omega)) hC hQ hSmp
    hDisk hqs hlen rfl rfl rfl rfl rfl rfl rfl rfl hwL hpL huL hlen₂ (by simp [hfr₂.len_eq,
      hfr₁.len_eq, hFl]) (by simp [hfr₂.len_eq, hfr₁.len_eq, hTh])
    (by simp [hfr₂.len_eq, hfr₁.len_eq, hLg]) hB₃ hU₃ hp₃ hTh₃ hwu hpwu
end Termination

end NLAlib.SmallEig
