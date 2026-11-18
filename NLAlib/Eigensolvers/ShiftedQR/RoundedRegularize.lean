/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedRegularizeDraws

/-!
# The rounded `Regularize`

`Regularize` ([BanksGarzaVargasSrivastava2022, §4.2], called RitzOrDecouple there)
computes forward-approximate Ritz values with `SmallEig`, perturbs each by an independent uniform
sample of a small disk, and tests the perturbed values with `Optimal`. If they are optimal it
returns them; otherwise the dichotomy
(`NLAlib.exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues`) gives one among them whose
degree $k$ step decouples, and the program tries them in turn. The random perturbation keeps
every shift away from the spectrum, which the forward error of the rounded steps needs.

## Main definitions

* `NLAlib.ShiftedQR.regularizeWith`: the program with a small-eigenvalue routine;
  `NLAlib.ShiftedQR.regularize`: the program with the `SmallEig` kernel;
  `NLAlib.ShiftedQR.RegularizeOutcome`: its outcome.

## Main results

* `NLAlib.ShiftedQR.IsRandomSmallEig.smallEigLeaf_pwrites`: `SmallEig` with its forward error.
* `NLAlib.ShiftedQR.regularizeWith_pwrites_at`, `NLAlib.ShiftedQR.regularize_pwrites`:
  `Regularize` as a probabilistic block.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- `Regularize` with a small-eigenvalue routine and caller-owned scratch: the trailing
$k \times k$ block of the order-$N$ matrix `A` into `B`, the routine `SE` with the words `Qw` and
the cap $T$ (interface `[d, nq, T] (Bk, Q) → (Ev)`) into the $k$ pairs `S`, one random
perturbation of each pair (radius word `Rd`), `Optimal` with the word `C` into `G`; if optimal,
the flag `Fl` is $0$; otherwise `Fl` is $2$ and the $k$ trials run until one decouples (then `Fl`
is $1$). Trial $t$ records its rotations in slot $j_0 + t$ of the slotted log `Lg` of slot width
$w$; an accepted trial validates its slot. The interface is
`[N, k, nq, T, w, j0] (A, Rd, C, Thr, Qw, B, Z, G, Tm, SR, Ds, Rg) → (A, S, Fl, Lg)`. -/
def regularizeWithScratchWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, nq, T, w, j0] (A, Rd, C, Thr, Qw, B, Z, G, Tm, SR, Ds, Rg) → (A, S, Fl, Lg) {
    run (copyToWork (Op := O) (Tst := Q)).body [N, N - k, k] (A, B);
    run SE.body [k, nq, T] (B, Qw, S);
    run (regularizeDraws (O := O) (Q := Q)).body [k] (Rd, Z, S);
    run (regularizeDecide (O := O) (Q := Q)).body [N, k, w, j0]
      (A, S, C, Thr, Tm, SR, Ds, Rg, A, G, Fl, Lg)
  }

/-- **`Regularize` with a small-eigenvalue routine** ([BanksGarzaVargasSrivastava2022, §4.2],
RitzOrDecouple there): from the order-$N$ matrix `A`, the radius word `Rd` of the perturbations,
the word `C` of `Optimal` ($0.999\theta^k$), the threshold word `Thr` of the decoupling scan and
the words `Qw` of the routine `SE`, store $k$ perturbed approximate Ritz values at `S` and set the
flag `Fl` to $0$ (they are optimal, `A` unchanged) or $1$ (`A` holds a decoupled degree $k$ step);
`Fl` is $2$ only if no trial decoupled. The trials record their rotations in the slots
$j_0, \dots, j_0 + k - 1$ of the slotted log `Lg` of slot width $w$, the accepted one valid. All
scratch is scoped. The interface is `[N, k, nq, T, w, j0] (A, Rd, C, Thr, Qw) → (A, S, Fl, Lg)`.
-/
def regularizeWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, nq, T, w, j0] (A, Rd, C, Thr, Qw) → (A, S, Fl, Lg) {
    let B ← alloc (2 * (k * k));
    let Z ← alloc 2;
    let G ← alloc 1;
    let Tm ← alloc (2 * (N * N));
    let SR ← alloc (2 * k);
    let Ds ← alloc (2 * k);
    let Rg ← alloc 5;
    run (regularizeWithScratchWith SE).body [N, k, nq, T, w, j0]
      (A, Rd, C, Thr, Qw, B, Z, G, Tm, SR, Ds, Rg, A, S, Fl, Lg)
  }

/-- **`Regularize`** ([BanksGarzaVargasSrivastava2022, §4.2], RitzOrDecouple there):
`NLAlib.ShiftedQR.regularizeWith` with the `SmallEig` kernel as the routine
(`NLAlib.ShiftedQR.smallEigKernel`), no words and the cap $0$. From the order-$N$ matrix `A`, the
radius word `Rd` of the perturbations, the word `C` of `Optimal` ($0.999\theta^k$) and the
threshold word `Thr` of the decoupling scan, store $k$ perturbed approximate Ritz values at `S`
and set the flag `Fl` to $0$ (they are optimal, `A` unchanged) or $1$ (`A` holds a decoupled
degree $k$ step); `Fl` is $2$ only if no trial decoupled. The trials record their rotations in
the slots $j_0, \dots, j_0 + k - 1$ of the slotted log `Lg`. The interface is
`[N, k, w, j0] (A, Rd, C, Thr) → (A, S, Fl, Lg)`. -/
def regularize : Impl O Q := opsImpl% [N, k, w, j0] (A, Rd, C, Thr) → (A, S, Fl, Lg) {
  run (regularizeWith (smallEigKernel (O := O) (Q := Q))).body [N, k, 0, 0, w, j0]
    (A, Rd, C, Thr, Rd, A, S, Fl, Lg)
}

end Program

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section SmallEig

variable {O Q : Type} [Has EigenvalueKernelOp O]

/-- **A randomized small-eigenvalue kernel with its forward error**
([BanksGarzaVargasSrivastava2022, Definition 1.2]): if the interpretation's `smallEig` is a
randomized kernel with forward error $\beta$ and failure probability $\varphi$ on the stream `s`
(`NLAlib.ShiftedQR.IsRandomSmallEig`), the leaf routine that calls it on an upper Hessenberg
$\mathbf{B}$ of order $d$ writes only its output and, except with probability at most $\varphi$,
stores values within $\beta$ of a listing of the eigenvalues of $\mathbf{B}$ with multiplicity. -/
theorem IsRandomSmallEig.smallEigLeaf_pwrites {law : ℕ → Measure ℝ} {s : ℕ} {β φ : ℝ}
    {I : Interp O Q ℝ} (h : IsRandomSmallEig law s β φ I) {d : ℕ} {w o : ℕ × ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : IsUpperHessenberg B) :
    PWrites law I (smallEigLeaf (O := O) (Q := Q)).body (Env.frame [d] [w, o])
      (Store.inBlock o.1 o.2 (2 * d))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.Live [w, o] ∧ o.2 + 2 * d ≤ μ.store.len o.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock o.1 o.2 (2 * d)))
      (fun μ' => ∃ roots ev : Fin d → ℂ, IsEigenvalueListing B ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) φ := by
  obtain ⟨W, Bad, hBad, hφ, hI⟩ := h
  refine PWrites.of_window (s := s) (W := W d) (Bad := fun _ => Bad d B)
    (measurable_snd (hBad d B)) (fun _ _ => hφ d B hB) ?_
  rintro μ τ ⟨hH, hl, hroom, hdisj⟩ hgood
  unfold smallEigLeaf
  have hread : μ.readBlocks [w] [2 * (d * d)] = some [matrixWords B] := by
    simp [Mem.readBlocks, show μ.store.readBlock w.1 w.2 (2 * (d * d)) =
      some (matrixWords B) from hH]
  refine (writes_call (R := randomSmallEigRel s W Bad β) hI (d := [d]) (a := [w]) (b := [o])
    (k := W d) (ls := [2 * d]) rfl rfl rfl rfl rfl rfl trivial (by simp [Fp.Apart])
    (fun _ => ⟨by simpa [Mem.Live] using hl, ⟨[matrixWords B], hread, trivial⟩,
      by simpa [Mem.Room] using hroom⟩)).mono (by simp [Fp.blocks]) ?_
  rintro μ' - ⟨-, xs, ys, hr, hys, hrel⟩
  have hxs : xs = [matrixWords B] := Option.some.inj (hr.symm.trans hread)
  have hwin : (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) =
      Tape.windowFn τ s μ.pos (W d) := by
    funext j
    simp [Tape.window, Tape.windowFn, List.getD_eq_getElem?_getD]
  obtain ⟨roots, ev, hev, hfw, rfl⟩ := hrel d (matrixWords B) rfl hxs
    (by simpa using hB) (by
      change (fun j : Fin (W d) => (τ.window s μ.pos (W d)).getD j 0) ∉ _
      rw [hwin]
      simpa using hgood)
  rw [matrixOfWords_matrixWords] at hev
  refine ⟨roots, ev, hev, hfw, ?_⟩
  obtain ⟨y, hy, hyy⟩ := Option.bind_eq_some_iff.mp
    (by simpa [Mem.readBlocks, randomSmallEigRel] using hys)
  simp only [Option.some.injEq, List.cons.injEq, and_true] at hyy
  simpa [HoldsMatrix] using hyy ▸ hy

end SmallEig

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

/-- The words `Regularize` with scratch at `L, …, L + 6` reads, and the room it writes into: the
matrix $\mathbf{H}$ at `a`, the radius word $R$ at `rd`, the word $c_w$ at `c`, the threshold
word $t$ at `thr`, room for the $k$ output pairs at `s` and the flag at `f`, and seven scratch
buffers of the lengths of `NLAlib.ShiftedQR.regularize` above the $L$ buffers of the caller. -/
def RegularizeCtx (L : ℕ) {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (R cw tv : ℝ) (a rd c thr s f : ℕ × ℕ) (m : Mem ℝ) : Prop :=
  HoldsMatrix a H m.store ∧ m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some cw ∧
    m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
    f.2 < m.store.len f.1 ∧ m.store.length = L + 7 ∧ m.store.len L = 2 * (k * k) ∧
    m.store.len (L + 1) = 2 ∧ m.store.len (L + 2) = 1 ∧
    m.store.len (L + 3) = 2 * ((n + 1) * (n + 1)) ∧ m.store.len (L + 4) = 2 * k ∧
    m.store.len (L + 5) = 2 * k ∧ m.store.len (L + 6) = 5

/-- The context survives a write apart from the matrix and the three input words. -/
theorem RegularizeCtx.of_eqOff {L n k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {R cw tv : ℝ} {a rd c thr s f : ℕ × ℕ} {m m' : Mem ℝ} {F : Fp}
    (h : RegularizeCtx L k H R cw tv a rd c thr s f m) (hfr : m.store.EqOff F m'.store)
    (hF : Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1)) :
    RegularizeCtx L k H R cw tv a rd c thr s f m' := by
  obtain ⟨hA, hrd, hc, ht, hs, hf, hlen, h0, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hA.of_eqOff hfr (hF.mono le_rfl (by fp_sub)),
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hrd,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) hc,
    hfr.keep (Store.readsOnly_get _ _ _) (hF.mono le_rfl (by fp_sub)) ht, ?_⟩
  simp only [hfr.len_eq, hfr.length_eq]
  exact ⟨hs, hf, hlen, h0, h1, h2, h3, h4, h5, h6⟩

/-- **The outcome of `Regularize`**, with the optimality parameter $\theta$, the distance $d$ to
the spectrum, the threshold word $t$ and the backward error $\varepsilon$: either the flag is $0$,
`a` still holds $\mathbf{H}$, and `s` holds $k$ shifts that are $\theta$-optimal, at distance at
least $d$ from every $e_i$ and in $\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$; or the flag is $1$ and
`a` holds an upper Hessenberg perturbed unitary similarity of $\mathbf{H}$ with error
$\varepsilon$, by the exact unitary of the valid entries of the $k$ trial slots, one of whose bottom
$k$ subdiagonal entries passes the scan. In both cases the $k$ trial slots are closed after the
slots `LL` of the log. -/
def RegularizeOutcome {n : ℕ} (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (e : Fin (n + 1) → ℂ) (u θ d tv ε : ℝ) (a s f lg : ℕ × ℕ) (ns w : ℕ)
    (LL : List (Option (List GivensEntry))) (m' : Mem ℝ) : Prop :=
  ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
    (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store ∧
  ((m'.store.get f.1 f.2 = some 0 ∧ HoldsMatrix a H m'.store ∧ slotEntries w Ls = [] ∧
    ∃ zs : Fin k → ℂ,
      m'.store.readBlock s.1 s.2 (2 * k) = some ((List.ofFn zs).flatMap fun z => [z.re, z.im]) ∧
      IsOptimalRitzValues θ H (List.ofFn zs) ∧ (∀ j i, d ≤ ‖e i - zs j‖) ∧
      ∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∨
    (m'.store.get f.1 f.2 = some 1 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries w Ls)) H H' ε ∧
      IsUpperHessenberg H' ∧ HoldsMatrix a H' m'.store ∧
      ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ tv))

/-- The bounds on the perturbed shifts that `Regularize` needs: from shifts $z_j$ within
$\beta + R + \delta_j$ of a listing $\lambda$ of the eigenvalues of the trailing block, with
$\lvert z_j - e_l\rvert + \delta_j \ge \eta$, $\delta_j = 2\boldsymbol{u}(\lvert\lambda_j\rvert
+ \beta + R)$, under $\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$ and $0 < \omega \le \psi_k(\mathbf{H})$,
$\|\mathbf{H}\|_2 \le \Sigma$: the shifts are within $\omega^2/(2020\Sigma)$ of $\lambda$, in
$\mathbb{D}(0, 1.1\|\mathbf{H}\|_2)$ and at distance at least $\eta/2$ from every $e_l$. -/
theorem regularize_shift_bounds {n k N : ℕ} {u β R η ω S : ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lam zs : Fin k → ℂ} {e : Fin N → ℂ}
    (hu0 : 0 ≤ u) (hk : 0 < k) (hkn : k ≤ n) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hS : specNorm H ≤ S) (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ η)
    (hz : ∀ j : Fin k, ‖zs j - lam j‖ ≤ β + R + 2 * u * (‖lam j‖ + β + R) ∧
      ∀ l, η ≤ ‖zs j - e l‖ + 2 * u * (‖lam j‖ + β + R)) :
    (∀ j, ‖zs j - lam j‖ ≤ ω ^ 2 / (20 * 101 * S)) ∧ (∀ j, ‖zs j‖ ≤ 1.1 * specNorm H) ∧
      ∀ j l, η / 2 ≤ ‖e l - zs j‖ := by
  have hψH := hessenbergPotential_le_specNorm hk hkn H
  have hS0 : 0 < S := by linarith
  have hlH : ∀ j, ‖lam j‖ ≤ specNorm H := fun j =>
    hlam.norm_le_specNorm_of_trailingBlock (by omega) j
  have hδ : ∀ j, 2 * u * (‖lam j‖ + β + R) ≤ 2 * u * (S + β + R) := fun j => by
    have := hlH j; gcongr; linarith
  have hsmall : ω ^ 2 / (20 * 101 * S) ≤ 0.1 * specNorm H := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨fun j => ?_, fun j => ?_, fun j l => ?_⟩
  · linarith [(hz j).1, hδ j]
  · have h1 := norm_le_norm_add_norm_sub' (zs j) (lam j)
    linarith [(hz j).1, hδ j, hlH j]
  · have := (hz j).2 l
    rw [norm_sub_rev] at this
    nlinarith [hδ j]

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops

section Tail

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- The views of `Regularize` are apart: the matrix, the output pairs and the flag from each other
and from the three input words, all below the scratch handle $L$. -/
structure RegularizeViews (L : ℕ) (n k : ℕ) (a rd c thr s f : ℕ × ℕ) : Prop where
  /-- Every view is below the scratch handle. -/
  lt : a.1 < L ∧ rd.1 < L ∧ c.1 < L ∧ thr.1 < L ∧ s.1 < L ∧ f.1 < L
  /-- The matrix is apart from the shifts. -/
  as : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock s.1 s.2 (2 * k))
  /-- The matrix is apart from the flag. -/
  af : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1)
  /-- The shifts are apart from the flag. -/
  sf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1)
  /-- The outputs are apart from the three input words. -/
  io : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
    Store.inBlock f.1 f.2 1) (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔
      Store.inBlock thr.1 thr.2 1)

/-- The deterministic tail of `Regularize`: from the context
`NLAlib.ShiftedQR.RegularizeCtx` and $k \ge 1$ perturbed shifts at `s` as
`NLAlib.ShiftedQR.DrawsInv` leaves them (within $\beta + R + \delta_j$ of a listing of the
eigenvalues of the trailing block, $\eta - \delta_j$ from every eigenvalue), under the precision
conditions of `Optimal`, of the rounded steps and of the scan, the decision of `Regularize` ends
in `NLAlib.ShiftedQR.RegularizeOutcome` with $d = \eta/2$, the optimality parameter
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$ and the backward error
$2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularizeDecide_outcome {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {m : Mem ℝ} {k L : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω β R η tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖) (hη : 0 < η)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ η) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤ (16 * B)⁻¹ * (η / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (η / 2)) ^ k * √(n + 1) *
      (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    (hctx : RegularizeCtx L k H R
      (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
      a rd c thr s f m)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + k ≤ ns)
    (hw : k * n ≤ w)
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hlgL : lg.1 < L)
    (hlgv : ∀ b ∈ [a, rd, c, thr, s, f], b.1 ≠ lg.1)
    (hinv : DrawsInv u β R η (fun lam : Fin k → ℂ => IsEigenvalueListing (trailingBlock k H) lam)
      e rd (L + 1, 0) s k m) :
    Writes .total I τ (regularizeDecide (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, s, c, thr, (L + 3, 0), (L + 4, 0), (L + 5, 0),
        (L + 6, 0), a, (L + 2, 0), f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock (L + 2) 0 1 ⊔
        Store.inBlock f.1 f.2 1 ⊔ (Store.inBlock (L + 3) 0 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock (L + 4) 0 (2 * k) ⊔ Store.inBlock (L + 5) 0 (2 * k) ⊔
          Store.inBlock (L + 6) 0 5) ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (η / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f lg ns w LL) m := by
  set θ := 1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) with hθdef
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := hv
  obtain ⟨hA, -, hc, hthr, -, hrf, hlen, -, -, h2, h3, h4, h5, h6⟩ := hctx
  obtain ⟨-, -, lam, hlam, zs, hpairs, hzk⟩ := hinv
  have hu0 := hM.roundoff_nonneg
  have hψH := hessenbergPotential_le_specNorm hk0 hk H
  have hψ0 : 0 < hessenbergPotential k H := lt_of_lt_of_le hω hψ
  have hS0 : 0 < S := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le one_pos ((one_le_pseudoConditionNumber hV.ne_zero).trans hκ)
  have hθ : 0 < θ := by positivity
  obtain ⟨hzl, hz, hdist⟩ := regularize_shift_bounds hu0 hk0 hk hω hψ hSH hlam hβ hdη
    (fun j => (hzk j).2 j.isLt)
  have hx : (0 : ℝ) ≤ 300 * (n + 1) ^ 2 * u := by positivity
  have huo' : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * 1.1) * specNorm H) ^ k ≤ (θ * hessenbergPotential k H) ^ k := by
    refine le_trans ?_ (huo.trans (by gcongr))
    gcongr
  have hdich := fun hopt => exists_forall_isStableQRChain_exists_norm_subdiag_le (d := η / 2)
    hH hk0 hk hBk hω hV hHV hκ hgap hSH hψ hlam hzl hz (by positivity)
    (fun j i => hdist j i) hopt hx hxu hbound
  have hdec := regularizeDecide_writes (τ := τ) (m := m) (a := a) (s := s) (c := c) (thr := thr)
    (t := (L + 3, 0)) (sr := (L + 4, 0)) (ds := (L + 5, 0)) (rg := (L + 6, 0)) (g := (L + 2, 0))
    (f := f) (C := 1.1) hS hM hu1 hL hNat hC hk0 hk hH hnu hθ hψ0 hz huo' huo1 hA hpairs hc hthr
    (by simp [h2]) hrf (by simp [h3]) (by simp [h4]) (by simp [h5]) (by simp [h6])
    (by disjoint) (by disjoint) (by disjoint) (by disjoint) (by disjoint)
    (Fp.disj_sup_left.mpr ⟨by disjoint, Fp.disj_sup_right.mpr ⟨by disjoint, haf.symm⟩⟩)
    (by disjoint) (Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨has, hio.mono (by fp_sub) (by fp_sub)⟩,
        hio.mono (by fp_sub) (by fp_sub)⟩, by disjoint⟩, Fp.disj_sup_right.mpr
      ⟨Fp.disj_sup_right.mpr ⟨hsf.symm, hio.mono (by fp_sub) (by fp_sub)⟩,
        hio.mono (by fp_sub) (by fp_sub)⟩⟩) hdich hthrω hlog hj hw
    (by simp [Mem.Live, hlen]; omega)
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (dsimp only; omega) | exact hlgv _ (by simp))
  refine hdec.mono le_rfl ?_
  rintro m' hfr (⟨hF, hA', hlog', hopt⟩ |
    ⟨hF, j, Ls, es, hLs, hpl, hlog', hse, H', Rs, hch, hH', hA', hdec'⟩)
  · refine ⟨List.replicate k none, by simp, by simp [slotEntries_replicate_none],
      hlog'.reject_replicate hj, Or.inl ⟨hF, hA', slotEntries_replicate_none w k, zs, ?_, hopt,
        fun j i => hdist j i, hz⟩⟩
    have := readBlock_flatMap_pair_of_forall (s := m'.store) (b := s.1) (o := s.2)
      (zs := List.ofFn zs) fun j hj => by
        have hj' : j < k := by simpa using hj
        have hkeep := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (Fp.disj_sup_left.mpr
          ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨has.symm.mono
            (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl |>.symm, by disjoint⟩,
            hsf.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl |>.symm⟩,
            by disjoint⟩, Fp.disj_inBlock_of_ne (hlgv s (by simp)).symm⟩) (hpairs ⟨j, hj'⟩)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj'] using hkeep
    simpa using this
  · refine ⟨Ls, hLs, hpl, hlog', Or.inr ⟨hF, H', ?_, hH', hA', hdec'⟩⟩
    have hsim := hch.isPerturbedUnitarySimilarBy hx (C := 1.1) (fun s hs => by
      rw [List.eq_of_mem_replicate hs]; exact hz j)
    rw [hse, givensLog_padEntries]
    simpa using hsim

end Tail

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

/-- The separation the perturbations need: if $\beta, R \ge 0$ and
$\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$, then eigenvalues
separated by $2\omega^2/\Sigma$ are $4R$ apart ($0 < \omega \le \psi_k(\mathbf{H})$,
$\|\mathbf{H}\|_2 \le \Sigma$). -/
theorem regularize_sep_of_gap {n k : ℕ} {u β R ω S : ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} (hu0 : 0 ≤ u) (hk0 : 0 < k) (hk : k ≤ n) (hω : 0 < ω)
    (hψ : ω ≤ hessenbergPotential k H) (hSH : specNorm H ≤ S)
    (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖) (hβ0 : 0 ≤ β) (hR : 0 ≤ R)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S)) :
    ∀ i j, e i ≠ e j → 4 * R ≤ ‖e i - e j‖ := by
  intro i j hij
  have hS0 : 0 < S := lt_of_lt_of_le (lt_of_lt_of_le hω
    (hψ.trans (hessenbergPotential_le_specNorm hk0 hk H))) hSH
  have h1 := hgap i j (fun h => hij (h ▸ rfl))
  have h2 : 0 ≤ 2 * u * (S + β + R) := by positivity
  have h3 : ω ^ 2 / (20 * 101 * S) = 2 * ω ^ 2 / S / 4040 := by field_simp; ring
  have h4 : 0 ≤ 2 * ω ^ 2 / S := by positivity
  linarith

end NLAlib.ShiftedQR

namespace NLAlib.ShiftedQR

open Ops MeasureTheory

section Assembly

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The shifts of `Regularize` are apart from the matrix and the three input words. -/
theorem RegularizeViews.disj_shifts {L n k : ℕ} {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f) :
    Fp.Disj (Store.inBlock s.1 s.2 (2 * k))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock rd.1 rd.2 1 ⊔
        Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) :=
  Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hv.as.symm,
    hv.io.mono (by fp_sub) (by fp_sub)⟩, hv.io.mono (by fp_sub) (by fp_sub)⟩,
    hv.io.mono (by fp_sub) (by fp_sub)⟩

omit [Has IdxTst Q] [Has EigenvalueKernelOp O] in
/-- `Regularize` with a small-eigenvalue routine and scratch as a probabilistic block:
`NLAlib.ShiftedQR.regularizeWithScratchWith` from the context `NLAlib.ShiftedQR.RegularizeCtx`
with the routine's words stored below the scratch, apart from the shifts, ends in
`NLAlib.ShiftedQR.RegularizeOutcome` except with probability at most
$\varphi_{\mathrm{se}} + \varphi/2$: the routine (`NLAlib.ShiftedQR.RandomSmallEigContractAt` on
orders at most $k$ and norms at most $\Sigma$) fails with probability at most
$\varphi_{\mathrm{se}}$, the $k$ perturbations with probability at most $\varphi/2$, the rest is
deterministic. -/
theorem regularizeWithScratchWith_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k L : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (hv : RegularizeViews L n k a rd c thr s f)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ} (hqL : qw.1 < L)
    (hqw : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + k ≤ ns)
    (hw : k * n ≤ w) (hlgL : lg.1 < L)
    (hlgv : ∀ b ∈ [a, rd, c, thr, qw, s, f], b.1 ≠ lg.1) :
    PWrites law I (regularizeWithScratchWith SE).body
      (Env.frame [n + 1, k, nq, T, w, LL.length] [a, rd, c, thr, qw, (L, 0), (L + 1, 0),
        (L + 2, 0), (L + 3, 0), (L + 4, 0), (L + 5, 0), (L + 6, 0), a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Fp.above L ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => RegularizeCtx L k H R
        (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
        a rd c thr s f m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        HoldsSlottedLog lg ns w LL [] m.store)
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f lg ns w LL)
      (φse + φ / 2) := by
  set cw := 0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k
  set η := R * √(φ / (2 * k))
  set Ctx := fun m : Mem ℝ => RegularizeCtx L k H R cw tv a rd c thr s f m ∧
    HoldsSlottedLog lg ns w LL [] m.store
  set Lam := fun lam : Fin k → ℂ => IsEigenvalueListing (trailingBlock k H) lam
  obtain ⟨⟨ha, hrd, hcl, htl, hsl, hfl⟩, has, haf, hsf, hio⟩ := id hv
  have hIn : ∀ {F : Fp}, Fp.Disj F (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1) →
      Fp.Disj F (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) →
      ∀ {m m'}, Ctx m → m.store.EqOff F m'.store → Ctx m' := fun hF hFl _ _ h hfr =>
    ⟨h.1.of_eqOff hfr hF, hfr.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _) hFl h.2⟩
  have hLlg : ∀ {i o m o' m'}, L ≤ i →
      Fp.Disj (Store.inBlock i o m) (Store.inBlock lg.1 o' m') :=
    fun hi => Fp.disj_inBlock_of_ne (by omega)
  have hslg : Fp.Disj (Store.inBlock s.1 s.2 (2 * k))
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) := Fp.disj_inBlock_of_ne (hlgv s (by simp))
  have hsep := regularize_sep_of_gap hM.roundoff_nonneg hk0 hk hω hψ hSH hgap hβ0 hR.le hβ
  have hsIn := hv.disj_shifts
  have hHt : IsUpperHessenberg (trailingBlock k H) := hH.subBlock (r := (n + 1 - k, k)) (by omega)
  have hHtS : specNorm (trailingBlock k H) ≤ S := (specNorm_trailingBlock_le H (by omega)).trans hSH
  have hqLw : ∀ {o m : ℕ}, Fp.Disj (Store.inBlock L o m) (Store.inBlock qw.1 qw.2 qs.length) :=
    Fp.disj_inBlock_of_ne (by omega)
  unfold regularizeWithScratchWith
  have h1 : PWrites law I (copyToWork (Op := O) (Tst := Q)).body
      (Env.frame [n + 1, n + 1 - k, k] [a, (L, 0)]) (Store.inBlock L 0 (2 * (k * k)))
      (fun m => Ctx m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs)
      (fun m => (Ctx m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs) ∧
        HoldsMatrix (L, 0) (trailingBlock k H) m.store) 0 := by
    refine PWrites.of_writes le_rfl fun m τ ⟨hm, hq⟩ => ?_
    obtain ⟨⟨hA, -, -, -, -, -, hlen, h0, -⟩, -⟩ := id hm
    refine (copyToWork_writes (τ := τ) (w := (L, 0)) (lo := n + 1 - k) (d := k) hS
      (by simp [Mem.Live, hlen]; omega) hA (by omega) (by simp [h0]) (by disjoint)).mono le_rfl ?_
    rintro m' hfr ⟨-, hB⟩
    exact ⟨⟨hIn (by disjoint) (hLlg le_rfl) hm hfr,
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) hqLw hq⟩, hB⟩
  have h2 : PWrites law I SE.body (Env.frame [k, nq, T] [(L, 0), qw, s])
      (Store.inBlock s.1 s.2 (2 * k))
      (fun m => (Ctx m ∧ m.store.readBlock qw.1 qw.2 qs.length = some qs) ∧
        HoldsMatrix (L, 0) (trailingBlock k H) m.store)
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s 0 m) φse := by
    refine (hSE (w := (L, 0)) (q := qw) (o := s) (trailingBlock k H) le_rfl hHt hHtS).mono_eqOff
      ?_ ?_
    · rintro m ⟨⟨hm, hq⟩, hB⟩
      obtain ⟨⟨-, -, -, -, hrs, -, hlen, -⟩, -⟩ := hm
      exact ⟨hB, hq, by simp [Mem.Live, hlen]; omega, hrs, by disjoint, hqw.symm⟩
    · rintro m m' ⟨⟨hm, -⟩, -⟩ hfr ⟨roots, ev, hev, hfw, hO⟩
      have hm' := hIn hsIn hslg hm hfr
      obtain ⟨⟨-, hrd', -, -, -, -, -, -, hz', -⟩, -⟩ := id hm'
      refine ⟨hm', hrd', by simp [hz'], ev, hev, roots, fun j => ?_, fun j =>
        ⟨fun _ => hfw j, fun h => absurd h (Nat.not_lt_zero _)⟩⟩
      simpa using hO.read_entry j 0
  have h3 : PWrites law I (regularizeDraws (O := O) (Q := Q)).body
      (Env.frame [k] [rd, (L + 1, 0), s])
      (Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock (L + 1) 0 2)
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s 0 m)
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s k m) (φ / 2) :=
    (regularizeDraws_pwrites (β := β) hI hloc hS hM hD hU hk0 Lam e hR hφ.le hφ1 hsep
      (by disjoint) (by disjoint) (hio.mono (by fp_sub) (by fp_sub))).mono_eqOff
      (fun _ h => h.2) fun m m' hm hfr hinv =>
        ⟨hIn (Fp.disj_sup_left.mpr ⟨hsIn, by disjoint⟩)
          (Fp.disj_sup_left.mpr ⟨hslg, hLlg (by omega)⟩) hm.1 hfr, hinv⟩
  have h4 : PWrites law I (regularizeDecide (O := O) (Q := Q)).body _ _
      (fun m => Ctx m ∧ DrawsInv u β R η Lam e rd (L + 1, 0) s k m) _ 0 :=
    PWrites.of_writes le_rfl fun m τ ⟨hm, hinv⟩ => regularizeDecide_outcome hS hM hu1 hL hNat hC
      hk0 hk hv hH hV hHV hκ hBk hω hψ hSH hgap (by positivity) hβ hdη hnu huo huo1 hxu hbound
      hthrω hm.1 hj hw hm.2 hlgL
      (fun b hb => hlgv b (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h | h | h | h <;> simp [h])) hinv
  have hlive : ∀ (l : List (ℕ × ℕ)), (∀ x ∈ l, x.1 < L + 7) → ∀ m, Ctx m → m.Live l :=
    fun l hl m hm x hx => by obtain ⟨⟨-, -, -, -, -, -, hlen, -⟩, -⟩ := hm; rw [hlen]; exact hl x hx
  refine (PWrites.seq hI hloc (by positivity) (h1.in_frame rfl rfl fun m hm =>
      hlive _ (by simp; omega) m hm.1)
    (PWrites.seq hI hloc (by positivity) (h2.in_frame rfl rfl fun m hm =>
      hlive _ (by simp; omega) m hm.1.1)
      (PWrites.seq hI hloc le_rfl (h3.in_frame rfl rfl fun m hm => hlive _ (by simp; omega) m hm.1)
        (h4.in_frame rfl rfl fun m hm => hlive _ (by simp; omega) m hm.1)))).mono
    (fun _ h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) (by fp_sub) (fun _ h => h) (by simp)

omit [Has IdxTst Q] [Has EigenvalueKernelOp O] in
/-- **`Regularize` with a small-eigenvalue routine as a probabilistic block**, with the word count
`nq` apart from the words `qs` (`NLAlib.ShiftedQR.RandomSmallEigContractAt`):
`NLAlib.ShiftedQR.regularize_pwrites` for `NLAlib.ShiftedQR.regularizeWith`; the merged statement
is the case of the kernel, `NLAlib.ShiftedQR.regularizeWith_pwrites` the case `nq = qs.length`.
`Regularize` as a probabilistic block ([BanksGarzaVargasSrivastava2022, Lemma 4.6],
corrected: the constant of the dichotomy, Theorem 4.1, is $\tfrac12 k^{-1/(2k)}$, which the
printed last display drops to $(2k)^{-1/(2k)}$ without the factor $2$; the proof's test is
$\psi_k(\mathbf{H}) \ge \varepsilon$ where the paper prints $\le$; and the precision of
`Optimal`, Lemma 4.5, carries $n + kn^{3/2}$ where the paper has $2n^2$, which needs
$k \lesssim 2\sqrt{n}$): on a scalar machine with the standard model,
exact comparisons, index literals and exact natural literals up to $n + 1$, a measurable
tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$ and $B^{2/k} \le 2$, $1 \le k \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$, the
radius word $R > 0$, $0 < \varphi \le 1$, $\eta = R\sqrt{\varphi/(2k)}$,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the word $0.999\theta^k$ and a threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, and the precision conditions
$\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$, those of `Optimal` (with $C = 1.1$), and those
of the forward error of the rounded steps at the distance $\eta/2$
(`NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow`). Then
`NLAlib.ShiftedQR.regularize` writes only the matrix, the $k$ output pairs, the flag and the
log, and
except with probability at most $\varphi_{\mathrm{se}} + \varphi/2$ ends in
`NLAlib.ShiftedQR.RegularizeOutcome`: $\theta$-optimal shifts at distance at least $\eta/2$
from the spectrum with $\mathbf{H}$ unchanged, or a decoupled perturbed unitary similarity with
backward error $2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularizeWith_pwrites_at {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {nq T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k nq T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + k ≤ ns)
    (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, qw, s, f], b.1 ≠ lg.1) :
    PWrites law I (regularizeWith SE).body
      (Env.frame [n + 1, k, nq, T, w, LL.length] [a, rd, c, thr, qw, a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, qw, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
        f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f lg ns w LL)
      (φse + φ / 2) := by
  have hφ0 : 0 ≤ φse + φ / 2 := by positivity
  have e : (regularizeWith SE).body = Stmt.allocs [.const 2 * (.var 1 * .var 1),
      .const 2, .const 1, .const 2 * (.var 0 * .var 0), .const 2 * .var 1, .const 2 * .var 1,
      .const 5] (.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5] [⟨0, .var 6⟩,
        ⟨1, .var 7⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩, ⟨4, .var 10⟩, ⟨9, .const 0⟩, ⟨10, .const 0⟩,
        ⟨11, .const 0⟩, ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨15, .const 0⟩,
        ⟨0, .var 6⟩, ⟨6, .var 12⟩, ⟨7, .var 13⟩, ⟨8, .var 14⟩]
        (regularizeWithScratchWith SE).body) := rfl
  rw [e]
  refine PWrites.allocs rfl (Pre₁ := fun L μ => (RegularizeViews L n k a rd c thr s f ∧
    qw.1 < L ∧ lg.1 < L) ∧ (RegularizeCtx L k H R
      (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) tv
      a rd c thr s f μ ∧ μ.store.readBlock qw.1 qw.2 qs.length = some qs ∧
      HoldsSlottedLog lg ns w LL [] μ.store)) ?_ ?_ fun L => ?_
  · rintro m s₁ ⟨hl, hA, hq, hrd, hc, hthr, hrs, hrf, hlog, hlgl⟩ hlen hlens hBelow
    have hlv : a.1 < m.store.length ∧ rd.1 < m.store.length ∧ c.1 < m.store.length ∧
        thr.1 < m.store.length ∧ qw.1 < m.store.length ∧ s.1 < m.store.length ∧
        f.1 < m.store.length := by
      simpa [Mem.Live] using hl
    have hlgl' : lg.1 < m.store.length := hlgl lg (by simp)
    obtain ⟨h1, h2, h3, h4, hq7, h5, h6⟩ := hlv
    have hl7 := fun i (hi : i < 7) => hlens i (by simpa using hi)
    refine ⟨⟨⟨⟨h1, h2, h3, h4, h5, h6⟩, has, haf, hsf, hio⟩, hq7, hlgl'⟩, ⟨hA.of_below hBelow h1,
      hBelow.get_of h2 hrd, hBelow.get_of h3 hc, hBelow.get_of h4 hthr,
      by rw [(hBelow s.1 h5).1]; exact hrs, by rw [(hBelow f.1 h6).1]; exact hrf,
      by simpa using hlen, ?_⟩, (hBelow.readBlock hq7 qw.2 qs.length).trans hq,
      hBelow.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
        (fun b i g => by rw [g.1]; exact hlgl') hlog⟩
    simpa using ⟨hl7 0 (by norm_num), hl7 1 (by norm_num), hl7 2 (by norm_num),
      hl7 3 (by norm_num), hl7 4 (by norm_num), hl7 5 (by norm_num), hl7 6 (by norm_num)⟩
  · rintro m ⟨hl, -, -, -, -, -, -, -, -, hlgl⟩ st st' p hBelow ⟨Ls, hLs, hpl, hlog, hout⟩
    have hlv : a.1 < m.store.length ∧ s.1 < m.store.length ∧ f.1 < m.store.length := by
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hl
      exact ⟨hl.1, hl.2.2.2.2.2.1, hl.2.2.2.2.2.2⟩
    have hlgl' : lg.1 < m.store.length := hlgl lg (by simp)
    obtain ⟨h1, h5, h6⟩ := hlv
    refine ⟨Ls, hLs, hpl, hBelow.keep (HoldsSlottedLog.readsOnly_region _ _ _ _ _)
      (fun b i g => by rw [g.1]; exact hlgl') hlog, ?_⟩
    rcases hout with ⟨hF, hA, hse, zs, hzs, hrest⟩ | ⟨hF, H', hsim, hH', hA, hdec⟩
    · exact Or.inl ⟨hBelow.get_of h6 hF, hA.of_below hBelow h1, hse, zs,
        hBelow.readBlock_of h5 hzs, hrest⟩
    · exact Or.inr ⟨hBelow.get_of h6 hF, H', hsim, hH', hA.of_below hBelow h1, hdec⟩
  · by_cases hvL : RegularizeViews L n k a rd c thr s f ∧ qw.1 < L ∧ lg.1 < L
    · refine ((regularizeWithScratchWith_pwrites hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU hk0
        hk hvL.1 hH hV hHV hκ hBk hω hψ hSH hgap hR hφ hφ1 hβ hdη hnu huo huo1 hxu hbound
        hthrω hSE hvL.2.1 (hqw.mono (by fp_sub) le_rfl) hj hw hvL.2.2 hlgv).in_frame rfl rfl
        ?_).mono (fun _ h => h.2) (by fp_sub) (fun _ h => h) le_rfl
      rintro μ ⟨⟨-, -, -, -, -, -, hlen, -⟩, -⟩
      obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6⟩, -⟩, hq, hlgL⟩ := hvL
      simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, hlen]
      omega
    · exact PWrites.of_writes hφ0 fun _ _ h => absurd h.1 hvL

omit [Has IdxTst Q] in
/-- **`Regularize` as a probabilistic block** ([BanksGarzaVargasSrivastava2022, Lemma 4.6],
corrected: the constant of the dichotomy, Theorem 4.1, is $\tfrac12 k^{-1/(2k)}$, which the
printed last display drops to $(2k)^{-1/(2k)}$ without the factor $2$; the proof's test is
$\psi_k(\mathbf{H}) \ge \varepsilon$ where the paper prints $\le$; and the precision of
`Optimal`, Lemma 4.5, carries $n + kn^{3/2}$ where the paper has $2n^2$, which needs
$k \lesssim 2\sqrt{n}$): on a scalar machine with the standard model,
exact comparisons, index literals and exact natural literals up to $n + 1$, a measurable
tape-local interpretation whose `SmallEig` is a randomized kernel with forward error
$\beta \ge 0$ and failure probability $\varphi_{\mathrm{se}} \ge 0$ on a stream `s₀` uniform on
$[0, 1]$, and an exact polar disk sampler on the same stream: let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$
with $\kappa(\mathbf{V}) \le B$ and $B^{2/k} \le 2$, $1 \le k \le n$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by $2\omega^2/\Sigma$, the
radius word $R > 0$, $0 < \varphi \le 1$, $\eta = R\sqrt{\varphi/(2k)}$,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the word $0.999\theta^k$ and a threshold word
$t \ge (1 + \boldsymbol{u})^2\omega^2$, and the precision conditions
$\beta + R + 2\boldsymbol{u}(\Sigma + \beta + R) \le \omega^2/(2020\Sigma)$,
$4\boldsymbol{u}(\Sigma + \beta + R) \le \eta$, those of `Optimal` (with $C = 1.1$), and those
of the forward error of the rounded steps at the distance $\eta/2$
(`NLAlib.IsStableQRChain.exists_norm_subdiag_le_of_le_norm_inv_pow`). Then
`NLAlib.ShiftedQR.regularize` writes only the matrix, the $k$ output pairs, the flag and the
log, and
except with probability at most $\varphi_{\mathrm{se}} + \varphi/2$ ends in
`NLAlib.ShiftedQR.RegularizeOutcome`: $\theta$-optimal shifts at distance at least $\eta/2$
from the spectrum with $\mathbf{H}$ unchanged, or a decoupled perturbed unitary similarity with
backward error $2.1\|\mathbf{H}\|_2((1 + x)^k - 1)$, $x = 300(n+1)^2\boldsymbol{u}$. -/
theorem regularize_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I) (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv)
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + k ≤ ns)
    (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, s, f], b.1 ≠ lg.1) :
    PWrites law I (regularize (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, w, LL.length] [a, rd, c, thr, a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
        f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f lg ns w LL)
      (φse + φ / 2) := by
  unfold regularize
  refine ((regularizeWith_pwrites_at hI hloc hS hM hu1 hL hNat hC hβ0 hφse hD hU hk0 hk has haf hsf
    hio hH hV hHV hκ hBk hω hψ hSH hgap hR hφ hφ1 hβ hdη hnu huo huo1 hxu hbound hthrω
    (hSE.randomSmallEigContractAt k 0 0 S []) (qw := rd)
    (fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega) hj hw
    (fun b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hlgv _ (by simp))).in_frame (by simp)
    (by simp [Operand.evalList, Operand.eval]) ?_).mono ?_ le_rfl (fun _ h => h) le_rfl
  · rintro μ ⟨hl, -, -, -, -, -, -, -, hlgl⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl hlgl ⊢
    tauto
  · rintro μ ⟨hl, hA, hrest⟩
    refine ⟨?_, hA, by simp, hrest⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl ⊢
    tauto

end Assembly

end NLAlib.ShiftedQR
