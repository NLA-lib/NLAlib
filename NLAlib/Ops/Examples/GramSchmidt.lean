/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Count
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Example: modified Gram–Schmidt over the level-1 operations

The algorithm `NLAlib.Ops.Examples.mgs` orthogonalizes a vector `w` against the `k` rows of `Q`
and stores the `k` coefficients and the norm of the result in `R`. This is the example of the
first build, proved in the program logic (`NLAlib.Ops.Logic`) with block specifications.

## Main results

* Mathematics: the postcondition is the recurrence with local errors
  `NLAlib.Ops.Examples.MgsRec`, on decoded values; its analysis is not part of this file.
* The certificate (`NLAlib.Ops.Examples.mgs_spec`): for every interpretation meeting the
  contracts, `mgs` meets its contract in operand form (`NLAlib.Ops.Examples.mgsRel`): one
  allocation, one loop in the standard invariant form, a named step per call.
* The abstract theorem (`NLAlib.Ops.Examples.runs_mgs_rounded`): the same with the call counts
  `k (dot + neg + axpy) + nrm2`, by evaluating the static cost.
* The corollary (`NLAlib.Ops.Examples.runs_mgs_link_seq`): the program linked through the
  profile of sequential summation, down to scalar arithmetic meeting the standard model at `u`,
  by one application of the certificate; its scalar counts are
  `NLAlib.Ops.Examples.push_seq_mgsCount`.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-! ### Mathematics: the recurrence with local errors -/

/-- **The modified Gram–Schmidt recurrence with local errors**: after `j` steps from `w₀`, the
vector is `w` and the coefficients are `r`; each step computes a coefficient `ρ` as a dot product
up to `εd` and updates `w` by `w - ρ q_j` up to `εa`. -/
inductive MgsRec (dec : K → ℝ) (εd εa : ℝ) (n : ℕ) (q : ℕ → ℕ → K) (w₀ : ℕ → K) :
    ℕ → (ℕ → K) → List K → Prop
  /-- No step. -/
  | zero : MgsRec dec εd εa n q w₀ 0 w₀ []
  /-- One more step. -/
  | step {j : ℕ} {w w' : ℕ → K} {r : List K} {ρ t : K} : MgsRec dec εd εa n q w₀ j w r →
      IsDotErr dec εd n (q j) w ρ → dec t = -dec ρ → IsAxpyErr dec εa n t (q j) w w' →
      MgsRec dec εd εa n q w₀ (j + 1) w' (r ++ [ρ])

/-! ### The algorithm -/

/-- One step: `R_j := dot Q_j w; t := neg R_j; w := w + t Q_j`. -/
def mgsBody : Stmt Op Tst :=
  .seq (.call (Has.inj Blas1Op.dot) [.var 0] [⟨0, .var 2 + .var 6 * .var 0⟩, ⟨1, .var 3⟩]
      [⟨3, .var 5 + .var 6⟩])
    (.seq (.call (Has.inj ScalarOp.neg) [] [⟨3, .var 5 + .var 6⟩] [⟨4, .const 0⟩])
      (.call (Has.inj Blas1Op.axpy) [.var 0]
        [⟨4, .const 0⟩, ⟨0, .var 2 + .var 6 * .var 0⟩, ⟨1, .var 3⟩] [⟨1, .var 3⟩]))

/-- **Modified Gram–Schmidt**: orthogonalise `w` against the `k` columns of `Q`, in place, and
write the `k` coefficients and the norm in `R`. Two inputs `Q`, `w` and two outputs `w`, `R`.
Index variables: `n`, `k`, the offsets of `Q`, `w`, `w`, `R`, then the loop variable; buffer
variables: `Q`, `w`, `w`, `R`, then the scratch cell. -/
def mgs : Stmt Op Tst :=
  .alloc (.const 1) (.seq (.loop (.var 1) mgsBody)
    (.call (Has.inj Blas1Op.nrm2) [.var 0] [⟨1, .var 3⟩] [⟨3, .var 5 + .var 1⟩]))

/-- **`mgs` as an implementation**: two dimensions `n`, `k`, two inputs `Q`, `w`, two outputs
`w`, `R`. -/
def mgsImpl : Impl Op Tst := ⟨2, 2, 2, mgs⟩

/-! ### The contract -/

variable [Inhabited K]

/-- The outputs of `mgs`: the vector `ws'` and the coefficients followed by the norm, related to
the inputs by the recurrence with local errors. -/
def MgsOut (dec : K → ℝ) (ε : Blas1Err) (n k : ℕ) (qs ws ws' rν : List K) : Prop :=
  ∃ (r : List K) (ν : K), rν = r ++ [ν] ∧
    MgsRec dec (ε.dot n) ε.axpy n (fun j i => vec qs (j * n + i)) (vec ws) k (vec ws') r ∧
    IsNrm2Err dec (ε.dot n) ε.sqrt n (vec ws') ν

/-- **The contract of `mgs`**, in operand form, with two output blocks: at the dimensions
`[n, k]`, from the blocks `Q` (`k n` cells) and `w` (`n` cells) to the blocks `w` (`n` cells) and
`R` (`k + 1` cells). -/
@[simps (attr := storeNF)]
def mgsRel (dec : K → ℝ) (ε : Blas1Err) : BlockRel K where
  nd := 2
  inLens d := match d with
    | [n, k] => [k * n, n]
    | _ => []
  outLens d := match d with
    | [n, k] => [n, k + 1]
    | _ => []
  rel d X _ Y := match d, X, Y with
    | [n, k], [qs, ws], [ws', rν] => MgsOut dec ε n k qs ws ws' rν
    | _, _, _ => False

/-- The admitted operands of `mgs`: the length `n` is covered, `w` is updated in place, and
`Q`, `w`, `R` are in three buffers. -/
@[admNF] def MgsOperands (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ok (d.headD 0) ∧ ∃ Q w R, ins = [Q, w] ∧ outs = [w, R] ∧
    Q.1 ≠ w.1 ∧ Q.1 ≠ R.1 ∧ w.1 ≠ R.1

/-- The postcondition of `mgs`: `w` holds `ws'` and `R` holds the coefficients and the norm,
related to the inputs by the recurrence with local errors; nothing else is written. -/
def MgsRounded (dec : K → ℝ) (ε : Blas1Err) (n k : ℕ) (w R : ℕ × ℕ) (qs ws : List K)
    (μ μ' : Mem K) : Prop :=
  ∃ ws' rν : List K, ws'.length = n ∧ rν.length = k + 1 ∧ MgsOut dec ε n k qs ws ws' rν ∧
    μ' = (μ.updBlock w ws').updBlock R rν

/-! ### The certificate, the abstract theorem and its corollary by linking -/

omit [Inhabited K] in
/-- The call counts of `mgs`: `k` times `dot`, `neg`, `axpy` at the dimension `n`, and one
`nrm2`. -/
noncomputable def mgsCount (n k : ℕ) : Count Op Tst :=
  k • (Count.one (Has.inj Blas1Op.dot) [n] + (Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj Blas1Op.axpy) [n])) + Count.one (Has.inj Blas1Op.nrm2) [n]

/-- The workspace of `mgs`: one cell and the workspace of the operation that needs most. -/
def mgsPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  1 + max (max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj ScalarOp.neg) [])
    (W (Has.inj Blas1Op.axpy) [n]))) (W (Has.inj Blas1Op.nrm2) [n])

omit [Inhabited K] in
theorem staticCost_mgs (n k a b b' c : ℕ) :
    staticCost (mgs (Op := Op) (Tst := Tst)) [n, k, a, b, b', c] = mgsCount n k := by
  simp [mgs, mgsBody, staticCost, useCost, mgsCount]

omit [Inhabited K] in
theorem staticPeak_mgs_le (W : Op → List ℕ → ℕ) (n k a b b' c : ℕ) :
    staticPeak W (mgs (Op := Op) (Tst := Tst)) [n, k, a, b, b', c] ≤ mgsPeak W n := by
  simp only [mgs, mgsBody, staticPeak, mgsPeak]
  refine Nat.add_le_add_left (max_le_max (Finset.sup_le fun j _ => ?_) ?_) _ <;> simp

/-- **The certificate of `mgs`**: for every interpretation meeting the contracts of scalar
arithmetic and of the level-1 operations, `mgs` meets its contract, which has two output blocks.
So `mgs` is an operation (an orthogonalisation step) for the algorithms above it. Proved by block
specifications. -/
theorem mgs_spec {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ a, dec (M.neg a) = -dec a) :
    (mgsImpl (Op := Op) (Tst := Tst)).Meets J .total ((mgsRel dec ε).spec (MgsOperands ok)) := by
  cert_intro [n, k] (Q, x) → (w, R) reads (qs, ws)
  obtain ⟨hok, rfl, hQw, hQR, hwR⟩ := hadm
  refine writes_alloc rfl fun s₁ hs₁ ht hB => ?_
  refine Writes.seq_le (writes_loop rfl
    (fun j => Store.inBlock w.1 w.2 n ⊔ Store.inBlock R.1 R.2 j ⊔ Store.inBuf μ.store.length)
    (fun j _ => by fp_sub)
    (fun j m' => m'.pos = μ.pos ∧ ∃ ws' r, m'.store.readBlock w.1 w.2 n = some ws' ∧
      m'.store.readBlock R.1 R.2 j = some r ∧
      MgsRec dec (ε.dot n) ε.axpy n (fun j i => vec qs (j * n + i)) (vec ws) j (vec ws') r)
    ⟨rfl, ws, [], by kept, rfl, .zero⟩ fun j hj m₁ hfr ⟨hpos, ws', r, hw', hr', hrec⟩ => ?_)
    (by fp_sub) fun m₁ hfr ⟨hpos, ws', r, hw', hr', hrec⟩ => ?_
  · step hJ.dot as m₂ hfr₂ ⟨hpos₂, ρ, hρ, hρrel⟩
    step (hS .neg) as m₃ hfr₃ ⟨hpos₃, t, ht, htrel⟩
    step hJ.axpy as m₄ hfr₄ ⟨hpos₄, zs, hzs, hzrel⟩
    exact ⟨by rw [hpos₄, hpos₃, hpos₂, hpos], zs, r ++ [ρ], hzs,
      Store.readBlock_succ_of (by kept) (by kept),
      hrec.step (hρrel.congr (fun i hi => vec_drop_take hi) fun _ _ => rfl) (htrel ▸ hneg ρ)
        (hzrel.congr (fun i hi => vec_drop_take hi) (fun _ _ => rfl) fun _ _ => rfl)⟩
  · step hJ.nrm2 as m₂ hfr₂ ⟨hpos₂, ν, hν, hνrel⟩
    intro s₂ _ hB₂
    exact ⟨by simp [hpos₂, hpos], [ws', r ++ [ν]], Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (Store.readBlock_succ_of (by kept) (by kept)) rfl),
      r, ν, rfl, hrec, hνrel⟩

/-- **The abstract theorem of `mgs`**, from its certificate by the bridge: for every
interpretation meeting the contracts of scalar arithmetic and of the level-1 operations, the run
terminates within `mgsCount n k` calls, and the memory is described by the recurrence with local
errors. -/
theorem runs_mgs_rounded {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ a, dec (M.neg a) = -dec a) (W : Op → List ℕ → ℕ) {τ : Tape K}
    {n k : ℕ} {Q w R : ℕ × ℕ} {μ : Mem K} {qs ws : List K} (hok : ok n) (hQw : Q.1 ≠ w.1)
    (hQR : Q.1 ≠ R.1) (hwR : w.1 ≠ R.1) (hl : μ.Live [Q, w, R])
    (hq : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hw : μ.store.readBlock w.1 w.2 n = some ws) (hwl : w.2 + n ≤ μ.store.len w.1)
    (hR : R.2 + (k + 1) ≤ μ.store.len R.1) :
    Runs J W τ mgs (Env.frame [n, k] [Q, w, w, R]) μ (mgsCount n k) (mgsPeak W n)
      (MgsRounded dec ε n k w R qs ws μ) := by
  refine ((mgs_spec hS hJ hneg).runs_rel W (d := [n, k]) (ins := [Q, w]) (outs := [w, R])
    (τ := τ) (xs := [qs, ws]) rfl ⟨hok, Q, w, R, rfl, rfl, hQw, hQR, hwR⟩
    (by simpa using hl) (by simp [Mem.readBlocks, hq, hw]) trivial
    ⟨hwl, hR, trivial⟩).mono (le_of_eq (staticCost_mgs ..))
    (staticPeak_mgs_le ..) ?_
  rintro μ' ⟨ys, hlen, hb, rfl⟩
  obtain ⟨ws', rν, rfl, h1, h2⟩ := map_length_eq_two hlen
  exact ⟨ws', rν, h1, h2, hb, rfl⟩

variable [Apart Blas1Op ScalarOp Op]

/-- **The concrete corollary**: `mgs` linked through the profile of sequential summation, down to
scalar arithmetic meeting the standard model at the unit roundoff `u`. One application of the
certificate of the profile; the accuracy parameters are those of the profile, the counts are
pushed forward. No proof about the algorithm or its loops. -/
theorem runs_mgs_link_seq {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    (hu : 0 ≤ u) {I : Interp Op Tst K} (hI : IsScalar M I) {τ : Tape K} {n k : ℕ}
    {Q w R : ℕ × ℕ} {μ : Mem K} {qs ws : List K} (hQw : Q.1 ≠ w.1) (hQR : Q.1 ≠ R.1)
    (hwR : w.1 ≠ R.1) (hl : μ.Live [Q, w, R])
    (hq : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hw : μ.store.readBlock w.1 w.2 n = some ws) (hwl : w.2 + n ≤ μ.store.len w.1)
    (hR : R.2 + (k + 1) ≤ μ.store.len R.1) :
    Runs I (Blas.ws 0) τ (mgs.link Blas.seq.table) (Env.frame [n, k] [Q, w, w, R]) μ
      (k • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
          (n - 1) • Blas.sc .add)) + (Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add))) +
        (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
          (n - 1) • Blas.sc .add) + Blas.sc .sqrt)))
      (mgsPeak (Blas.ws 0 : Op → List ℕ → ℕ) n) (MgsRounded dec (Blas.seq.err u) n k w R qs ws μ) :=
  ((Blas.seq_certifies hM hu fun _ => True).runs
    (fun _ hJ => runs_mgs_rounded hJ.1 hJ.2 hM.neg _ trivial hQw hQR hwR hl hq hw hwl hR) hI).mono
    (by count_eval [mgsCount]) le_rfl fun _ h => h

omit [Inhabited K] in
/-- **The scalar counts of the linked `mgs`**, by evaluating the push-forward. -/
theorem push_seq_mgsCount (n k : ℕ) :
    Count.push Blas.seq.cost (mgsCount (Op := Op) (Tst := Tst) n k) =
      k • (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add)) + (Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add))) +
      (n • Blas.sc .mul + (Blas.sc (.lit 0) + ((1 - (1 - n)) • Blas.sc .copy +
        (n - 1) • Blas.sc .add) + Blas.sc .sqrt)) := by
  count_eval [mgsCount]

end NLAlib.Ops.Examples
