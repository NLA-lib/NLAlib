/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Blas

/-!
# Example: a second level, `nrm2` over `dot` and `sqrt`

The signature `NLAlib.Ops.Examples.KOp` adds the norm `nrm2` to the vector level. It is
implemented over the vector level (`NLAlib.Ops.Examples.krylovTable`) by `dot` and `sqrt`, so
that an algorithm over `KOp` is linked twice to reach scalar arithmetic. The contract of `nrm2`
is relational and is proved for its implementation from the contracts of `dot` and `sqrt` alone:
two calls by contract, no arithmetic unfolded.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

variable {K : Type} [Inhabited K]

/-- The norm, and the vector level. -/
inductive KOp where
  /-- `nrm2 [n] [x] [z]`: the Euclidean norm of a block of length `n`, in the cell `z`. -/
  | nrm2
  /-- An operation of the vector level. -/
  | bl (b : BOp)
  deriving DecidableEq

/-- **The relational contract of `nrm2`**: the cell receives a rounded square root (relative
error `εs`) of a sum of squares computed up to the relative error `εd n`. -/
def Nrm2Spec (dec : K → ℝ) (εd : ℕ → ℝ) (εs : ℝ) : Contract K := fun md d ins outs _ =>
  { pre := fun m => ∃ n x z, d = [n] ∧ ins = [x] ∧ outs = [z] ∧ x.1 ≠ z.1 ∧
      md.Needs ((m.store.readBlock x.1 x.2 n).isSome ∧ z.2 < m.store.len z.1)
    post := fun m m' => ∃ n x z xs σ ν, d = [n] ∧ ins = [x] ∧ outs = [z] ∧
      m.store.readBlock x.1 x.2 n = some xs ∧ DotErr dec (εd n) n (vec xs) (vec xs) σ ∧
      (0 ≤ dec σ → |dec ν - √(dec σ)| ≤ εs * √(dec σ)) ∧ m' = m.upd z ν }

/-- **The contracts of the second level.** -/
structure IsKrylov (M : Machine K) (dec : K → ℝ) (εd : ℕ → ℝ) (εa εs : ℝ) (J : Interp KOp K) :
    Prop where
  /-- `nrm2`. -/
  nrm2 : J.Meets .total .nrm2 (Nrm2Spec dec εd εs)
  /-- `dot`. -/
  dot : J.Meets .total (.bl .dot) (DotSpec dec εd)
  /-- `axpy`. -/
  axpy : J.Meets .total (.bl .axpy) (AxpySpec dec εa)
  /-- Scalar operations. -/
  ar : ∀ a, J.IsFn .total (.bl (.ar a)) (M.fn a) anyOperands

/-- **The implementation of `nrm2`** over the vector level: `z := dot x x; z := sqrt z`. Index
variables: `n`, the offsets of `x`, `z`. -/
def nrm2Impl : Impl BOp where
  nd := 1
  nin := 1
  nout := 1
  body := .seq (.call .dot [.var 0] [⟨0, .var 1⟩, ⟨0, .var 1⟩] [⟨1, .var 2⟩])
    (.call (.ar .sqrt) [] [⟨1, .var 2⟩] [⟨1, .var 2⟩])

/-- The implementation of `nrm2` meets its contract, for every interpretation of the vector level
meeting its contracts. Two calls by contract. -/
theorem nrm2Impl_spec {M : Machine K} {dec : K → ℝ} {εd : ℕ → ℝ} {εa u : ℝ} {J : Interp BOp K}
    (hJ : IsBlas M dec εd εa J) (hM : StdModel u dec M) (d : List ℕ) (ins outs : List (ℕ × ℕ))
    (τ : ℕ → K) (m : Mem K) (hpre : (Nrm2Spec dec εd u .total d ins outs τ).pre m) :
    nrm2Impl.Fits d.length ins.length outs.length ∧
      wp .total J τ nrm2Impl.body (Env.frame d (ins ++ outs))
        ((Nrm2Spec dec εd u .total d ins outs τ).post m) m := by
  obtain ⟨n, x, z, rfl, rfl, rfl, hxz, hn⟩ := hpre
  obtain ⟨hx, hz⟩ := hn rfl
  refine ⟨⟨rfl, rfl, rfl⟩, wp_seq (wp_call hJ.dot (d := [n]) (a := [x, x]) (b := [z]) rfl rfl rfl
    ⟨n, x, x, z, rfl, rfl, rfl, hxz, hxz, by simpa using ⟨hx, hz⟩⟩ ?_)⟩
  rintro m₁ ⟨n', x', y', z', xs, ys, σ, hd, hi, ho, hxs, hys, herr, rfl⟩
  cases hd
  cases hi
  cases ho
  obtain rfl : xs = ys := Option.some.inj (hxs.symm.trans hys)
  refine wp_call_un (hJ.ar .sqrt) (x := z) (z := z) rfl rfl rfl trivial (a := σ)
    (Store.get_upd_self hz σ) rfl (by simpa using hz) ?_
  exact ⟨n, x, z, xs, σ, M.sqrt σ, rfl, rfl, rfl, hxs, herr, hM.sqrt σ, by simp [Mem.upd]⟩

/-- **The implementation of the second level over the vector level.** -/
def krylovTable : Table KOp BOp
  | .nrm2 => .inl nrm2Impl
  | .bl b => .inr b

/-- The cost of one call of each operation of the second level, in the vector level. -/
noncomputable def krylovCost : KOp → List ℕ → Count BOp
  | .nrm2, [n] => Count.one .dot [n] + Count.one (.ar .sqrt) []
  | .nrm2, _ => 0
  | .bl b, d => Count.one b d

/-- The workspace of each operation of the second level. -/
def krylovWs : KOp → List ℕ → ℕ
  | .nrm2, _ => 1
  | .bl b, d => blasWs b d

omit [Inhabited K] in
/-- The accounting certificate of the second table, by evaluating static costs. -/
theorem krylov_accounts (J : Interp BOp K) : krylovTable.Accounts J blasWs krylovCost krylovWs := by
  refine Table.accounts_of_static ?_ ?_ J
  · intro o R hT d offs hd ho
    cases o with
    | nrm2 =>
      cases hT
      obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hd
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp ho
      simp [nrm2Impl, staticCost, staticPeak, useCost, krylovCost, krylovWs, blasWs]
    | bl b => cases hT
  · intro o o' hT d
    cases o with
    | nrm2 => cases hT
    | bl b => cases hT; exact ⟨le_rfl, le_rfl⟩

/-- **The induced interpretation meets the contracts of the second level.** -/
theorem isKrylov_link {M : Machine K} {dec : K → ℝ} {εd : ℕ → ℝ} {εa u : ℝ} {J : Interp BOp K}
    (hJ : IsBlas M dec εd εa J) (hM : StdModel u dec M) :
    IsKrylov M dec εd εa u (J.link krylovTable) where
  nrm2 := Interp.link_meets rfl (nrm2Impl_spec hJ hM)
  dot := Interp.link_meets_kept rfl hJ.dot
  axpy := Interp.link_meets_kept rfl hJ.axpy
  ar a := Interp.link_meets_kept rfl (hJ.ar a)

/-- **Witness**: the contracts of the second level can be met, for every `u ≥ 0`. -/
theorem exists_isKrylov {u : ℝ} (hu : 0 ≤ u) :
    ∃ (K : Type) (_ : Inhabited K) (dec : K → ℝ) (M : Machine K) (J : Interp KOp K),
      StdModel u dec M ∧
        IsKrylov M dec (fun n => (1 + u) ^ (2 * n) - 1) (2 * u + u ^ 2) u J :=
  ⟨ℝ, ⟨0⟩, id, exactMachine, ((Interp.ofFns exactMachine.fn).link blasTable).link krylovTable,
    stdModel_exact hu,
    isKrylov_link (isBlas_link (fun o => Interp.ofFns_isFn _ _ o _) (stdModel_exact hu) hu)
      (stdModel_exact hu)⟩

end NLAlib.Ops.Examples
