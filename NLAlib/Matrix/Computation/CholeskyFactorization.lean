/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyColumns
public import NLAlib.Matrix.Computation.SchurUpdate

/-!
# Stored Cholesky factorization

The factorization copies its input into a scoped elimination residual, then constructs one
factor column, explicitly zeros its upper prefix and eliminates one pivot per iteration.
Positive definiteness supplies every
pivot required by the exact execution proof. Source and destination may coincide because the
input copy precedes all output writes.

## Main results

* `NLAlib.Computation.exec_cholesky`: successful exact factorization and its complete frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Compute the Cholesky factor of a packed square matrix: copy the input to a scoped
residual, then form each factor column, explicitly zero its upper prefix and eliminate its
pivot. The input and output may
share a buffer or coincide. Only the output block remains written on return.
[GolubVanLoan2013, §4.2]. -/
def cholesky {P ι VB VI : Type} (p : P) (n : IExp VI) (A : VB) (ao : IExp VI)
    (L : VB) (lo : IExp VI) : Builder P ι VB VI Unit := scope do
  let R ← alloc p (n * n)
  copyv p A ao R 0 (n * n)
  forRange n fun k => do
    choleskyColumnOfResidual p n R L 0 lo (.var k)
    forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
    schurStep p n R 0 (.var k)

/-- The scoped full Cholesky routine composes under any interpretation. -/
theorem executionComposable_cholesky {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (n : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (L : ℕ) (lo : IExp ℕ) : ExecutionComposable I (cholesky p n A ao L lo) :=
  executionComposable_single I (fun _ => rfl)

/-- The actual full Cholesky body's zero-dimensional case succeeds without reading any
matrix or factor cells, under arbitrary word semantics and charges. Buffer handles and offsets
may be invalid because both the initial copy and factor loop have zero length. -/
theorem exec_choleskyBody_of_eval_eq_zero {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (st : St P K C)
    (n : IExp ℕ) (Ab R L : ℕ) (ao lo : IExp ℕ) (hn : n.eval = 0) :
    exec I (do
      copyv p Ab ao R 0 (n * n)
      forRange n fun k => do
        choleskyColumnOfResidual p n R L 0 lo (.var k)
        forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
        schurStep p n R 0 (.var k)).run st = some st := by
  change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop n _) .skip)) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]

variable {P ι : Type} [DecidableEq P]

namespace CholeskyFactorization

/-- Copy a packed matrix into separate writable residual storage, with its complete write frame. -/
theorem exec_copy_residual (I : Interp P ι ℝ (OpCount P ι))
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (Ab R : ℕ) (ao : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : Holds st.store p Ab ao.eval A)
    (hR : Writable st.store p R 0 (n.eval * n.eval))
    (hAR : 0 < n.eval → Ab ≠ R) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (copyv p Ab ao R 0 (n * n)).run st = some out ∧
      st.store.writeBlock p R 0 (flatten A) = some out.store ∧
      Holds out.store p R 0 A := by
  let xs : ℕ → ℝ := fun t => if h : t % n.eval < n.eval ∧ t / n.eval < n.eval then
    A ⟨t % n.eval, h.1⟩ ⟨t / n.eval, h.2⟩ else 0
  have hread : ∀ t < (n * n).eval, st.store.read p Ab (ao.eval + t) = some (xs t) := by
    intro t ht
    have hN : 0 < n.eval := by change t < n.eval * n.eval at ht; nlinarith
    have hi := Nat.mod_lt t hN
    have hj := (Nat.div_lt_iff_lt_mul hN).mpr (show t < n.eval * n.eval from ht)
    have hboth : t % n.eval < n.eval ∧ t / n.eval < n.eval := ⟨hi, hj⟩
    simpa only [xs, dif_pos hboth, Nat.add_assoc, Nat.mod_add_div] using
      hA ⟨t % n.eval, hi⟩ ⟨t / n.eval, hj⟩
  obtain ⟨s', hw⟩ := Writable.exists_writeBlock (y := flatten A)
    (by simpa only [size_flatten] using hR)
  obtain ⟨out, hr, hs, _⟩ := exec_copyv I hc p st Ab ao R 0 (n * n) xs hread
    (fun he i hi _ _ _ => (hAR (by change i < n.eval * n.eval at hi; nlinarith) he).elim)
    s' (by simpa only [flatten, xs, IExp.eval_mul, IExp.eval_zero] using hw)
  refine ⟨out, hr, ?_, fun i j => ?_⟩
  · rw [hs]
    exact hw
  · rw [hs]
    simpa only [Nat.add_assoc] using
      (Store.read_of_writeBlock_eq_some_of_lt hw
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
        (getElem?_flatten A i j)

/-- Writing a computed factor column preserves the full residual/output block frame. -/
theorem frame_column {base s s' : Store P ℝ} {p : P} {R L lo N k : ℕ}
    {g : ℕ → Option ℝ} (A : Matrix (Fin N) (Fin N) ℝ) (hk : k < N)
    (h : Store.BlockFrame base p R L lo (N * N) s g)
    (hw : s.writeBlock p L (lo + N * k)
      (Array.ofFn fun i => choleskyLower A i ⟨k, hk⟩) = some s') :
    ∃ g', Store.BlockFrame base p R L lo (N * N) s' g' := by
  refine ⟨_, h.writeBlock hw ?_⟩
  simp only [Array.size_ofFn]
  have hm := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hk)
  nlinarith

/-- Writing the next computed factor column extends the already stored column prefix. -/
theorem read_column {s s' : Store P ℝ} {p : P} {L lo N k : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hk : k < N)
    (h : ∀ i j : Fin N, (j : ℕ) < k →
      s.read p L (lo + i + N * j) = some (choleskyLower A i j))
    (hw : s.writeBlock p L (lo + N * k)
      (Array.ofFn fun i => choleskyLower A i ⟨k, hk⟩) = some s') :
    ∀ i j : Fin N, (j : ℕ) < k + 1 →
      s'.read p L (lo + i + N * j) = some (choleskyLower A i j) := by
  intro i j hj
  by_cases hjk : (j : ℕ) = k
  · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hjk
    have hr := Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hw
      (by simpa only [Array.size_ofFn] using i.isLt)
    simpa only [Array.getElem?_ofFn, i.isLt, dite_true, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hr
  · have hj' : (j : ℕ) < k := by omega
    have hi := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt hj'
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inr (Or.inl (by omega))),
      h i j hj']

private theorem frame_flatten {s₀ sF : Store P ℝ} {p : P} {R L off N : ℕ}
    {g : ℕ → Option ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (h : Store.BlockFrame s₀ p R L off (N * N) sF g)
    (hA : Holds sF p L off A) :
    ∀ m < N * N, g m = (flatten A)[m]? := by
  intro m hm
  have hN : 0 < N := by nlinarith
  let i : Fin N := ⟨m % N, Nat.mod_lt _ hN⟩
  let j : Fin N := ⟨m / N, (Nat.div_lt_iff_lt_mul hN).mpr hm⟩
  have he : (i : ℕ) + N * j = m := Nat.mod_add_div m N
  calc
    g m = sF.read p L (off + m) := (h.2.2 m hm).symm
    _ = some (A i j) := by simpa only [Nat.add_assoc, he] using hA i j
    _ = (flatten A)[m]? := by simpa only [he] using (getElem?_flatten A i j).symm

/-- Release residual scratch and identify the sole remaining full factor write. -/
theorem writeBlock_flatten_of_pop_frame {s₀ sF : Store P ℝ} {p : P} {L off N : ℕ}
    {g : ℕ → Option ℝ} {A : Matrix (Fin N) (Fin N) ℝ} {scratch : Array (Option ℝ)}
    (h : Store.BlockFrame (s₀.push (p, scratch)) p s₀.size L off (N * N) sF g)
    (hA : Holds sF p L off A) (hw : Writable s₀ p L off (N * N)) :
    s₀.writeBlock p L off (flatten A) = some sF.pop := by
  obtain ⟨out, hout⟩ := Writable.exists_writeBlock (y := flatten A)
    (by simpa only [size_flatten] using hw)
  have hp := h.pop_eq hout (size_flatten A) (frame_flatten h hA)
  rw [hp]
  exact hout

end CholeskyFactorization

open CholeskyFactorization

/-- Residual/output frame, exact elimination residual and stored computed-column prefix. -/
def CholeskyFactorization.FactorState (base : Store P ℝ) (p : P) (R L lo : ℕ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (s : Store P ℝ) : Prop :=
  (∃ g, Store.BlockFrame base p R L lo (N * N) s g) ∧
    Holds s p R 0 (gaussState A k) ∧
    ∀ i j : Fin N, (j : ℕ) < k →
      s.read p L (lo + i + N * j) = some (choleskyLower A i j)

private theorem exec_iteration (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (base : Store P ℝ)
    (n : IExp ℕ) (R L : ℕ) (lo : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosDef) (hRL : R ≠ L) (hL : Writable base p L lo.eval (n.eval * n.eval))
    (k : ℕ) (hk : k < n.eval) (st : St P ℝ (OpCount P ι))
    (hInv : FactorState base p R L lo.eval A k st.store) :
    ∃ out, exec I (do
      choleskyColumnOfResidual p n R L 0 lo (.var k)
      forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
      schurStep p n R 0 (.var k)).run st = some out ∧
      FactorState base p R L lo.eval A (k + 1) out.store := by
  obtain ⟨⟨g, hF⟩, hR, hprefix⟩ := hInv
  have hcap : Writable st.store p L (lo.eval + n.eval * k) n.eval := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hL (i + n.eval * k)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hF.1 ▸ hlen, by omega⟩
  obtain ⟨s₁, hr₁, hw₁⟩ := exec_choleskyColumnOfResidual_of_posDef I hI hc p st n R L
    0 lo (.var k) A hA hk hR hRL hcap
  have hR₁ : Holds s₁.store p R 0 (gaussState A k) := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hRL)).trans (hR i j)
  obtain ⟨g', hF₁⟩ := frame_column A hk hF hw₁
  have hprefix₁ := read_column A hk hprefix hw₁
  have hcap₁ := hcap.of_shape_eq (Store.shape_of_writeBlock_eq_some hw₁)
  obtain ⟨cleared, hclear, hstore⟩ := exec_forRange_zero_of_reads_eq_zero I p 0
    (by rw [hI]; simp only [exactSem, Rat.cast_zero]) s₁ (.var k) L
    (lo + n * .var k) (fun i hi => by
      change i < k at hi
      simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using hcap₁ i (by omega))
    (fun i hi => by
      change i < k at hi
      have hread := hprefix₁ ⟨i, by omega⟩ ⟨k, hk⟩ (Nat.lt_succ_self k)
      have hz : choleskyLower A ⟨i, by omega⟩ ⟨k, hk⟩ = 0 :=
        isLowerTriangular_choleskyLower A (by exact hi)
      simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var, hz, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hread)
  have hFc : Store.BlockFrame base p R L lo.eval (n.eval * n.eval) cleared.store g' :=
    hstore.symm ▸ hF₁
  obtain ⟨out, hr₂, hw₂, hR₂⟩ := exec_schurStep I hI hc p cleared n R 0 (.var k)
    (gaussState A k) hk (hstore.symm ▸ hR₁) (hA.gaussState_apply_self_pos ⟨k, hk⟩).ne'
  refine ⟨out, ?_, ⟨g', hFc.writeBlock_scratch (fun _ => hRL.symm) hw₂⟩, ?_, ?_⟩
  · rw [exec_run_bind I
      (b := choleskyColumnOfResidual p n R L 0 lo (.var k)) (fun _ => rfl),
      hr₁, Option.bind_some, exec_run_bind I
        (b := forRange (IExp.var k) fun i =>
          ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0))
        (fun _ => rfl), hclear, Option.bind_some]
    exact hr₂
  · rw [gaussState_succ A hk]
    exact hR₂
  · intro i j hj
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRL.symm), hstore,
      hprefix₁ i j hj]

private theorem exists_exec_cholesky_of_push (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (initial : Store P ℝ)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosDef)
    (hinput : Holds initial p Ab ao.eval A)
    (hL : Writable initial p L lo.eval (n.eval * n.eval))
    (hst : st.store = initial.push (p, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv p Ab ao initial.size 0 (n * n)
      forRange n fun k => do
        choleskyColumnOfResidual p n initial.size L 0 lo (.var k)
        forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
        schurStep p n initial.size 0 (.var k)).run st = some out ∧
      initial.writeBlock p L lo.eval (flatten (choleskyLower A)) = some out.store.pop := by
  have hLb : 0 < n.eval * n.eval → L < initial.size := by
    intro hn
    obtain ⟨len, hlen, _⟩ := hL 0 hn
    have := (Array.getElem?_eq_some_iff.mp hlen).1
    simpa only [Store.size_shape] using this
  have hAb : 0 < n.eval → Ab < initial.size := fun hn =>
    Store.lt_size_of_read_eq_some (hinput ⟨0, hn⟩ ⟨0, hn⟩)
  have hinput' : Holds st.store p Ab ao.eval A := fun i j => by
    rw [hst, Store.read_push_of_lt (hAb (Nat.zero_lt_of_lt i.isLt))]
    exact hinput i j
  have hR : Writable st.store p initial.size 0 (n.eval * n.eval) := by
    intro i hi
    exact ⟨n.eval * n.eval, by rw [hst]; exact
      Store.getElem?_shape_push_size initial p (n.eval * n.eval), by omega⟩
  have hL' : Writable st.store p L lo.eval (n.eval * n.eval) := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hL i hi
    refine ⟨len, ?_, hlt⟩
    rw [hst, Store.getElem?_shape_push_of_lt _ (hLb (by omega))]
    exact hlen
  obtain ⟨s₁, hr₁, hw₁, hR₁⟩ := exec_copy_residual I hc p st n Ab initial.size ao A
    hinput' hR (fun hn => Nat.ne_of_lt (hAb hn))
  have hF : Store.BlockFrame st.store p initial.size L lo.eval (n.eval * n.eval) st.store
      (fun i => st.store.read p L (lo.eval + i)) :=
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hInv : FactorState st.store p initial.size L lo.eval A 0 s₁.store :=
    ⟨⟨_, hF.writeBlock_scratch (fun hn => Nat.ne_of_lt (hLb hn)) hw₁⟩,
      hR₁, fun _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  obtain ⟨out, hr₂, ⟨g, hFout⟩, _, hprefix⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k σ => FactorState st.store p initial.size L lo.eval A k σ.store) hInv
    (fun k hk σ hσ => exec_iteration I hI hc p st.store n initial.size L lo A hA
      (Nat.ne_of_gt (hLb (Nat.mul_pos (by omega) (by omega)))) hL' k hk σ hσ)
  have hfinal : Holds out.store p L lo.eval (choleskyLower A) := fun i j =>
    hprefix i j j.isLt
  refine ⟨out, ?_, writeBlock_flatten_of_pop_frame (hst ▸ hFout) hfinal hL⟩
  rw [exec_run_bind I (b := copyv p Ab ao initial.size 0 (n * n)) (fun _ => rfl),
    hr₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) s₁ = some out
  rw [exec_seq_skip]
  exact hr₂

/-- Under exact real arithmetic, readable positive definite input and a writable factor block
suffice for the full Cholesky routine to succeed. Its final store is exactly the original store
with the full lower triangular factor written at the output offset. The input and output may
coincide or overlap: the routine first copies the input into scoped scratch. Empty matrices
require no valid matrix or factor buffer handle. The stored factor satisfies the exact
Cholesky predicate. [GolubVanLoan2013, §4.2]. -/
theorem exec_cholesky (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (Ab L : ℕ) (ao lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosDef)
    (hinput : Holds st.store p Ab ao.eval A)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval)) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (cholesky p n Ab ao L lo).run st = some out ∧
      st.store.writeBlock p L lo.eval (flatten (choleskyLower A)) = some out.store ∧
      Holds out.store p L lo.eval (choleskyLower A) ∧
      IsCholesky A (choleskyLower A) := by
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I p (n * n)
    (fun R => (do
      copyv p Ab ao R 0 (n * n)
      forRange n fun k => do
        choleskyColumnOfResidual p n R L 0 lo (.var k)
        forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
        schurStep p n R 0 (.var k)).run) st
    (fun s => st.store.writeBlock p L lo.eval (flatten (choleskyLower A)) = some s)
    (fun σ hσ => exists_exec_cholesky_of_push I hI hc p st.store σ n Ab L ao lo A hA hinput hL hσ)
  refine ⟨out, ?_, hw, ?_, hA.isCholesky_choleskyLower⟩
  · change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    simpa only [Nat.add_assoc] using
      (Store.read_of_writeBlock_eq_some_of_lt hw
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
        (getElem?_flatten (choleskyLower A) i j)

end NLAlib.Computation
