/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQ
public import NLAlib.Matrix.Computation.PLUFrames

/-!
# Stored rook and threshold LU factorizations

These actual builders specialize the single exact two-index factorization engine. Rook
pivoting chooses mutual active row/column maxima. Threshold partial pivoting keeps the
current column and accepts a qualifying diagonal, preserving equality. The row-only wrapper
scopes the actual identity column log. Singular matrices use the same zero-safe kernels.

## Main definitions

* `NLAlib.Computation.rookPluqFactor`: actual rook-pivoted LU with two logs.
* `NLAlib.Computation.thresholdPluqFactor`: threshold LU with an actual identity column log.
* `NLAlib.Computation.thresholdPluFactor`: threshold LU exposing only its row log.

## Main results

* `NLAlib.Computation.executionComposable_rookPluqFactor`: scoped rook factorization.
* `NLAlib.Computation.executionComposable_thresholdPluqFactor`: scoped threshold factorization.
* `NLAlib.Computation.executionComposable_thresholdPluFactor`: scoped row-only factorization.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Factor a square matrix by actual rook selection, exchanging residual/lower rows and
residual/upper columns before each total elimination step. Both absolute logs are outputs. -/
def rookPluqFactor {P ι VB VI : Type} (tag : P) (n : IExp VI) (A L U Hr Hc : VB)
    (ao lo uo hro hco : IExp VI) : Builder P ι VB VI Unit :=
  pivotedLUFactor tag (rookPivotChoice tag) n A L U Hr Hc ao lo uo hro hco

/-- Factor using the exact rational threshold for row selection and the current column
literal at every step. The actual column log therefore records identity exchanges. -/
def thresholdPluqFactor {P ι VB VI : Type} (tag : P) (τ : ℚ) (n : IExp VI) (A L U Hr Hc : VB)
    (ao lo uo hro hco : IExp VI) : Builder P ι VB VI Unit :=
  pivotedLUFactor tag (fun m k S off rowIndex colIndex => do
    thresholdPivotChoice tag m k S off τ rowIndex
    ins (.litIdx tag colIndex k)) n A L U Hr Hc ao lo uo hro hco

/-- Expose threshold partial pivoting with only its two factors and actual row log. The
identity column log is really computed in a scoped buffer and then released. -/
def thresholdPluFactor {P ι VB VI : Type} (tag : P) (τ : ℚ) (n : IExp VI) (A L U H : VB)
    (ao lo uo ho : IExp VI) : Builder P ι VB VI Unit := scope do
  let Hc ← alloc tag n
  thresholdPluqFactor tag τ n A L U H Hc ao lo uo ho 0

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Rook factorization releases its residual and selector scratch before continuation. -/
theorem executionComposable_rookPluqFactor (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ) :
    ExecutionComposable I (rookPluqFactor tag n A L U Hr Hc ao lo uo hro hco) :=
  executionComposable_pivotedLUFactor I tag _ n A L U Hr Hc ao lo uo hro hco

/-- Threshold factorization releases its residual and selector scratch before continuation. -/
theorem executionComposable_thresholdPluqFactor (I : Interp P ι K C) (tag : P) (τ : ℚ)
    (n : IExp ℕ) (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ) :
    ExecutionComposable I (thresholdPluqFactor tag τ n A L U Hr Hc ao lo uo hro hco) :=
  executionComposable_pivotedLUFactor I tag _ n A L U Hr Hc ao lo uo hro hco

/-- The row-only threshold wrapper also releases its identity column log. -/
theorem executionComposable_thresholdPluFactor (I : Interp P ι K C) (tag : P) (τ : ℚ)
    (n : IExp ℕ) (A L U H : ℕ) (ao lo uo ho : IExp ℕ) :
    ExecutionComposable I (thresholdPluFactor tag τ n A L U H ao lo uo ho) :=
  executionComposable_single I (fun _ => rfl)

namespace ThresholdLU

private def Result {N : ℕ} (initial : Store P ℝ) (tag : P)
    (M : Matrix (Fin N) (Fin N) ℝ) (τ : ℚ) (A L U H ao lo uo ho : ℕ)
    (final : Store P ℝ) : Prop :=
  ∃ p : Fin N → Fin N,
    initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (H, ho, N)]
      [flatten (luLower (M.submatrix (luPivotPermutation p N) id)),
        flatten (luUpper (M.submatrix (luPivotPermutation p N) id)),
        Array.ofFn (fun j => ((p j).val : ℝ))] = some final ∧ (∀ j, j ≤ p j) ∧
    IsLU (M.submatrix (luPivotPermutation p N) id)
      (luLower (M.submatrix (luPivotPermutation p N) id))
      (luUpper (M.submatrix (luPivotPermutation p N) id)) ∧
    (∀ i j, |luLower (M.submatrix (luPivotPermutation p N) id) i j| ≤ (τ : ℝ)⁻¹) ∧
    Holds final tag L lo (luLower (M.submatrix (luPivotPermutation p N) id)) ∧
    Holds final tag U uo (luUpper (M.submatrix (luPivotPermutation p N) id)) ∧
    (∀ j : Fin N, final.read tag H (ho + j) = some ((p j).val : ℝ)) ∧
    Holds final tag A ao M

private theorem exec_empty (I : Interp P ι ℝ C) (tag : P) (initial : Store P ℝ)
    (st : St P ℝ C) (n : IExp ℕ) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (τ : ℚ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hn : n.eval = 0)
    (hM : Holds initial tag A ao.eval M)
    (hstore : st.store = initial.push (tag, Array.replicate n.eval none)) :
    ∃ out, exec I (thresholdPluqFactor tag τ n A L U H initial.size ao lo uo ho 0).run st =
      some out ∧ Result initial tag M τ A L U H ao.eval lo.eval uo.eval ho.eval out.store.pop := by
  obtain ⟨out, he, hs⟩ := exec_pivotedLUFactor_of_zero I tag _ st n A L U H initial.size
    ao lo uo ho 0 hn
  have hpop : out.store.pop = initial := by rw [hs, hstore]; exact Array.pop_push
  have hfin : ∀ j : Fin n.eval, False := fun j => by have := j.isLt; omega
  let B := M.submatrix (luPivotPermutation (id : Fin n.eval → Fin n.eval) n.eval) id
  have hLe : flatten (luLower B) = #[] := Array.eq_empty_of_size_eq_zero
    (by simp only [size_flatten, hn, zero_mul])
  have hUe : flatten (luUpper B) = #[] := Array.eq_empty_of_size_eq_zero
    (by simp only [size_flatten, hn, zero_mul])
  have hHe : Array.ofFn (fun j : Fin n.eval => ((id j).val : ℝ)) = #[] :=
    Array.eq_empty_of_size_eq_zero (by rw [Array.size_ofFn, hn])
  refine ⟨out, he, ?_⟩
  dsimp only [Result]
  rw [hpop]
  refine ⟨id, ?_, (fun j => (hfin j).elim), ?_, (fun i => (hfin i).elim),
    (fun i => (hfin i).elim), (fun i => (hfin i).elim), (fun j => (hfin j).elim), hM⟩
  · change initial.writeBlocks tag _ [flatten (luLower B), flatten (luUpper B), _] = _
    simp only [hLe, hUe, hHe, hn, zero_mul, Store.writeBlocks, Array.size_empty,
      ↓reduceIte, Store.writeBlock, List.range_zero, List.foldlM_nil, Option.pure_def,
      Option.bind_some]
  · exact isLU_luLower_luUpper_of_forall_eq_zero (fun j => (hfin j).elim)

private theorem writeBlocks_pop_three {𝕜 : Type} [RCLike 𝕜] {N : ℕ}
    {initial final : Store P 𝕜} {tag : P} {L U H lo uo ho : ℕ}
    (F G : Matrix (Fin N) (Fin N) 𝕜) (history : Fin N → 𝕜) (lastWords : Array 𝕜)
    (hw : Store.writeBlocks (initial.push (tag, Array.replicate N none)) tag
      [(L, lo, N * N), (U, uo, N * N), (H, ho, N), (initial.size, 0, N)]
      [flatten F, flatten G, Array.ofFn history, lastWords] = some final)
    (hF : Holds final tag L lo F) (hG : Holds final tag U uo G)
    (hH : ∀ j : Fin N, final.read tag H (ho + j) = some (history j))
    (hLcap : Writable initial tag L lo (N * N)) (hUcap : Writable initial tag U uo (N * N))
    (hHcap : Writable initial tag H ho N) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H) :
    initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (H, ho, N)]
      [flatten F, flatten G, Array.ofFn history] = some final.pop ∧
      Holds final.pop tag L lo F ∧ Holds final.pop tag U uo G ∧
      (∀ j : Fin N, Store.read final.pop tag H (ho + j) = some (history j)) := by
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using
      congrArg Array.size (Store.shape_of_writeBlocks_eq_some hw)
  have hLb : 0 < N → L < initial.size := fun hn => hLcap.lt_size (Nat.mul_pos hn hn)
  have hUb : 0 < N → U < initial.size := fun hn => hUcap.lt_size (Nat.mul_pos hn hn)
  have hHb : 0 < N → H < initial.size := fun hn => hHcap.lt_size hn
  have hFp : Holds final.pop tag L lo F := by
    intro i j
    rw [Store.read_pop_of_lt (by have := hLb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hF i j
  have hGp : Holds final.pop tag U uo G := by
    intro i j
    rw [Store.read_pop_of_lt (by have := hUb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hG i j
  have hHp : ∀ j : Fin N, Store.read final.pop tag H (ho + j) = some (history j) := by
    intro j
    rw [Store.read_pop_of_lt (by have := hHb (Nat.zero_lt_of_lt j.isLt); omega)]
    exact hH j
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, Store.shape_of_writeBlocks_eq_some hw]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  refine ⟨PLU.writeBlocks_factors_history F G history hLU hLH hUH hshape hFp hGp hHp ?_,
    hFp, hGp, hHp⟩
  intro q b i houtL houtU houtH
  by_cases hb : b < initial.size
  · rw [Store.read_pop_of_lt (by omega), Store.read_of_writeBlocks_eq_some_of_forall hw ?_,
      Store.read_push_of_lt hb]
    intro block hblock
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
    rcases hblock with rfl | rfl | rfl | rfl
    · exact houtL
    · exact houtU
    · exact houtH
    · exact Or.inl (by omega)
  · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
      Store.read_eq_none_of_size_le (by omega)]

end ThresholdLU

/-- Actual rook-pivoted LU succeeds on every square real input, including singular and empty
matrices. Both actual logs decode the row/column permutations in its exact factorization;
lower entries have magnitude at most one and the original four-output frame is retained. -/
theorem exec_rookPluqFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U Hr Hc : ℕ)
    (ao lo uo hro hco : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U)
    (hAR : 0 < n.eval → A ≠ Hr) (hAC : 0 < n.eval → A ≠ Hc) :
    ∃ (out : St P ℝ (OpCount P ι)) (p q : Fin n.eval → Fin n.eval),
      exec I (rookPluqFactor tag n A L U Hr Hc ao lo uo hro hco).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval)
          (luPivotPermutation q n.eval))),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval)
            (luPivotPermutation q n.eval))),
          Array.ofFn (fun j => ((p j).val : ℝ)), Array.ofFn (fun j => ((q j).val : ℝ))] =
            some out.store ∧ (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval)))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval)
        (luPivotPermutation q n.eval)) i j| ≤ 1) ∧
      Holds out.store tag L lo.eval
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      Holds out.store tag U uo.eval
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ j : Fin n.eval, out.store.read tag Hr (hro.eval + j) = some ((p j).val : ℝ)) ∧
      (∀ j : Fin n.eval, out.store.read tag Hc (hco.eval + j) = some ((q j).val : ℝ)) ∧
      Holds out.store tag A ao.eval M := by
  obtain ⟨out, p, q, he, hw, hp, hq, hf, hm, hLf, hUf, hr, hc', -, hMS⟩ :=
    exec_pivotedLUFactor I hI hc tag (rookPivotChoice tag)
      (isPivotChoiceRoutine_rookPivotChoice I hI tag) st n A L U Hr Hc ao lo uo hro hco M
      hM hL hU hR hC hLU hLR hLC hUR hUC hRC hAL hAU hAR hAC
  refine ⟨out, p, q, he, hw, hp, hq, hf, ?_, hLf, hUf, hr, hc', hMS⟩
  simpa only [inv_one] using hm

/-- Actual threshold LU succeeds for every real input with a positive rational threshold at
most one. Its two actual logs include an identity column log, lower entries are bounded by
reciprocal threshold, and its exact original four-output frame admits singular and empty inputs. -/
theorem exec_thresholdPluqFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U Hr Hc : ℕ)
    (ao lo uo hro hco : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U)
    (hAR : 0 < n.eval → A ≠ Hr) (hAC : 0 < n.eval → A ≠ Hc) :
    ∃ (out : St P ℝ (OpCount P ι)) (p q : Fin n.eval → Fin n.eval),
      exec I (thresholdPluqFactor tag τ n A L U Hr Hc ao lo uo hro hco).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval)
          (luPivotPermutation q n.eval))),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval)
            (luPivotPermutation q n.eval))),
          Array.ofFn (fun j => ((p j).val : ℝ)), Array.ofFn (fun j => ((q j).val : ℝ))] =
            some out.store ∧ (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval)))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval)
        (luPivotPermutation q n.eval)) i j| ≤ (τ : ℝ)⁻¹) ∧
      Holds out.store tag L lo.eval
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      Holds out.store tag U uo.eval
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ j : Fin n.eval, out.store.read tag Hr (hro.eval + j) = some ((p j).val : ℝ)) ∧
      (∀ j : Fin n.eval, out.store.read tag Hc (hco.eval + j) = some ((q j).val : ℝ)) ∧
      (∀ j, q j = j) ∧ Holds out.store tag A ao.eval M := by
  obtain ⟨out, p, q, he, hw, hp, hq, hf, hm, hLf, hUf, hr, hc', hfixed, hMS⟩ :=
    exec_pivotedLUFactor I hI hc tag _
      (isPivotChoiceRoutine_thresholdPivotChoice I hI tag τ hτ₀ hτ₁)
      st n A L U Hr Hc ao lo uo hro hco M
      hM hL hU hR hC hLU hLR hLC hUR hUC hRC hAL hAU hAR hAC
  exact ⟨out, p, q, he, hw, hp, hq, hf, hm, hLf, hUf, hr, hc', hfixed rfl, hMS⟩

namespace ThresholdLU

private theorem exec_nonempty (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hn : 0 < n.eval)
    (hM : Holds initial tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hH : Writable initial tag H ho.eval n.eval)
    (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAH : 0 < n.eval → A ≠ H)
    (hstore : st.store = initial.push (tag, Array.replicate n.eval none)) :
    ∃ out, exec I (thresholdPluqFactor tag τ n A L U H initial.size ao lo uo ho 0).run st =
      some out ∧ Result initial tag M τ A L U H ao.eval lo.eval uo.eval ho.eval out.store.pop := by
  have hAb := Store.lt_size_of_read_eq_some (hM ⟨0, hn⟩ ⟨0, hn⟩)
  have hLb := hL.lt_size (Nat.mul_pos hn hn)
  have hUb := hU.lt_size (Nat.mul_pos hn hn)
  have hHb := hH.lt_size hn
  have hMst : Holds st.store tag A ao.eval M := by
    intro i j
    rw [hstore, Store.read_push_of_lt hAb]
    exact hM i j
  have hC : Writable st.store tag initial.size 0 n.eval := by
    rw [hstore]
    intro i hi
    exact ⟨n.eval, Store.getElem?_shape_push_size _ _ _, by omega⟩
  obtain ⟨out, p, q, he, hw, hp, -, hf, hm, hLf, hUf, hrow, -, hfixed, hMS⟩ :=
    exec_thresholdPluqFactor I hI hc tag τ hτ₀ hτ₁ st n A L U H initial.size ao lo uo ho 0 M
      hMst (hstore ▸ hL.push _) (hstore ▸ hU.push _) (hstore ▸ hH.push _) hC
      hLU hLH (Nat.ne_of_lt hLb) hUH (Nat.ne_of_lt hUb) (Nat.ne_of_lt hHb)
      hAL hAU hAH (fun _ => Nat.ne_of_lt hAb)
  have hqid : q = id := funext hfixed
  have hperm : luPivotPermutation q n.eval = Equiv.refl _ := by simp [hqid, luPivotPermutation]
  have hB : M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval) =
      M.submatrix (luPivotPermutation p n.eval) id := by rw [hperm]; rfl
  rw [hB] at hw hf hm hLf hUf
  rw [hstore] at hw
  obtain ⟨hw', hLf', hUf', hrow'⟩ := writeBlocks_pop_three _ _ _
    (Array.ofFn (fun j => ((q j).val : ℝ))) hw hLf hUf hrow
    hL hU hH hLU hLH hUH
  have hsize : out.store.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using
      congrArg Array.size (Store.shape_of_writeBlocks_eq_some hw)
  refine ⟨out, he, p, hw', hp, hf, hm, hLf', hUf', hrow', ?_⟩
  intro i j
  rw [Store.read_pop_of_lt (by omega)]
  exact hMS i j

private theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds initial tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hH : Writable initial tag H ho.eval n.eval)
    (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAH : 0 < n.eval → A ≠ H)
    (hstore : st.store = initial.push (tag, Array.replicate n.eval none)) :
    ∃ out, exec I (thresholdPluqFactor tag τ n A L U H initial.size ao lo uo ho 0).run st =
      some out ∧ Result initial tag M τ A L U H ao.eval lo.eval uo.eval ho.eval out.store.pop := by
  by_cases hn : n.eval = 0
  · exact exec_empty I tag initial st n A L U H ao lo uo ho τ M hn hM hstore
  · exact exec_nonempty I hI hc tag initial st n τ hτ₀ hτ₁ A L U H ao lo uo ho M
      (Nat.pos_of_ne_zero hn) hM hL hU hH hLU hLH hUH hAL hAU hAH hstore

end ThresholdLU

/-- Actual threshold partial pivoting succeeds with only lower/upper factors and its actual
row log as outputs. The computed identity column log is scoped. Exact semantics and a positive
rational threshold at most one suffice for all inputs, including singular and empty matrices.
Only the original three blocks change, lower entries are bounded by reciprocal threshold,
and empty inputs permit invalid handles even when one equals the scoped log handle. -/
theorem exec_thresholdPluFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hH : Writable st.store tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAH : 0 < n.eval → A ≠ H) :
    ∃ (out : St P ℝ (OpCount P ι)) (p : Fin n.eval → Fin n.eval),
      exec I (thresholdPluFactor tag τ n A L U H ao lo uo ho).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (H, ho.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval) id)),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval) id)),
          Array.ofFn (fun j => ((p j).val : ℝ))] = some out.store ∧
      (∀ j, j ≤ p j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) id)
        (luLower (M.submatrix (luPivotPermutation p n.eval) id))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval) id) i j| ≤ (τ : ℝ)⁻¹) ∧
      Holds out.store tag L lo.eval (luLower (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      Holds out.store tag U uo.eval (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      (∀ j : Fin n.eval, out.store.read tag H (ho.eval + j) = some ((p j).val : ℝ)) ∧
      Holds out.store tag A ao.eval M := by
  let Q := ThresholdLU.Result st.store tag M τ A L U H ao.eval lo.eval uo.eval ho.eval
  obtain ⟨out, he, p, hw, hp, hf, hm, hLf, hUf, hlog, hMS⟩ := exists_exec_alloc I tag n
    (fun Hc => (thresholdPluqFactor tag τ n A L U H Hc ao lo uo ho 0).run) st Q
    (fun σ hσ => ThresholdLU.exec_body I hI hc tag st.store σ n τ hτ₀ hτ₁ A L U H
      ao lo uo ho M hM hL hU hH hLU hLH hUH hAL hAU hAH hσ)
  refine ⟨out, p, ?_, hw, hp, hf, hm, hLf, hUf, hlog, hMS⟩
  change exec I (.seq (.alloc tag n _) .skip) st = some out
  rw [exec_seq_skip]
  exact he

end NLAlib.Computation
