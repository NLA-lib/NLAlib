/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.Contract
public import NLAlib.Computation.RoutineFrames

/-!
# Rounded execution of the rank-one update

The actual `ger` program first multiplies the coefficient by each conjugated right-vector
entry, then forms each left-vector product and adds it to the original matrix entry.
The theorem records these three rounded operations separately and proves successful execution
and the complete matrix block frame. Arithmetic charges are arbitrary.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_ger`: actual success, matrix write and local error witnesses.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

namespace RankOneRounding

private structure GerCtx (I : Interp P ι K C) (s₀ : Store P K) (p : P)
    (T A x y : ℕ) (a : Cell ℕ ℕ) (m n ao xo yo : ℕ) (av : K)
    (xv yv : ℕ → K) (M : ℕ → ℕ → K) (cy tv : ℕ → K) (qv zv : ℕ → ℕ → K) : Prop where
  scratch : s₀.shape[T]? = some (p, 2)
  A_ne : 0 < m * n → A ≠ T
  A_shape : ∀ k < m * n, ∃ l, s₀.shape[A]? = some (p, l) ∧ ao + k < l
  a_read : 0 < n → s₀.read p a.buf a.idx.eval = some av
  a_out : 0 < n → a.buf ≠ T ∧
    ¬(p = p ∧ a.buf = A ∧ ao ≤ a.idx.eval ∧ a.idx.eval < ao + m * n)
  x_read : 0 < n → ∀ i < m, s₀.read p x (xo + i) = some (xv i)
  x_out : 0 < n → ∀ i < m, x ≠ T ∧
    ¬(p = p ∧ x = A ∧ ao ≤ xo + i ∧ xo + i < ao + m * n)
  y_read : ∀ j < n, s₀.read p y (yo + j) = some (yv j)
  y_out : ∀ j < n, y ≠ T ∧
    ¬(p = p ∧ y = A ∧ ao ≤ yo + j ∧ yo + j < ao + m * n)
  conj : ∀ j < n, I.sem.un p .conj (yv j) = some (cy j)
  col_mul : ∀ j < n, I.sem.bin p .mul av (cy j) = some (tv j)
  cell_mul : ∀ i < m, ∀ j < n, I.sem.bin p .mul (xv i) (tv j) = some (qv i j)
  cell_add : ∀ i < m, ∀ j < n, I.sem.bin p .add (M i j) (qv i j) = some (zv i j)

variable {I : Interp P ι K C} {s₀ : Store P K} {p : P} {T A x y : ℕ}
  {m n ao xo yo : IExp ℕ} {a : Cell ℕ ℕ} {av : K} {xv yv cy tv : ℕ → K}
  {M qv zv : ℕ → ℕ → K}

private theorem exec_gerStep
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv M cy tv qv zv)
    {σ : St P K C} {g : ℕ → Option K} {i j : ℕ} (hi : i < m.eval)
    (hj : j < n.eval) (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (ht : σ.store.read p T 0 = some (tv j)) (hw : g (i + m.eval * j) = some (M i j)) :
    ∃ s', exec I (.seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
        (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩
          ⟨T, 1⟩)) .skip)) σ = some { σ with store := s', cnt := σ.cnt +
            (I.charge (.bin p .mul) + I.charge (.bin p .add)) } ∧
      Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s'
        (Function.update g (i + m.eval * j) (some (zv i j))) ∧
      s'.read p T 0 = some (tv j) := by
  have hk : i + m.eval * j < m.eval * n.eval := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
  have hAT := hC.A_ne (by omega)
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some (qv i j) hC.scratch (by omega : 1 < 2)
  have h₁' := h.write_scratch (fun _ => hAT) h₁
  obtain ⟨l, hAsh, hAlt⟩ := hC.A_shape _ hk
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some (zv i j) hAsh hAlt
  refine ⟨s₂, ?_, h₁'.write_of_lt hk h₂, ?_⟩
  · have rx : σ.store.read p x (xo.eval + i) = some (xv i) :=
      (h.read_of_ne (hC.x_out (by omega) i hi).1
        (hC.x_out (by omega) i hi).2).trans (hC.x_read (by omega) i hi)
    have rA : s₁.read p A (ao.eval + i + m.eval * j) = some (M i j) := by
      rw [Nat.add_assoc, h₁'.2.2 _ hk, hw]
    rw [← Nat.add_assoc] at h₂
    simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
      IExp.eval_zero, IExp.eval_one, rx, ht, hC.cell_mul i hi j hj, hC.cell_add i hi j hj,
      h₁, Option.bind_some,
      Option.map_some, Store.read_of_write_eq_some h₁, rA, h₂]
    simp only [add_assoc]
  · rw [Store.read_of_write_eq_some_of_ne h₂ (Or.inl (Ne.symm hAT)),
      Store.read_of_write_eq_some_of_ne h₁ (Or.inr (by omega)), ht]

private def gerVal (M zv : ℕ → ℕ → K) (i j : ℕ) (b : Prop)
    [Decidable b] : Option K := some (if b then zv i j else M i j)

private theorem exec_gerRow
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv M cy tv qv zv)
    {σ : St P K C} {g : ℕ → Option K} {j : ℕ} (hj : j < n.eval)
    (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (ht : σ.store.read p T 0 = some (tv j))
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = gerVal M zv i j' (j' < j)) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
        (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩
          ⟨T, 1⟩)) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval •
          (I.charge (.bin p .mul) + I.charge (.bin p .add)) } ∧
        Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          gerVal M zv i j' (j' < j + 1) := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • (I.charge (.bin p .mul) + I.charge (.bin p .add)) } ∧
      Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
      s'.read p T 0 = some (tv j) ∧ ∀ i < m.eval, ∀ j' < n.eval,
        g' (i + m.eval * j') = gerVal M zv i j' (j' < j ∨ (j' = j ∧ i < i')))
    ⟨σ.store, g, by simp, h, ht, by simpa using hg⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, _, hrow⟩ => ⟨hrun, s', g', hσ, hI, fun i hi j' hj' => by
      rw [hrow i hi j' hj']
      unfold gerVal
      split_ifs <;> first | rfl | (exfalso; omega)⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, ht', hrow⟩
  replace hI : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ'.store g' := hσ ▸ hI
  replace ht' : σ'.store.read p T 0 = some (tv j) := hσ ▸ ht'
  have hw := hrow i' hi' j hj
  simp only [gerVal, lt_irrefl, false_or, and_false, if_false] at hw
  obtain ⟨s'', hrun, hI', ht''⟩ := exec_gerStep hC hi' hj hI ht' hw
  refine ⟨_, hrun, s'', _, ?_, hI', ht'', fun i hi j' hj' => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases he : i = i' ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := he
      simp [gerVal]
    · rw [Function.update_of_ne (fun h' => he
        ((Nat.add_mul_eq_add_mul_iff_of_lt hi hi').mp h')), hrow i hi j' hj']
      unfold gerVal
      split_ifs <;> first | rfl | (exfalso; omega)

private theorem exec_gerCol
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv M cy tv qv zv)
    {σ : St P K C} {g : ℕ → Option K} {j : ℕ} (hj : j < n.eval)
    (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = gerVal M zv i j' (j' < j)) :
    ∃ σ', exec I (.seq (.instr (.un p .conj ⟨T, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨T, 0⟩ a ⟨T, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨T, 1⟩)) .skip)) .skip))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (I.charge (.un p .conj) +
          I.charge (.bin p .mul) + m.eval •
            (I.charge (.bin p .mul) + I.charge (.bin p .add))) } ∧
        Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          gerVal M zv i j' (j' < j + 1) := by
  obtain ⟨hyT, hyout⟩ := hC.y_out j hj
  have ry : σ.store.read p y (yo.eval + j) = some (yv j) :=
    (h.read_of_ne hyT hyout).trans (hC.y_read j hj)
  obtain ⟨s₁, h₁⟩ := h.exists_write_eq_some (cy j) hC.scratch (by omega : 0 < 2)
  have h₁' := h.write_scratch hC.A_ne h₁
  have ra : s₁.read p a.buf a.idx.eval = some av :=
    (h₁'.read_of_ne (hC.a_out (by omega)).1 (hC.a_out (by omega)).2).trans (hC.a_read (by omega))
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write_eq_some (tv j) hC.scratch (by omega : 0 < 2)
  have h₂' := h₁'.write_scratch hC.A_ne h₂
  obtain ⟨σ'', hrun, s'', g'', hσ'', hI'', hrow''⟩ := exec_gerRow (M := M) hC hj (σ := { σ with
      store := s₂, cnt := σ.cnt + I.charge (.un p .conj) + I.charge (.bin p .mul) }) h₂'
    (Store.read_of_write_eq_some h₂) hg
  refine ⟨σ'', ?_, s'', g'', ?_, hI'', hrow''⟩
  · rw [exec_seq_instr_un I (s := s₁) ry (hC.conj j hj) h₁,
      exec_seq_instr_bin I (s := s₂) ra (Store.read_of_write_eq_some h₁) (hC.col_mul j hj)
        h₂, exec_seq_skip]
    exact hrun
  · rw [hσ'']
    simp only [add_assoc]

private theorem exec_gerCols
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv M cy tv qv zv)
    {σ : St P K C} {g : ℕ → Option K}
    (h : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = some (M i j')) :
    ∃ σ', exec I (.loop n fun j => .seq (.instr (.un p .conj ⟨T, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨T, 0⟩ a ⟨T, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨T, 1⟩)) .skip)) .skip))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + n.eval •
          (I.charge (.un p .conj) + I.charge (.bin p .mul) + m.eval •
            (I.charge (.bin p .mul) + I.charge (.bin p .add))) } ∧
        Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          some (zv i j') := by
  refine (exists_exec_loop_eq_some_of_forall I (fun j σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + j • (I.charge (.un p .conj) + I.charge (.bin p .mul) +
        m.eval • (I.charge (.bin p .mul) + I.charge (.bin p .add))) } ∧
      Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
      ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') = gerVal M zv i j' (j' < j))
    ⟨σ.store, g, by simp, h, fun i hi j' hj' => by simp [gerVal, hg i hi j' hj']⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ => ⟨hrun, s', g', hσ, hI, fun i hi j' hj' => by
      simpa [gerVal, hj'] using hrow i hi j' hj'⟩
  rintro j hj σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : Store.BlockFrame s₀ p T A ao.eval (m.eval * n.eval) σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hrow'⟩ := exec_gerCol hC hj hI hrow
  refine ⟨_, hrun, s'', g'', ?_, hI', hrow'⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]


omit [DecidableEq P] in
/-- A disjoint input cell is outside the destination interval. -/
private theorem outside_of_blockDisjoint {b o l A ao N i : ℕ}
    (hd : blockDisjoint (b, o, l) (A, ao, N) = true) (hi : i < l) :
    ¬(p = p ∧ b = A ∧ ao ≤ o + i ∧ o + i < ao + N) := by
  have hh := blockDisjoint_iff.mp hd
  dsimp only at hh
  omega

/-- The actual rank-one update succeeds from arbitrary successful scalar instruction
witnesses, initialized source/matrix words and disjoint source/output blocks. The coefficient,
conjugation, row-scaling multiply, cell multiply and final add witnesses follow the exact
instruction order. The only net store effect is one full packed matrix block write. This
execution lemma assumes no arithmetic error model or numerical value bounds. -/
theorem exec_ger_words (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (av : K) (xv yv cy tv : ℕ → K) (M qv zv : ℕ → ℕ → K)
    (ha : 0 < n.eval → st.store.read p a.buf a.idx.eval = some av)
    (hx : 0 < n.eval → ∀ i < m.eval, st.store.read p x (xo.eval + i) = some (xv i))
    (hy : ∀ j < n.eval, st.store.read p y (yo.eval + j) = some (yv j))
    (hM : ∀ i < m.eval, ∀ j < n.eval,
      st.store.read p A (ao.eval + i + m.eval * j) = some (M i j))
    (haA : blockDisjoint (a.buf, a.idx.eval, 1) (A, ao.eval, m.eval * n.eval) = true)
    (hxA : blockDisjoint (x, xo.eval, m.eval) (A, ao.eval, m.eval * n.eval) = true)
    (hyA : blockDisjoint (y, yo.eval, n.eval) (A, ao.eval, m.eval * n.eval) = true)
    (hcj : ∀ j < n.eval, I.sem.un p .conj (yv j) = some (cy j))
    (hct : ∀ j < n.eval, I.sem.bin p .mul av (cy j) = some (tv j))
    (hcq : ∀ i < m.eval, ∀ j < n.eval,
      I.sem.bin p .mul (xv i) (tv j) = some (qv i j))
    (hcz : ∀ i < m.eval, ∀ j < n.eval,
      I.sem.bin p .add (M i j) (qv i j) = some (zv i j)) :
    ∃ (out : St P K C) (W : Array K), W.size = m.eval * n.eval ∧
      exec I (ger p m n a x xo y yo A ao).run st = some out ∧
      st.store.writeBlock p A ao.eval W = some out.store ∧
      ∀ i < m.eval, ∀ j < n.eval, W[i + m.eval * j]? = some (zv i j) := by
  let W := (List.range (m.eval * n.eval)).toArray.map
    (fun k => zv (k % m.eval) (k / m.eval))
  have hWs : W.size = m.eval * n.eval := by simp [W]
  have hW : ∀ k < m.eval * n.eval,
      W[k]? = some (zv (k % m.eval) (k / m.eval)) := by
    intro k hk
    simp [W, hk]
  have hshape : Writable st.store p A ao.eval (m.eval * n.eval) := by
    intro k hk
    have hm : 0 < m.eval := by nlinarith
    have hj : k / m.eval < n.eval := Nat.div_lt_of_lt_mul hk
    have hh := hM (k % m.eval) (Nat.mod_lt _ hm) (k / m.eval) hj
    rw [Nat.add_assoc, Nat.mod_add_div] at hh
    exact Store.exists_getElem?_shape_of_read_eq_some hh
  obtain ⟨s₁, h₁⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := st.store) (xs := W) (by intro i hi; exact hshape i (hWs ▸ hi))
  rw [run_ger, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  let s₀ := st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)
  have hC : GerCtx I s₀ p st.store.size A x y a m.eval n.eval ao.eval xo.eval yo.eval
      av xv yv M cy tv qv zv :=
    { scratch := Store.getElem?_shape_push_size _ _ _
      A_ne := fun hn => Nat.ne_of_lt (hshape.lt_size hn)
      A_shape := fun k hk => by
        rw [Store.getElem?_shape_push_of_lt _ (hshape.lt_size (by omega))]
        exact hshape k hk
      a_read := fun hn => by
        rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some (ha hn)), ha hn]
      a_out := fun hn => ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (ha hn)), by
        simpa only [Nat.add_zero] using outside_of_blockDisjoint (p := p) haA (by omega : 0 < 1)⟩
      x_read := fun hn i hi => by
        rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hx hn i hi)), hx hn i hi]
      x_out := fun hn i hi =>
        ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hx hn i hi)),
          outside_of_blockDisjoint hxA hi⟩
      y_read := fun j hj => by
        rw [Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hy j hj)), hy j hj]
      y_out := fun j hj => ⟨Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hy j hj)),
        outside_of_blockDisjoint hyA hj⟩
      conj := hcj
      col_mul := hct
      cell_mul := hcq
      cell_add := hcz }
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := exec_gerCols hC
    (σ := { st with
      store := s₀
      cur := Function.update st.cur p (st.cur p + (2 : IExp ℕ).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (2 : IExp ℕ).eval))
      curW := st.curW + (2 : IExp ℕ).eval * I.width p
      peakW := max st.peakW (st.curW + (2 : IExp ℕ).eval * I.width p) })
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩ (fun i hi j hj => by
      rw [← Nat.add_assoc, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hM i hi j hj))]
      exact hM i hi j hj)
  rw [hF, Option.map_some]
  have hpop : sF.pop = s₁ := hIF.pop_eq h₁ hWs (fun k hk => by
    have hm : 0 < m.eval := by nlinarith
    rw [hW k hk]
    have hg := hgF (k % m.eval) (Nat.mod_lt _ hm) (k / m.eval) (Nat.div_lt_of_lt_mul hk)
    rwa [Nat.mod_add_div] at hg)
  refine ⟨_, W, hWs, rfl, by simpa only [hpop] using h₁, fun i hi j hj => ?_⟩
  rw [hW _ (Nat.add_mul_lt_mul_of_lt_of_lt hi hj)]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
    Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.zero_add]

end RankOneRounding

/-- Under standard relative-error semantics with every scalar result in range, readable decoded
operands and an initialized decoded matrix, the actual `ger` succeeds and writes exactly its
matrix block. The witnesses
record its instruction order: coefficient times right entry, left entry times that intermediate,
and addition to the original matrix. The three relations use the standard model of
[Higham2002, §2.2]. Inputs may share buffers with the destination when their blocks are disjoint.
For an empty column range no coefficient or left-vector readability is required. With zero rows
and nonzero columns the coefficient and right entries are still read.
There is no restriction on arithmetic charges or on the word carrier. -/
theorem IsRelErrSem.exec_ger {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (st : St P K C) (m n : IExp ℕ) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (av : ℝ) (xs : Fin m.eval → ℝ) (ys : Fin n.eval → ℝ)
    (M : Matrix (Fin m.eval) (Fin n.eval) ℝ)
    (ha : 0 < n.eval → ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : 0 < n.eval → ReadsDecoded st.store dec p x xo.eval xs)
    (hy : ReadsDecoded st.store dec p y yo.eval ys)
    (hM : HoldsDecoded st.store dec p A ao.eval M)
    (haA : blockDisjoint (a.buf, a.idx.eval, 1) (A, ao.eval, m.eval * n.eval) = true)
    (hxA : blockDisjoint (x, xo.eval, m.eval) (A, ao.eval, m.eval * n.eval) = true)
    (hyA : blockDisjoint (y, yo.eval, n.eval) (A, ao.eval, m.eval * n.eval) = true) :
    ∃ (out : St P K C) (W : Array K) (t : Fin n.eval → ℝ)
      (q : Matrix (Fin m.eval) (Fin n.eval) ℝ),
      W.size = m.eval * n.eval ∧
      exec I (ger p m n a x xo y yo A ao).run st = some out ∧
      st.store.writeBlock p A ao.eval W = some out.store ∧
      (∀ j, RelErr (u p) (av * ys j) (t j)) ∧
      ∀ i j, RelErr (u p) (xs i * t j) (q i j) ∧
        RelErr (u p) (M i j + q i j)
          (unflatten m.eval n.eval (W.map (dec p)) i j) := by
  classical
  obtain ⟨w₀, _⟩ := h.lit_ok p 0 trivial
  have ha' : ∃ w, ∀ hn : 0 < n.eval,
      st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av := by
    by_cases hn : 0 < n.eval
    · obtain ⟨w, hw⟩ := ha hn
      exact ⟨w, fun _ => hw⟩
    · exact ⟨w₀, fun hh => (hn hh).elim⟩
  obtain ⟨aw, haw⟩ := ha'
  have hx' : ∀ i : Fin m.eval, ∃ w, ∀ hn : 0 < n.eval,
      st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i := by
    intro i
    by_cases hn : 0 < n.eval
    · obtain ⟨w, hw⟩ := hx hn i
      exact ⟨w, fun _ => hw⟩
    · exact ⟨w₀, fun hh => (hn hh).elim⟩
  choose xw hxw using hx'
  choose yw hyw hdyw using hy
  choose Mw hMw hdMw using hM
  let xv (i : ℕ) := if hi : i < m.eval then xw ⟨i, hi⟩ else w₀
  let yv (j : ℕ) := if hj : j < n.eval then yw ⟨j, hj⟩ else w₀
  let Mv (i j : ℕ) := if hij : i < m.eval ∧ j < n.eval then Mw ⟨i, hij.1⟩ ⟨j, hij.2⟩ else w₀
  choose cy hcy hdcy using fun j : ℕ => h.conj p (yv j)
  choose tv htv using fun j : ℕ => h.bin_ok p .mul aw (cy j) trivial (by simp) trivial
  choose qv hqv using fun i j : ℕ => h.bin_ok p .mul (xv i) (tv j) trivial (by simp) trivial
  choose zv hzv using fun i j : ℕ => h.bin_ok p .add (Mv i j) (qv i j) trivial (by simp) trivial
  obtain ⟨out, W, hWs, hr, hw, hW⟩ := RankOneRounding.exec_ger_words I p st m n a x xo y yo A ao
    aw xv yv cy tv Mv qv zv (fun hn => (haw hn).1)
    (fun hn i hi => by simpa only [xv, dif_pos hi] using (hxw ⟨i, hi⟩ hn).1)
    (fun j hj => by simpa only [yv, dif_pos hj] using hyw ⟨j, hj⟩)
    (fun i hi j hj => by simpa only [Mv, dif_pos (And.intro hi hj)] using hMw ⟨i, hi⟩ ⟨j, hj⟩)
    haA hxA hyA (fun j _ => hcy j) (fun j _ => htv j)
    (fun i _ j _ => hqv i j) (fun i _ j _ => hzv i j)
  refine ⟨out, W, fun j => dec p (tv j), fun i j => dec p (qv i j), hWs, hr, hw, ?_, ?_⟩
  · intro j
    have hj := j.isLt
    have hh := h.bin_err p .mul aw (cy j) (tv j) trivial (htv j)
    simpa only [RelErr, BinOp.realOp, (haw (by omega)).2, hdcy, yv, dif_pos j.isLt, hdyw] using hh
  · intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hq := h.bin_err p .mul (xv i) (tv j) (qv i j) trivial (hqv i j)
    have hz := h.bin_err p .add (Mv i j) (qv i j) (zv i j) trivial (hzv i j)
    have hout : unflatten m.eval n.eval (W.map (dec p)) i j = dec p (zv i j) := by
      simp only [unflatten, Matrix.of_apply, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        hW i i.isLt j j.isLt, Option.map_some, Option.getD_some]
    refine ⟨?_, ?_⟩
    · simpa only [RelErr, BinOp.realOp, xv, dif_pos i.isLt, (hxw i (by omega)).2] using hq
    · simpa only [RelErr, hout, BinOp.realOp, Mv, dif_pos (And.intro i.isLt j.isLt), hdMw] using hz

end NLAlib.Computation
