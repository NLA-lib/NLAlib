/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.CholeskyRoundingError
public import NLAlib.Matrix.Factorizations.TriangularSolve.Substitution

/-!
# Left-looking Cholesky factorization as a routine

`NLAlib.Cholesky.leftLooking` factors a matrix stored by columns in place, over scalar operations,
with one scratch cell: the running value of an entry is kept in the cell of that entry. The
routine is generic over the signature, so it can be run at a precision tag. The machine is total,
so the run succeeds on every input; the specification is the trace of computed values
`NLAlib.Computation.IsCholTrace`, which assumes nothing about the pivots.

## Main definitions

* `NLAlib.Cholesky.leftLooking`, `NLAlib.Cholesky.leftLookingSpec`: the routine and its
  specification.

## Main results

* `NLAlib.Cholesky.leftLooking_meets`: the block written is a trace of left-looking Cholesky.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops Computation TriangularSolve

variable {K Op Tst : Type}

/-! ### Values -/

/-- The entries of a matrix of order `n` stored by columns in the words `W`, decoded. -/
def entryOf (dec : K → ℝ) (n : ℕ) (W : ℕ → K) : ℕ → ℕ → ℝ := fun i j => dec (W (j * n + i))

/-- The offset of an entry of a matrix stored by columns determines the column and the row. -/
theorem mul_add_inj {n c c' r r' : ℕ} (hr : r < n) (hr' : r' < n)
    (h : c * n + r = c' * n + r') : c = c' ∧ r = r' := by
  rcases Nat.lt_trichotomy c c' with hc | rfl | hc
  · have := Nat.mul_le_mul_right n hc
    rw [Nat.succ_mul] at this
    omega
  · exact ⟨rfl, by omega⟩
  · have := Nat.mul_le_mul_right n hc
    rw [Nat.succ_mul] at this
    omega

/-- Two different positions of a matrix stored by columns have different offsets. -/
theorem mul_add_ne {n c c' r r' : ℕ} (hr : r < n) (hr' : r' < n) (h : c ≠ c' ∨ r ≠ r') :
    c * n + r ≠ c' * n + r' := fun e => by
  obtain ⟨h₁, h₂⟩ := mul_add_inj hr hr' e
  rcases h with h | h
  · exact h h₁
  · exact h h₂

/-- Column `c` of a trace of left-looking Cholesky: its diagonal entry and the entries below. -/
def CholColumn (u : ℝ) (a L : ℕ → ℕ → ℝ) (n c : ℕ) : Prop :=
  (∃ s, IsCholEntryTrace u a L c c s ∧ (0 ≤ s c → RelErr u (Real.sqrt (s c)) (L c c))) ∧
    ∀ i, c < i → i < n → ∃ s, IsCholEntryTrace u a L i c s ∧
      (L c c ≠ 0 → RelErr u (s c / L c c) (L i c))

/-- An entry trace depends on the factor only at the two rows, in the columns before its own. -/
theorem isCholEntryTrace_congr {u : ℝ} {a L L' : ℕ → ℕ → ℝ} {i j : ℕ} {s : ℕ → ℝ}
    (h : IsCholEntryTrace u a L i j s) (hL : ∀ k < j, L i k = L' i k ∧ L j k = L' j k) :
    IsCholEntryTrace u a L' i j s :=
  ⟨h.1, fun k hk => by simpa only [(hL k hk).1, (hL k hk).2] using h.2 k hk⟩

/-- A column of a trace depends on the factor only in the columns up to its own. -/
theorem CholColumn.congr {u : ℝ} {a L L' : ℕ → ℕ → ℝ} {n c : ℕ} (h : CholColumn u a L n c)
    (hc : c < n) (hL : ∀ i < n, ∀ k ≤ c, L i k = L' i k) : CholColumn u a L' n c := by
  obtain ⟨⟨s, hs, hd⟩, hb⟩ := h
  refine ⟨⟨s, isCholEntryTrace_congr hs fun k hk => ⟨hL c hc k hk.le, hL c hc k hk.le⟩, ?_⟩,
    fun i hci hi => ?_⟩
  · rwa [← hL c hc c le_rfl]
  · obtain ⟨s, hs, hd⟩ := hb i hci hi
    refine ⟨s, isCholEntryTrace_congr hs fun k hk => ⟨hL i hi k hk.le, hL c hc k hk.le⟩, ?_⟩
    rwa [← hL c hc c le_rfl, ← hL i hi c le_rfl]

/-- The accumulator of entry $(r, j)$ is an entry trace, for a factor that holds the words read in
the columns before `j`. -/
theorem isCholEntryTrace_mulSubWord {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    {a L : ℕ → ℕ → ℝ} {A B : ℕ → K} {v : K} {r j : ℕ} (hv : dec v = a r j)
    (hA : ∀ k < j, dec (A k) = L r k) (hB : ∀ k < j, dec (B k) = L j k) :
    IsCholEntryTrace u a L r j (fun l => dec (mulSubWord M A B v l)) :=
  ⟨hv, fun k hk => by simpa only [hA k hk, hB k hk] using relErr_mulSubWord hM A B v k⟩

/-- Entries $(r, j)$ of column `j`, `j < r < j + 1 + l`, computed on the words `W`. -/
def BelowPrefix (u : ℝ) (dec : K → ℝ) (a : ℕ → ℕ → ℝ) (n j l : ℕ) (W : ℕ → K) : Prop :=
  ∀ r, j < r → r < j + 1 + l → ∃ s, IsCholEntryTrace u a (entryOf dec n W) r j s ∧
    (entryOf dec n W j j ≠ 0 →
      RelErr u (s j / entryOf dec n W j j) (entryOf dec n W r j))

/-- The word of the entry below the diagonal in row `j + 1 + l`, on the words `W`. -/
def belowWord (M : Machine K) (n j l : ℕ) (W : ℕ → K) : K :=
  M.div (mulSubWord M (fun k => W (k * n + (j + 1 + l))) (fun k => W (k * n + j))
    (W (j * n + (j + 1 + l))) j) (W (j * n + j))

/-- Writing the next entry below the diagonal extends the prefix of computed entries. -/
theorem BelowPrefix.succ {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    {a : ℕ → ℕ → ℝ} {n j l : ℕ} {W : ℕ → K} (h : BelowPrefix u dec a n j l W)
    (hl : j + 1 + l < n) (hv : dec (W (j * n + (j + 1 + l))) = a (j + 1 + l) j) :
    BelowPrefix u dec a n j (l + 1)
      (Function.update W (j * n + (j + 1 + l)) (belowWord M n j l W)) := by
  have hkeep : ∀ {c r : ℕ}, r < n → (c ≠ j ∨ r ≠ j + 1 + l) →
      entryOf dec n (Function.update W (j * n + (j + 1 + l)) (belowWord M n j l W)) r c =
        entryOf dec n W r c := fun hr hcr => by
    simp only [entryOf, Function.update_of_ne (mul_add_ne hr hl hcr)]
  have hjn : j < n := by omega
  intro r hjr hr
  rcases Nat.lt_succ_iff_lt_or_eq.mp (show r < j + 1 + l + 1 by omega) with hr' | rfl
  · obtain ⟨s, hs, hd⟩ := h r hjr hr'
    have hrn : r < n := by omega
    refine ⟨s, isCholEntryTrace_congr hs fun k hk =>
      ⟨(hkeep hrn (Or.inl (by omega))).symm, (hkeep hjn (Or.inl (by omega))).symm⟩, ?_⟩
    rw [hkeep hjn (Or.inr (by omega)), hkeep hrn (Or.inr (by omega))]
    exact hd
  · refine ⟨_, isCholEntryTrace_mulSubWord hM (A := fun k => W (k * n + (j + 1 + l)))
      (B := fun k => W (k * n + j)) (v := W (j * n + (j + 1 + l))) hv
      (fun k hk => (hkeep hl (Or.inl (by omega))).symm)
      (fun k hk => (hkeep hjn (Or.inl (by omega))).symm), ?_⟩
    rw [hkeep hjn (Or.inr (by omega))]
    intro hD
    have e : entryOf dec n (Function.update W (j * n + (j + 1 + l)) (belowWord M n j l W))
        (j + 1 + l) j = dec (belowWord M n j l W) := by
      simp only [entryOf, Function.update_self]
    rw [e]
    exact relErr_of_abs_sub_le (unitRoundoff_nonneg hM) (hM.div _ _ hD)

/-- After the diagonal and the entries below it are written, the columns up to `j` are columns of a
trace, on the final words `Wf`. -/
theorem cholColumn_succ {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    {a : ℕ → ℕ → ℝ} {n j : ℕ} {W Wf : ℕ → K} (hj : j < n)
    (hpre : ∀ c < j, CholColumn u a (entryOf dec n W) n c)
    (hv : dec (W (j * n + j)) = a j j)
    (hkeep : ∀ c r, r < n → (c ≠ j ∨ r ≤ j) → Wf (c * n + r) = Function.update W (j * n + j)
      (M.sqrt (mulSubWord M (fun k => W (k * n + j)) (fun k => W (k * n + j))
        (W (j * n + j)) j)) (c * n + r))
    (hbelow : BelowPrefix u dec a n j (n - (j + 1)) Wf) :
    ∀ c < j + 1, CholColumn u a (entryOf dec n Wf) n c := by
  have hold : ∀ {c r : ℕ}, r < n → c < j → entryOf dec n Wf r c = entryOf dec n W r c :=
    fun hr hc => by
      simp only [entryOf]
      rw [hkeep _ _ hr (Or.inl (by omega)),
        Function.update_of_ne (mul_add_ne hr hj (Or.inl (by omega)))]
  intro c hc
  by_cases hcj : c = j
  · rw [hcj]
    have e : entryOf dec n Wf j j = dec (M.sqrt (mulSubWord M (fun k => W (k * n + j))
        (fun k => W (k * n + j)) (W (j * n + j)) j)) := by
      simp only [entryOf]
      rw [hkeep j j hj (Or.inr le_rfl), Function.update_self]
    refine ⟨⟨_, isCholEntryTrace_mulSubWord hM (A := fun k => W (k * n + j))
      (B := fun k => W (k * n + j)) (v := W (j * n + j)) hv
      (fun k hk => (hold hj hk).symm) (fun k hk => (hold hj hk).symm), fun hs => ?_⟩,
      fun i hji hin => hbelow i hji (by omega)⟩
    rw [e]
    refine relErr_of_abs_sub_le (unitRoundoff_nonneg hM) ?_
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hM.sqrt _ hs
  · have hcl : c < j := by omega
    exact (hpre c hcl).congr (by omega) fun i hi k hk => (hold hi (by omega)).symm

/-! ### The routine -/

section Routine

variable [Has ScalarOp Op]

/-- **Left-looking Cholesky factorization** in place on a matrix stored by columns. For each
column, the diagonal entry is accumulated and replaced by its rounded square root, then each entry
below it is accumulated and divided by the diagonal. One scratch cell holds the products. -/
def leftLooking : Routine Op Tst := routine% [n] (L : n * n) → (L) {
  let t ← alloc 1;
  for j < n {
    for k < j {
      call (Has.inj ScalarOp.mul) [] (L[k * n + j], L[k * n + j]) → (t);
      call (Has.inj ScalarOp.sub) [] (L[j * n + j], t) → (L[j * n + j])
    };
    call (Has.inj ScalarOp.sqrt) [] (L[j * n + j]) → (L[j * n + j]);
    for i < n - (j + 1) {
      for k < j {
        call (Has.inj ScalarOp.mul) [] (L[k * n + (j + 1 + i)], L[k * n + j]) → (t);
        call (Has.inj ScalarOp.sub) [] (L[j * n + (j + 1 + i)], t) → (L[j * n + (j + 1 + i)])
      };
      call (Has.inj ScalarOp.div) [] (L[j * n + (j + 1 + i)], L[j * n + j]) →
        (L[j * n + (j + 1 + i)])
    }
  }
}

variable [Inhabited K]

/-- The block written is a trace of left-looking Cholesky at unit roundoff $u$ on the decoded
block read. Nothing is assumed of the pivots. -/
def leftLookingSpec (u : ℝ) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (Ls) → (Ls') ensures
    IsCholTrace u (fun i j => dec (vec Ls (j * n + i))) (fun i j => dec (vec Ls' (j * n + i))) n

omit [Inhabited K] in
/-- The loop over the entries below the diagonal of column `j`, a fragment of
`NLAlib.Cholesky.leftLooking`: every entry is accumulated in place and divided by the diagonal.
The columns before `j`, the diagonal and the entries above it are not written. -/
theorem leftLookingBelow_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) {u : ℝ}
    {dec : K → ℝ} (hM : StdModel u dec M) {τ : Tape K} {ρ : Env} {m : Mem K} {bound inner : IExp}
    {n j o b₀ : ℕ} {w : ℕ × ℕ} {a₀ b c d t : Operand} {W₀ : ℕ → K} {a : ℕ → ℕ → ℝ} (hj : j < n)
    (hbound : bound.eval ρ.idx = some (n - (j + 1)))
    (hinner : ∀ i, inner.eval (ρ.pushIdx i).idx = some j)
    (ha : ∀ i, ∀ k, a₀.eval ((ρ.pushIdx i).pushIdx k) = some (b₀, o + k * n + (j + 1 + i)))
    (hb : ∀ i, ∀ k, b.eval ((ρ.pushIdx i).pushIdx k) = some (b₀, o + k * n + j))
    (hc : ∀ i, c.eval (ρ.pushIdx i) = some (b₀, o + j * n + (j + 1 + i)))
    (hd : ∀ i, d.eval (ρ.pushIdx i) = some (b₀, o + j * n + j))
    (ht : ∀ i, ∀ k, t.eval ((ρ.pushIdx i).pushIdx k) = some w) (hbw : b₀ ≠ w.1)
    (hw : w.2 < m.store.len w.1) (hW : CellsHold m.store b₀ o (n * n) W₀)
    (horig : ∀ r, j < r → r < n → dec (W₀ (j * n + r)) = a r j) :
    Writes .total I τ
      (.loop bound (.seq (.loop inner (.seq (.call (Has.inj ScalarOp.mul) [] [a₀, b] [t])
        (.call (Has.inj ScalarOp.sub) [] [c, t] [c])))
        (.call (Has.inj ScalarOp.div) [] [c, d] [c]))) ρ
      (Store.inBlock b₀ o (n * n) ⊔ Store.inBlock w.1 w.2 1)
      (fun m' => m'.pos = m.pos ∧ ∃ W', CellsHold m'.store b₀ o (n * n) W' ∧
        (∀ c r, r < n → (c ≠ j ∨ r ≤ j) → W' (c * n + r) = W₀ (c * n + r)) ∧
        BelowPrefix u dec a n j (n - (j + 1)) W') m := by
  refine Writes.mono (writes_loop hbound
    (fun _ => Store.inBlock b₀ o (n * n) ⊔ Store.inBlock w.1 w.2 1) (fun _ _ => le_rfl)
    (fun l m' => m'.pos = m.pos ∧ ∃ W', CellsHold m'.store b₀ o (n * n) W' ∧
      (∀ c r, r < n → (c ≠ j ∨ r < j + 1 ∨ j + 1 + l ≤ r) → W' (c * n + r) = W₀ (c * n + r)) ∧
      BelowPrefix u dec a n j l W')
    ⟨rfl, W₀, hW, fun _ _ _ _ => rfl, fun r h₁ h₂ => absurd h₂ (by omega)⟩ ?_) le_rfl ?_
  · intro l hl m₁ hfr ⟨hpos₁, W, hW₁, hkeep, hpre⟩
    have hrn : j + 1 + l < n := by omega
    have hlw : w.2 < m₁.store.len w.1 := by rw [hfr.len_eq]; exact hw
    have hval : W (j * n + (j + 1 + l)) = W₀ (j * n + (j + 1 + l)) :=
      hkeep j _ hrn (Or.inr (Or.inr le_rfl))
    have hcell : ∀ {c r : ℕ}, c < n → r < n → c * n + r ≠ j * n + (j + 1 + l) →
        (b₀, o + c * n + r) ≠ (b₀, o + j * n + (j + 1 + l)) := fun _ _ hne e => hne (by
      have := congrArg Prod.snd e
      simp only at this
      omega)
    have hwrite := writes_mulSubDiv (τ := τ) (m := m₁) hI (hinner l)
      (a := a₀) (b := b) (c := c) (d := d) (t := t) (p := fun k => (b₀, o + k * n + (j + 1 + l)))
      (q := fun k => (b₀, o + k * n + j)) (z := (b₀, o + j * n + (j + 1 + l))) (w := w)
      (e := (b₀, o + j * n + j)) (A := fun k => W (k * n + (j + 1 + l)))
      (B := fun k => W (k * n + j)) (v := W (j * n + (j + 1 + l))) (D := W (j * n + j))
      (fun k _ => ha l k) (fun k _ => hb l k) (hc l) (hd l) (fun k _ => ht l k)
      (fun k hk => hW₁.get_entry (by omega) hrn) (fun k hk => hW₁.get_entry (by omega) hj)
      (hW₁.get_entry hj hrn) (hW₁.get_entry hj hj) hbw
      (fun k hk => hcell (by omega) hrn fun e => by
        have := (mul_add_inj hrn hrn e).1
        omega)
      (fun k hk => hcell (by omega) hj fun e => by
        have := (mul_add_inj hj hrn e).1
        omega)
      (fun _ _ => hbw) (fun _ _ => hbw)
      (hcell hj hj fun e => by
        have := (mul_add_inj hj hrn e).2
        omega) hbw hlw
    refine Writes.mono hwrite (sup_le ?_ le_sup_right) fun m₂ hfr₂ ⟨hpos₂, hz₂⟩ =>
      ⟨hpos₂.trans hpos₁, _, hW₁.update_entry (c := j) (r := j + 1 + l) hfr₂ hbw.symm hz₂,
        fun c r hr hcr => ?_, hpre.succ hM hrn (by rw [hval]; exact horig _ (by omega) hrn)⟩
    · rintro _ _ ⟨rfl, h₁, h₂⟩
      have hlt := mul_add_lt_mul_self hj hrn
      exact Or.inl ⟨rfl, by simp only at h₁; omega, by simp only at h₁ h₂; omega⟩
    · rw [Function.update_of_ne (fun e => by
        obtain ⟨h₁, h₂⟩ := mul_add_inj hr hrn e
        omega)]
      exact hkeep c r hr (by omega)
  · rintro m₁ - ⟨hpos₁, W, hW₁, hkeep, hpre⟩
    exact ⟨hpos₁, W, hW₁, fun c r hr hcr => hkeep c r hr (by omega), hpre⟩

/-- Left-looking Cholesky meets its specification under the standard model, with no assumption
on the pivots. -/
theorem leftLooking_meets {M : Machine K} {I : Interp Op Tst K} {u : ℝ} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) :
    (leftLooking (Op := Op) (Tst := Tst)).Meets I (leftLookingSpec u dec) := by
  routine_intro [n] (L) reads (Ls)
  change Writes .total I τ _ (Env.frame [n] [L, L]) (Fp.blocks [L] [n * n]) _ m
  alloc as t
  have hLs₁ := Store.Below.readBlock_of hbelow_t hl hLs
  have htne : L.1 ≠ t := Nat.ne_of_lt hl
  have htlen : 0 < s_t.len t := Nat.lt_of_lt_of_eq Nat.one_pos ht.symm
  refine Writes.mono (writes_loop (N := n) (by rfl)
    (fun _ => Store.inBlock L.1 L.2 (n * n) ⊔ Store.inBlock t 0 1) (fun _ _ => le_rfl)
    (fun j m' => m'.pos = m.pos ∧ ∃ W, CellsHold m'.store L.1 L.2 (n * n) W ∧
      (∀ c r, j ≤ c → c < n → r < n → W (c * n + r) = vec Ls (c * n + r)) ∧
      ∀ c < j, CholColumn u (entryOf dec n (vec Ls)) (entryOf dec n W) n c)
    ⟨rfl, vec Ls, CellsHold.of_readBlock hLs₁, fun _ _ _ _ _ => rfl,
      fun _ h => absurd h (by omega)⟩ ?_) ?_ ?_
  · intro j hj m₁ hfr ⟨hpos₁, W, hW, horig, hpre₁⟩
    have hlt₁ : 0 < m₁.store.len t := by rw [hfr.len_eq]; exact htlen
    have hcell : ∀ k < j, (L.1, L.2 + k * n + j) ≠ (L.1, L.2 + j * n + j) := fun k hk e => by
      have h₂ : L.2 + k * n + j = L.2 + j * n + j := congrArg Prod.snd e
      have := (mul_add_inj (c := k) (c' := j) hj hj (by omega)).1
      omega
    refine Writes.seq_le (writes_mulSubLoop (m := m₁) hI (N := j) (by rfl)
      (p := fun k => (L.1, L.2 + k * n + j)) (q := fun k => (L.1, L.2 + k * n + j))
      (z := (L.1, L.2 + j * n + j)) (w := (t, 0))
      (A := fun k => W (k * n + j)) (B := fun k => W (k * n + j)) (v := W (j * n + j))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun k hk => hW.get_entry (by omega) hj) (fun k hk => hW.get_entry (by omega) hj)
      (hW.get_entry hj hj) htne hcell hcell (fun _ _ => htne) (fun _ _ => htne) hlt₁)
      (sup_le_sup_right (inBlock_entry_le hj hj) _) fun m₂ hfr₂ ⟨hpos₂, hz₂⟩ => ?_
    have hz₂' : m₂.store.get L.1 (L.2 + j * n + j) = some (mulSubWord M (fun k => W (k * n + j))
        (fun k => W (k * n + j)) (W (j * n + j)) j) := hz₂
    step (hI .sqrt) as m₃ hfr₃ ⟨hpos₃, v, hv, rfl⟩
    have hW₀ := hW.update_entry (c := j) (r := j) (w := (t, 0))
      (hfr₂.trans (hfr₃.mono fun _ _ h => Or.inl h)) htne.symm hv
    refine Writes.mono (leftLookingBelow_writes (m := m₃) (a := entryOf dec n (vec Ls))
      (o := L.2) (b₀ := L.1) (w := (t, 0)) hI hM hj (by rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) htne
      (by
        change 0 < m₃.store.len t
        rw [hfr₃.len_eq, hfr₂.len_eq]
        exact hlt₁) hW₀ (fun r hjr hr => ?_)) le_rfl
      fun m₄ _ ⟨hpos₄, Wf, hWf, hkeep, hbelow⟩ => ⟨hpos₄.trans (hpos₃.trans (hpos₂.trans hpos₁)),
        Wf, hWf, fun c r hc hcn hr => ?_,
        cholColumn_succ hM hj hpre₁ (by rw [horig j j le_rfl hj hj]; rfl) hkeep hbelow⟩
    · rw [Function.update_of_ne (mul_add_ne hr hj (Or.inr (by omega))), horig j r le_rfl hj hr]
      rfl
    · rw [hkeep c r hr (Or.inl (by omega)),
        Function.update_of_ne (mul_add_ne hr hj (Or.inl (by omega)))]
      exact horig c r (by omega) hcn hr
  · fp_sub
  · rintro m' - ⟨hpos, W, hW, -, hpre₁⟩ s₂ - hB
    refine ⟨hpos, [(List.range (n * n)).map W],
      Mem.readBlocks_of_cons (Store.Below.readBlock_of hB hl hW.readBlock) rfl, ?_⟩
    have hcol : ∀ c < n, CholColumn u (entryOf dec n (vec Ls))
        (entryOf dec n (vec ((List.range (n * n)).map W))) n c := fun c hc =>
      (hpre₁ c hc).congr hc fun i hi k hk => by
        simp only [entryOf]
        rw [vec_map_range W (mul_add_lt_mul_self (by omega) hi)]
    exact ⟨fun j hj => (hcol j hj).1, fun j hj i hji hin => (hcol j hj).2 i hji hin⟩

end Routine

end NLAlib.Cholesky
