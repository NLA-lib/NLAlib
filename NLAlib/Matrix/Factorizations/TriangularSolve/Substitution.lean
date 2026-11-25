/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Traces
public import NLAlib.Ops.Routine
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# The accumulation loop of substitution and factorization kernels

The kernels of triangular solves, of left-looking Cholesky and of the residual share one inner
loop: for $k < N$, a product $q := a_k b_k$ into a scratch cell and $c := c - q$ in place. This
file proves that loop once, for operands given by their evaluation, and the value lemmas that
turn its result into rounding traces.

## Main definitions

* `NLAlib.TriangularSolve.mulSubWord`: the word the loop leaves in the accumulator.
* `NLAlib.TriangularSolve.CellsHold`: a block of cells, read as a function of the offset.

## Main results

* `NLAlib.TriangularSolve.writes_mulSubLoop`: the loop writes the accumulator and the scratch.
* `NLAlib.TriangularSolve.writes_mulSubDiv`: the loop followed by a division.
* `NLAlib.TriangularSolve.writes_substLoop`: a whole substitution, in any order of the rows.
* `NLAlib.TriangularSolve.relErr_mulSubWord`: the decoded accumulator is a rounding trace.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops Computation

variable {K Op Tst : Type}

/-- The words of the accumulator: $w_0 = v$, $w_{k+1} = w_k \ominus (a_k \otimes b_k)$. -/
def mulSubWord (M : Machine K) (A B : ℕ → K) (v : K) : ℕ → K
  | 0 => v
  | k + 1 => M.sub (mulSubWord M A B v k) (M.mul (A k) (B k))

/-- The standard model has a nonnegative unit roundoff (from the literal one). -/
theorem unitRoundoff_nonneg {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M) :
    0 ≤ u := by
  have h := hM.lit 1
  simp only [Rat.cast_one, abs_one, mul_one] at h
  exact (abs_nonneg _).trans h

/-- An absolute bound relative to the exact value is a relative error. -/
theorem relErr_of_abs_sub_le {u a z : ℝ} (hu : 0 ≤ u) (h : |z - a| ≤ u * |a|) : RelErr u a z :=
  Computation.relErr_of_abs_sub_le hu h

/-- The decoded accumulator is a rounding trace: each step is a rounded product and a rounded
difference. -/
theorem relErr_mulSubWord {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    (A B : ℕ → K) (v : K) (k : ℕ) :
    ∃ q : ℝ, RelErr u (dec (A k) * dec (B k)) q ∧
      RelErr u (dec (mulSubWord M A B v k) - q) (dec (mulSubWord M A B v (k + 1))) := by
  have hu := unitRoundoff_nonneg hM
  exact ⟨dec (M.mul (A k) (B k)), relErr_of_abs_sub_le hu (hM.mul _ _),
    relErr_of_abs_sub_le hu (hM.sub _ _)⟩

/-- The cells at offsets below `n` of a block hold the words `W`. -/
def CellsHold (s : Store K) (b off n : ℕ) (W : ℕ → K) : Prop :=
  ∀ o < n, s.get b (off + o) = some (W o)

/-- The cells of a block read hold the entries of the list read. -/
theorem CellsHold.of_readBlock [Inhabited K] {s : Store K} {b off n : ℕ} {xs : List K}
    (h : s.readBlock b off n = some xs) : CellsHold s b off n (vec xs) :=
  fun _ ho => Store.get_of_readBlock h ho default

/-- Cells that hold `W` are the block of the values of `W`. -/
theorem CellsHold.readBlock {s : Store K} {b off n : ℕ} {W : ℕ → K} (h : CellsHold s b off n W) :
    s.readBlock b off n = some ((List.range n).map W) :=
  Store.readBlock_eq_some_iff.mpr ⟨by simp, fun j hj => by simp [h j hj, hj]⟩

/-- An entry of the block of the values of `W` is a value of `W`. -/
theorem vec_map_range [Inhabited K] {n o : ℕ} (W : ℕ → K) (ho : o < n) :
    vec ((List.range n).map W) o = W o := by
  simp [vec, ho]

/-- After a write of the cell `off + o`, and of scratch in another buffer, the cells hold `W`
updated at `o`. -/
theorem CellsHold.update {s s' : Store K} {b off n o : ℕ} {W : ℕ → K} {v : K} {w : ℕ × ℕ}
    (h : CellsHold s b off n W)
    (hfr : s.EqOff (Store.inBlock b (off + o) 1 ⊔ Store.inBlock w.1 w.2 1) s') (hw : w.1 ≠ b)
    (hv : s'.get b (off + o) = some v) : CellsHold s' b off n (Function.update W o v) := by
  intro o' ho'
  by_cases e : o' = o
  · subst e
    simpa using hv
  · rw [Function.update_of_ne e, hfr.get_eq, h o' ho']
    rintro (⟨-, h₁, h₂⟩ | ⟨h₁, -⟩)
    · omega
    · exact hw h₁.symm

/-- The offset of entry $(r, c)$ of a matrix of order $n$ stored by columns is in its block. -/
theorem mul_add_lt_mul_self {n c r : ℕ} (hc : c < n) (hr : r < n) : c * n + r < n * n :=
  calc c * n + r < c * n + n := by omega
    _ = (c + 1) * n := (Nat.succ_mul c n).symm
    _ ≤ n * n := Nat.mul_le_mul_right n hc

/-- Entry $(r, c)$ of a matrix of order $n$ stored by columns, read from its block. -/
theorem get_matrix_entry [Inhabited K] {s : Store K} {b off n c r : ℕ} {xs : List K}
    (h : s.readBlock b off (n * n) = some xs) (hc : c < n) (hr : r < n) :
    s.get b (off + c * n + r) = some (vec xs (c * n + r)) := by
  rw [Nat.add_assoc]
  exact Store.get_of_readBlock h (mul_add_lt_mul_self hc hr) default

/-- The cell of entry $(r, c)$ of a matrix of order $n$ stored by columns is in its block. -/
theorem inBlock_entry_le {b off n c r : ℕ} (hc : c < n) (hr : r < n) :
    Store.inBlock b (off + c * n + r) 1 ≤ Store.inBlock b off (n * n) := by
  rintro _ _ ⟨rfl, h₁, h₂⟩
  have := mul_add_lt_mul_self hc hr
  exact ⟨rfl, by omega, by omega⟩

/-- A cell of a matrix stored by columns, in the words that its block holds. -/
theorem CellsHold.get_entry {s : Store K} {b off n c r : ℕ} {W : ℕ → K}
    (h : CellsHold s b off (n * n) W) (hc : c < n) (hr : r < n) :
    s.get b (off + c * n + r) = some (W (c * n + r)) := by
  rw [Nat.add_assoc]
  exact h _ (mul_add_lt_mul_self hc hr)

/-- A write of one entry of a matrix stored by columns, and of scratch elsewhere, updates the
words its block holds. -/
theorem CellsHold.update_entry {s s' : Store K} {b off n c r : ℕ} {W : ℕ → K} {v : K}
    {w : ℕ × ℕ} (h : CellsHold s b off (n * n) W)
    (hfr : s.EqOff (Store.inBlock b (off + c * n + r) 1 ⊔ Store.inBlock w.1 w.2 1) s')
    (hw : w.1 ≠ b) (hv : s'.get b (off + c * n + r) = some v) :
    CellsHold s' b off (n * n) (Function.update W (c * n + r) v) := by
  rw [Nat.add_assoc] at hfr hv
  exact h.update hfr hw hv

/-- A prefix of cells, kept by a write off it, grows by the cell written next. -/
theorem CellsHold.extend {s s' : Store K} {F : Fp} {b off i : ℕ} {W : ℕ → K} {v : K}
    (h : CellsHold s b off i W) (hfr : s.EqOff F s') (hF : ∀ o < i, ¬ F b (off + o))
    (hv : s'.get b (off + i) = some v) :
    CellsHold s' b off (i + 1) (Function.update W i v) := by
  intro o ho
  by_cases e : o = i
  · subst e
    simpa using hv
  · have hoi : o < i := by omega
    rw [Function.update_of_ne e, hfr.get_eq (hF o hoi), h o hoi]

/-- The accumulation loop: for $k < N$, $q := a_k b_k$ into the scratch cell $w$ and
$c := c - q$ in place at the cell $z$. The factors are read at cells off $z$ and $w$, so they do
not change during the loop, and the accumulator ends with `mulSubWord`. The operands are given by
their evaluation in each round. -/
theorem writes_mulSubLoop [Has ScalarOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {ρ : Env} {m : Mem K} {bound : IExp} {N : ℕ}
    (hN : bound.eval ρ.idx = some N) {a b c t : Operand} {p q : ℕ → ℕ × ℕ} {z w : ℕ × ℕ}
    (ha : ∀ k < N, a.eval (ρ.pushIdx k) = some (p k))
    (hb : ∀ k < N, b.eval (ρ.pushIdx k) = some (q k))
    (hc : ∀ k < N, c.eval (ρ.pushIdx k) = some z)
    (ht : ∀ k < N, t.eval (ρ.pushIdx k) = some w)
    {A B : ℕ → K} {v : K}
    (hA : ∀ k < N, m.store.get (p k).1 (p k).2 = some (A k))
    (hB : ∀ k < N, m.store.get (q k).1 (q k).2 = some (B k))
    (hv : m.store.get z.1 z.2 = some v) (hzw : z.1 ≠ w.1)
    (hpz : ∀ k < N, p k ≠ z) (hqz : ∀ k < N, q k ≠ z)
    (hpw : ∀ k < N, (p k).1 ≠ w.1) (hqw : ∀ k < N, (q k).1 ≠ w.1)
    (hw : w.2 < m.store.len w.1) :
    Writes .total I τ
      (.loop bound (.seq (.call (Has.inj ScalarOp.mul) [] [a, b] [t])
        (.call (Has.inj ScalarOp.sub) [] [c, t] [c]))) ρ
      (Store.inBlock z.1 z.2 1 ⊔ Store.inBlock w.1 w.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some (mulSubWord M A B v N)) m := by
  have off : ∀ {x : ℕ × ℕ}, x ≠ z → x.1 ≠ w.1 →
      ¬ (Store.inBlock z.1 z.2 1 ⊔ Store.inBlock w.1 w.2 1) x.1 x.2 := by
    rintro ⟨x₁, x₂⟩ hxz hxw (⟨h₁, h₂, h₃⟩ | ⟨h₁, -⟩)
    · exact hxz (Prod.ext h₁ (by simp only at h₂ h₃ ⊢; omega))
    · exact hxw h₁
  refine writes_loop hN (fun _ => Store.inBlock z.1 z.2 1 ⊔ Store.inBlock w.1 w.2 1)
    (fun _ _ => le_rfl)
    (fun k m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some (mulSubWord M A B v k))
    ⟨rfl, hv⟩ ?_
  intro k hk m₁ hfr ⟨hpos₁, hz₁⟩
  have hA₁ := (hfr.get_eq (off (hpz k hk) (hpw k hk))).trans (hA k hk)
  have hB₁ := (hfr.get_eq (off (hqz k hk) (hqw k hk))).trans (hB k hk)
  have hlw : w.2 < m₁.store.len w.1 := by rw [hfr.len_eq]; exact hw
  refine Writes.seq_le (writes_call_bin (x := p k) (y := q k) (z := w) (hI .mul)
    (by simp [ha k hk, hb k hk]) (by simp [ht k hk]) trivial hA₁ hB₁ rfl
    fun _ => ⟨?_, hlw⟩) le_sup_right fun m₂ hfr₂ ⟨hpos₂, ht₂⟩ => ?_
  · simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get hA₁, Store.lt_length_of_get hB₁,
      Store.lt_length_of_lt_len hlw⟩
  have hz₂ : m₂.store.get z.1 z.2 = some (mulSubWord M A B v k) := by
    rw [hfr₂.get_eq]
    · exact hz₁
    · rintro ⟨h₁, -⟩
      exact hzw h₁
  have hlz₂ : z.2 < m₂.store.len z.1 := Store.lt_len_of_get hz₂
  refine Writes.mono (writes_call_bin (x := z) (y := w) (z := z) (hI .sub)
    (by simp [hc k hk, ht k hk]) (by simp [hc k hk]) trivial hz₂ ht₂ rfl
    fun _ => ⟨?_, hlz₂⟩) le_sup_left
    fun m₃ _ ⟨hpos₃, hz₃⟩ => ⟨hpos₃.trans (hpos₂.trans hpos₁), hz₃⟩
  simp only [Mem.live_cons, Mem.live_nil, and_true]
  exact ⟨Store.lt_length_of_get hz₂, Store.lt_length_of_get ht₂, Store.lt_length_of_get hz₂⟩

/-- The accumulation loop followed by a division of the accumulator by a cell $e$ off the
accumulator and the scratch. -/
theorem writes_mulSubDiv [Has ScalarOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {ρ : Env} {m : Mem K} {bound : IExp} {N : ℕ}
    (hN : bound.eval ρ.idx = some N) {a b c d t : Operand} {p q : ℕ → ℕ × ℕ} {z w e : ℕ × ℕ}
    (ha : ∀ k < N, a.eval (ρ.pushIdx k) = some (p k))
    (hb : ∀ k < N, b.eval (ρ.pushIdx k) = some (q k))
    (hc : c.eval ρ = some z) (hd : d.eval ρ = some e)
    (ht : ∀ k < N, t.eval (ρ.pushIdx k) = some w)
    {A B : ℕ → K} {v D : K}
    (hA : ∀ k < N, m.store.get (p k).1 (p k).2 = some (A k))
    (hB : ∀ k < N, m.store.get (q k).1 (q k).2 = some (B k))
    (hv : m.store.get z.1 z.2 = some v) (hD : m.store.get e.1 e.2 = some D) (hzw : z.1 ≠ w.1)
    (hpz : ∀ k < N, p k ≠ z) (hqz : ∀ k < N, q k ≠ z)
    (hpw : ∀ k < N, (p k).1 ≠ w.1) (hqw : ∀ k < N, (q k).1 ≠ w.1)
    (hez : e ≠ z) (hew : e.1 ≠ w.1) (hw : w.2 < m.store.len w.1) :
    Writes .total I τ
      (.seq (.loop bound (.seq (.call (Has.inj ScalarOp.mul) [] [a, b] [t])
        (.call (Has.inj ScalarOp.sub) [] [c, t] [c])))
        (.call (Has.inj ScalarOp.div) [] [c, d] [c])) ρ
      (Store.inBlock z.1 z.2 1 ⊔ Store.inBlock w.1 w.2 1)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get z.1 z.2 = some (M.div (mulSubWord M A B v N) D)) m := by
  refine Writes.seq_le (writes_mulSubLoop hI hN ha hb
    (fun k _ => Operand.eval_pushIdx hc k) ht hA hB hv hzw hpz hqz hpw hqw hw) le_rfl
    fun m₁ hfr ⟨hpos₁, hz₁⟩ => ?_
  have hD₁ : m₁.store.get e.1 e.2 = some D := by
    rw [hfr.get_eq]
    · exact hD
    · rintro (⟨h₁, h₂, h₃⟩ | ⟨h₁, -⟩)
      · exact hez (Prod.ext h₁ (by omega))
      · exact hew h₁
  have hlz := Store.lt_len_of_get hz₁
  refine Writes.mono (writes_call_bin (x := z) (y := e) (z := z) (hI .div)
    (by simp [hc, hd]) (by simp [hc]) trivial hz₁ hD₁ rfl fun _ => ⟨?_, hlz⟩) le_sup_left
    fun m₂ _ ⟨hpos₂, hz₂⟩ => ⟨hpos₂.trans hpos₁, hz₂⟩
  simp only [Mem.live_cons, Mem.live_nil, and_true]
  exact ⟨Store.lt_length_of_get hz₁, Store.lt_length_of_get hD₁, Store.lt_length_of_get hz₁⟩

/-- A row trace depends on the solution only at the indices it has passed. -/
theorem isSubstRowTrace_congr_solution {err : BinOp → ℝ → ℝ → Prop} {t : ℕ → ℕ → ℝ}
    {b x x' s : ℕ → ℝ} {i k : ℕ} (h : IsSubstRowTrace err t b x i k s)
    (hx : ∀ j < k, x j = x' j) : IsSubstRowTrace err t b x' i k s :=
  ⟨h.1, fun j hj => by simpa only [hx j hj] using h.2 j hj⟩

/-- The decoded accumulator is a row trace of substitution. -/
theorem isSubstRowTrace_mulSubWord {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    {t : ℕ → ℕ → ℝ} {b x : ℕ → ℝ} {A X : ℕ → K} {v : K} {i k : ℕ}
    (hA : ∀ j < k, dec (A j) = t i j) (hX : ∀ j < k, dec (X j) = x j) (hv : dec v = b i) :
    IsSubstRowTrace (fun _ => RelErr u) t b x i k (fun l => dec (mulSubWord M A X v l)) := by
  refine ⟨hv, fun j hj => ?_⟩
  simpa only [hA j hj, hX j hj] using relErr_mulSubWord hM A X v j

/-- The rows below `r` of a substitution in the order `σ` are traces, on the words `W`. -/
def SubstPrefix (u : ℝ) (dec : K → ℝ) (t : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (σ : ℕ → ℕ) (W : ℕ → K)
    (r : ℕ) : Prop :=
  ∀ l < r, ∃ s : ℕ → ℝ, IsSubstRowTrace (fun _ => RelErr u) t b (fun j => dec (W (σ j))) l l s ∧
    RelErr u (s l / t l l) (dec (W (σ l)))

/-- Writing the quotient of row `r` at `σ r` extends the prefix of rows that are traces. -/
theorem SubstPrefix.succ {M : Machine K} {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M)
    {T : ℕ → ℕ → K} {b : ℕ → ℝ} {σ : ℕ → ℕ} {W : ℕ → K} {r n : ℕ} {D : K}
    (h : SubstPrefix u dec (fun i j => dec (T i j)) b σ W r) (hr : r < n)
    (hinj : ∀ i < n, ∀ l < n, σ i = σ l → i = l) (hv : dec (W (σ r)) = b r)
    (hD : D = T r r) (hne : dec D ≠ 0) :
    SubstPrefix u dec (fun i j => dec (T i j)) b σ
      (Function.update W (σ r) (M.div (mulSubWord M (T r) (fun j => W (σ j)) (W (σ r)) r) D))
      (r + 1) := by
  have hkeep : ∀ j < r, Function.update W (σ r)
      (M.div (mulSubWord M (T r) (fun j => W (σ j)) (W (σ r)) r) D) (σ j) = W (σ j) :=
    fun j hj => Function.update_of_ne (fun e => by
      have := hinj j (by omega) r hr e
      omega) _ _
  intro l hl
  rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
  · obtain ⟨s, hs, he⟩ := h l hl
    refine ⟨s, isSubstRowTrace_congr_solution hs fun j hj => ?_, ?_⟩
    · simp only [hkeep j (by omega)]
    · simpa only [hkeep l hl] using he
  · refine ⟨_, isSubstRowTrace_mulSubWord hM (A := T l) (X := fun j => W (σ j)) (v := W (σ l))
      (fun _ _ => rfl) (fun j hj => by simp only [hkeep j hj]) hv, ?_⟩
    subst hD
    simp only [Function.update_self]
    exact relErr_of_abs_sub_le (unitRoundoff_nonneg hM) (hM.div _ _ hne)

/-- The loop of a substitution in the order `σ`: for $r < n$, row `r` is accumulated in place
at the cell `σ r` of `x`, from the coefficients $T_{rj}$, $j < r$, and the entries already
computed, and divided by $T_{rr} \ne 0$. The coefficients are read in cells off `x` and off the
scratch `w`. The block written is a trace of forward substitution in the order `σ`. -/
theorem writes_substLoop [Inhabited K] [Has ScalarOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {u : ℝ} {dec : K → ℝ} (hM : StdModel u dec M) {τ : Tape K}
    {ρ : Env} {m : Mem K} {bound inner : IExp} {n : ℕ} (hn : bound.eval ρ.idx = some n)
    (hinner : ∀ r < n, inner.eval (ρ.pushIdx r).idx = some r) {a b c d t : Operand}
    {σ : ℕ → ℕ} (hσ : ∀ r < n, σ r < n) (hinj : ∀ r < n, ∀ l < n, σ r = σ l → r = l)
    {x w : ℕ × ℕ} {p : ℕ → ℕ → ℕ × ℕ} {e : ℕ → ℕ × ℕ} {T : ℕ → ℕ → K} {xs : List K}
    (ha : ∀ r < n, ∀ j < r, a.eval ((ρ.pushIdx r).pushIdx j) = some (p r j))
    (hb : ∀ r < n, ∀ j < r, b.eval ((ρ.pushIdx r).pushIdx j) = some (x.1, x.2 + σ j))
    (hc : ∀ r < n, c.eval (ρ.pushIdx r) = some (x.1, x.2 + σ r))
    (hd : ∀ r < n, d.eval (ρ.pushIdx r) = some (e r))
    (ht : ∀ r < n, ∀ j < r, t.eval ((ρ.pushIdx r).pushIdx j) = some w)
    (hT : ∀ r < n, ∀ j < r, m.store.get (p r j).1 (p r j).2 = some (T r j))
    (hD : ∀ r < n, m.store.get (e r).1 (e r).2 = some (T r r))
    (hpx : ∀ r < n, ∀ j < r, (p r j).1 ≠ x.1) (hex : ∀ r < n, (e r).1 ≠ x.1)
    (hpw : ∀ r < n, ∀ j < r, (p r j).1 ≠ w.1) (hew : ∀ r < n, (e r).1 ≠ w.1) (hxw : x.1 ≠ w.1)
    (hw : w.2 < m.store.len w.1) (hxs : m.store.readBlock x.1 x.2 n = some xs)
    (hne : ∀ r < n, dec (T r r) ≠ 0) :
    Writes .total I τ
      (.loop bound (.seq (.loop inner (.seq (.call (Has.inj ScalarOp.mul) [] [a, b] [t])
        (.call (Has.inj ScalarOp.sub) [] [c, t] [c])))
        (.call (Has.inj ScalarOp.div) [] [c, d] [c]))) ρ
      (Store.inBlock x.1 x.2 n ⊔ Store.inBlock w.1 w.2 1)
      (fun m' => m'.pos = m.pos ∧ ∃ ys, m'.store.readBlock x.1 x.2 n = some ys ∧
        IsSubstTrace (fun _ => RelErr u) (fun r j => dec (T r j))
          (fun r => dec (vec xs (σ r))) n (fun r => dec (vec ys (σ r)))) m := by
  have hoff : ∀ {y : ℕ × ℕ}, y.1 ≠ x.1 → y.1 ≠ w.1 →
      ¬ (Store.inBlock x.1 x.2 n ⊔ Store.inBlock w.1 w.2 1) y.1 y.2 := by
    rintro y h₁ h₂ (⟨h, -⟩ | ⟨h, -⟩)
    · exact h₁ h
    · exact h₂ h
  refine (writes_loop hn (fun _ => Store.inBlock x.1 x.2 n ⊔ Store.inBlock w.1 w.2 1)
    (fun _ _ => le_rfl)
    (fun r m' => m'.pos = m.pos ∧ ∃ W, CellsHold m'.store x.1 x.2 n W ∧
      (∀ l, r ≤ l → l < n → W (σ l) = vec xs (σ l)) ∧
      SubstPrefix u dec (fun i j => dec (T i j)) (fun i => dec (vec xs (σ i))) σ W r)
    ⟨rfl, vec xs, CellsHold.of_readBlock hxs, fun _ _ _ => rfl, fun l hl => absurd hl (by omega)⟩
    ?_).mono le_rfl ?_
  · intro r hr m₁ hfr ⟨hpos₁, W, hW, horig, hpre⟩
    have hsr := hσ r hr
    have hwrite := writes_mulSubDiv (τ := τ) (m := m₁) hI (hinner r hr)
      (a := a) (b := b) (c := c) (d := d) (t := t) (p := p r)
      (q := fun j => (x.1, x.2 + σ j)) (z := (x.1, x.2 + σ r)) (w := w) (e := e r)
      (A := T r) (B := fun j => W (σ j)) (v := W (σ r)) (D := T r r)
      (ha r hr) (hb r hr) (hc r hr) (hd r hr) (ht r hr)
      (fun j hj => (hfr.get_eq (hoff (hpx r hr j hj) (hpw r hr j hj))).trans (hT r hr j hj))
      (fun j hj => hW _ (hσ j (by omega))) (hW _ hsr)
      ((hfr.get_eq (hoff (hex r hr) (hew r hr))).trans (hD r hr)) hxw
      (fun j hj e' => hpx r hr j hj (by simpa using congrArg Prod.fst e'))
      (fun j hj e' => by
        have h₂ : σ j = σ r := by simpa using congrArg Prod.snd e'
        have := hinj j (by omega) r hr h₂
        omega)
      (fun j hj => hpw r hr j hj)
      (fun j _ => hxw)
      (fun e' => hex r hr (by simpa using congrArg Prod.fst e')) (hew r hr)
      (by rw [hfr.len_eq]; exact hw)
    refine hwrite.mono (sup_le ?_ le_sup_right) fun m₂ hfr₂ ⟨hpos₂, hz₂⟩ => ⟨hpos₂.trans hpos₁,
      _, hW.update hfr₂ hxw.symm hz₂, fun l hl hln => ?_,
      hpre.succ hM hr hinj (by rw [horig r le_rfl hr]) rfl (hne r hr)⟩
    · rintro _ _ ⟨rfl, h₁, h₂⟩
      exact Or.inl ⟨rfl, by simp only at h₁; omega, by simp only at h₁ h₂; omega⟩
    · rw [Function.update_of_ne (fun e' => by
        have := hinj l hln r hr e'
        omega)]
      exact horig l (by omega) hln
  · rintro m₁ - ⟨hpos₁, W, hW, -, hpre⟩
    refine ⟨hpos₁, _, hW.readBlock, fun r hr => ?_⟩
    obtain ⟨s, hs, he⟩ := hpre r hr
    refine ⟨s, isSubstRowTrace_congr_solution hs fun j hj => ?_, ?_⟩
    · simp only [vec_map_range W (hσ j (by omega))]
    · simpa only [vec_map_range W (hσ r hr)] using he

end NLAlib.TriangularSolve
