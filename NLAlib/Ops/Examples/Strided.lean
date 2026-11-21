/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.RoutineSyntax
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.Catalog.Scalar

/-!
# Example: operands that are not contiguous

The block of an operand may be made of runs at a fixed period (`NLAlib.Ops.Port.stride`): a
vector with an increment, a row of a matrix stored by columns.

* `scalStrided` scales the `n` cells of a vector with increment `inc`, in place.
* `swapRows` exchanges two rows of a matrix stored by columns with leading dimension `lda`. The
  two rows are interleaved in one buffer; the routine is separated by block, and its judgment
  requires only that their cells differ.
* `swapMatrixRows` calls it on rows `i < j` of a matrix with `p` rows and `n` columns given as
  one contiguous block.

## Main definitions

* `NLAlib.Ops.Examples.Strided.scalStrided`, `NLAlib.Ops.Examples.Strided.swapRows`,
  `NLAlib.Ops.Examples.Strided.swapMatrixRows`: the routines.

## Main results

* `NLAlib.Ops.Examples.Strided.scalStrided_meets`, `NLAlib.Ops.Examples.Strided.swapRows_meets`,
  `NLAlib.Ops.Examples.Strided.swapMatrixRows_meets`: their judgments.
* `NLAlib.Ops.Examples.Strided.countPoly_scalStrided`,
  `NLAlib.Ops.Examples.Strided.countPoly_swapMatrixRows`: instruction counts, evaluated by the
  kernel.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Strided

variable {K Op Tst : Type} [Has ScalarOp Op]

/-! ### A vector with an increment -/

/-- Scale in place the `n` cells of `x`, one every `inc` cells: `x_k := x_k · a`. -/
def scalStrided : Routine Op Tst := routine% [n, inc] (a : 1, x : n every inc) → (x) {
  for i < n {
    call (Has.inj ScalarOp.mul) [] (x[inc * i], a) → (x[inc * i])
  }
}

/-- With a positive increment, the cells of the vector hold the products of the machine. -/
def scalStridedSpec (M : Machine K) : Routine.Spec K :=
  spec% [_n, inc] ([a], xs) → (ys) requires 0 < inc ensures ys = xs.map fun v => M.mul v a

/-- The strided scaling meets its specification. -/
theorem scalStrided_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (scalStrided (Op := Op) (Tst := Tst)).Meets I (scalStridedSpec M) := by
  routine_intro [n, inc] (al, x) reads (as, xs)
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  have hinc : 0 < inc := hpre
  obtain ⟨hxl, hxg⟩ := Store.readView_eq_some_iff.mp hxs
  have hxlen : xs.length = n := by simpa using hxl
  have hg : ∀ k < n, m.store.get x.1 (x.2 + inc * k) = xs[k]? := fun k hk => by
    simpa using hxg k (by simpa using hk)
  change Wp .total I τ _ _ _ m
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Fp.inView x.1 x.2 ⟨1, some (n, inc)⟩) s' ∧
    ∀ k < n, s'.get x.1 (x.2 + inc * k) =
      if k < i then (xs[k]?).map (fun v => M.mul v a) else xs[k]?)
    ⟨_, rfl, Store.EqOff.refl _ _, fun k hk => by simpa using hg k hk⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hcells⟩
    have hi' : i < xs.length := hxlen ▸ hi
    have hxi : s'.get x.1 (x.2 + inc * i) = some xs[i] := by
      rw [hcells i hi, if_neg (Nat.lt_irrefl i), List.getElem?_eq_getElem hi']
    have hal : s'.get al.1 al.2 = some a := by
      rw [← ha]
      exact hfr.get_eq fun h => halx (Fp.inView_apply.mp h).1
    refine wp_call_bin (hI .mul) rfl rfl rfl trivial hxi hal rfl (Store.lt_len_of_get hxi) ?_
    refine ⟨_, rfl, hfr.upd (Fp.inView_apply.mpr ⟨rfl, i, by simpa using hi, by simp⟩) _,
      fun k hk => ?_⟩
    by_cases hki : k = i
    · subst hki
      change (s'.upd x.1 (x.2 + inc * k) (M.mul xs[k] a)).get x.1 (x.2 + inc * k) = _
      rw [Store.get_upd_self (Store.lt_len_of_get hxi), if_pos (Nat.lt_succ_self k),
        List.getElem?_eq_getElem hi', Option.map_some]
    · have hne : x.2 + inc * k ≠ x.2 + inc * i := fun e =>
        hki (Nat.eq_of_mul_eq_mul_left hinc (Nat.add_left_cancel e))
      change (s'.upd x.1 (x.2 + inc * i) (M.mul xs[i] a)).get x.1 (x.2 + inc * k) = _
      rw [Store.get_upd_of_idx_ne hne, hcells k hk]
      by_cases hlt : k < i
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · rw [if_neg hlt, if_neg (by omega)]
  · rintro m' ⟨s', rfl, hfr, hcells⟩
    refine ⟨hfr.mono fun b i h => Or.inl h, rfl, [xs.map fun v => M.mul v a],
      Mem.readViews_of_cons (Store.readView_eq_some_iff.mpr ⟨by simpa using hxlen,
        fun k hk => ?_⟩) rfl, rfl⟩
    have hk' : k < n := by simpa using hk
    rw [View.offset_runs_one, List.getElem?_map]
    exact (hcells k hk').trans (if_pos hk')

/-! ### Two rows of a matrix stored by columns -/

/-- Exchange two rows of `n` entries of a matrix stored by columns with leading dimension `lda`:
entry `k` of a row is `lda * k` cells after its first. The rows may be rows of one matrix; they
are then interleaved in one buffer, which separation by block admits. -/
def swapRows : Routine Op Tst :=
  routine% [n, lda] (r : n every lda, s : n every lda) → (r, s) by blocks {
    let T ← alloc 1;
    for i < n {
      call (Has.inj ScalarOp.copy) [] (r[lda * i]) → (T);
      call (Has.inj ScalarOp.copy) [] (s[lda * i]) → (r[lda * i]);
      call (Has.inj ScalarOp.copy) [] (T) → (s[lda * i])
    }
  }

/-- With a positive leading dimension, each row holds the entries of the other. -/
def swapRowsSpec : Routine.Spec K :=
  spec% [_n, lda] (rs, ss) → (rs', ss') requires 0 < lda ensures rs' = ss ∧ ss' = rs

/-- The cells of the two rows after `i` exchanges: entries below `i` are exchanged. -/
def Swapped (st : Store K) (r s : ℕ × ℕ) (n lda : ℕ) (rs ss : List K) (i : ℕ) : Prop :=
  ∀ k < n, st.get r.1 (r.2 + lda * k) = (if k < i then ss[k]? else rs[k]?) ∧
    st.get s.1 (s.2 + lda * k) = (if k < i then rs[k]? else ss[k]?)

/-- One exchange: the three copies of round `i` exchange entry `i` and keep the others. -/
theorem Swapped.step {st : Store K} {r s : ℕ × ℕ} {n lda : ℕ} {rs ss : List K} {i L : ℕ}
    (h : Swapped st r s n lda rs ss i) (hi : i < n) (hlda : 0 < lda) {a b : K}
    (ha : st.get r.1 (r.2 + lda * i) = some a) (hb : st.get s.1 (s.2 + lda * i) = some b)
    (hra : rs[i]? = some a) (hsb : ss[i]? = some b) (hrL : r.1 ≠ L) (hsL : s.1 ≠ L)
    (hd : ∀ k < n, ∀ j < n, r.1 ≠ s.1 ∨ r.2 + lda * k ≠ s.2 + lda * j) :
    Swapped (((st.upd L 0 a).upd r.1 (r.2 + lda * i) b).upd s.1 (s.2 + lda * i) a) r s n lda
      rs ss (i + 1) := by
  intro k hk
  have hrlen : r.2 + lda * i < (st.upd L 0 a).len r.1 := by
    rw [Store.len_upd]
    exact Store.lt_len_of_get ha
  have hslen : s.2 + lda * i < ((st.upd L 0 a).upd r.1 (r.2 + lda * i) b).len s.1 := by
    rw [Store.len_upd, Store.len_upd]
    exact Store.lt_len_of_get hb
  by_cases hki : k = i
  · subst hki
    rw [if_pos (Nat.lt_succ_self k), if_pos (Nat.lt_succ_self k), hra, hsb]
    exact ⟨by rw [Store.get_upd_of_ne (hd k hk k hk), Store.get_upd_self hrlen],
      Store.get_upd_self hslen a⟩
  · have hne (o : ℕ) : o + lda * k ≠ o + lda * i := fun e =>
      hki (Nat.eq_of_mul_eq_mul_left hlda (Nat.add_left_cancel e))
    have hif {α : Type} (x y : α) : (if k < i + 1 then x else y) = if k < i then x else y := by
      by_cases hlt : k < i
      · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]
      · rw [if_neg hlt, if_neg (by omega)]
    rw [hif, hif]
    refine ⟨?_, ?_⟩
    · rw [Store.get_upd_of_ne (hd k hk i hi), Store.get_upd_of_idx_ne (hne r.2),
        Store.get_upd_of_buf_ne hrL]
      exact (h k hk).1
    · rw [Store.get_upd_of_idx_ne (hne s.2),
        Store.get_upd_of_ne ((hd i hi k hk).imp Ne.symm Ne.symm),
        Store.get_upd_of_buf_ne hsL]
      exact (h k hk).2

/-- The row exchange meets its specification, for every machine. -/
theorem swapRows_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (swapRows (Op := Op) (Tst := Tst)).Meets I swapRowsSpec := by
  routine_intro [n, lda] (r, s) reads (rs, ss)
  have hlda : 0 < lda := hpre
  have hdc : ∀ k < n, ∀ j < n, r.1 ≠ s.1 ∨ r.2 + lda * k ≠ s.2 + lda * j := fun k hk j hj =>
    Fp.Disj.ne_cells (fun b i h₁ h₂ => hblocks.1.1 b i h₁ (Or.inl h₂))
      (Fp.inView_apply.mpr ⟨rfl, k, by simpa using hk, by simp⟩)
      (Fp.inView_apply.mpr ⟨rfl, j, by simpa using hj, by simp⟩)
  obtain ⟨hrl, hrg⟩ := Store.readView_eq_some_iff.mp hrs
  obtain ⟨hsl, hsg⟩ := Store.readView_eq_some_iff.mp hss
  have hrlen : rs.length = n := by simpa using hrl
  have hslen : ss.length = n := by simpa using hsl
  have hrL : r.1 ≠ m.store.length := Nat.ne_of_lt hl.1
  have hsL : s.1 ≠ m.store.length := Nat.ne_of_lt hl.2
  refine writes_alloc rfl fun s₁ _ hlen₁ hbelow => ?_
  change Wp .total I τ _ _ _ _
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    s₁.EqOff (Fp.views [r, s] [⟨1, some (n, lda)⟩, ⟨1, some (n, lda)⟩] ⊔
      Store.inBuf m.store.length) s' ∧ Swapped s' r s n lda rs ss i)
    ⟨_, rfl, Store.EqOff.refl _ _, fun k hk => ?_⟩ ?_ ?_
  · rw [(hbelow r.1 hl.1).2, (hbelow s.1 hl.2).2, if_neg (Nat.not_lt_zero k),
      if_neg (Nat.not_lt_zero k)]
    exact ⟨by simpa using hrg k (by simpa using hk), by simpa using hsg k (by simpa using hk)⟩
  · rintro i hi m' ⟨s', rfl, hfr, hsw⟩
    have hi₁ : i < rs.length := hrlen ▸ hi
    have hi₂ : i < ss.length := hslen ▸ hi
    have ha : s'.get r.1 (r.2 + lda * i) = some rs[i] := by
      rw [(hsw i hi).1, if_neg (Nat.lt_irrefl i), List.getElem?_eq_getElem hi₁]
    have hb : s'.get s.1 (s.2 + lda * i) = some ss[i] := by
      rw [(hsw i hi).2, if_neg (Nat.lt_irrefl i), List.getElem?_eq_getElem hi₂]
    have hT : 0 < s'.len m.store.length := by
      rw [hfr.len_eq, hlen₁]
      exact Nat.one_pos
    have h₂ : (s'.upd m.store.length 0 rs[i]).get s.1 (s.2 + lda * i) = some ss[i] :=
      (Store.get_upd_of_buf_ne hsL _ _).trans hb
    have hz₂ : r.2 + lda * i < (s'.upd m.store.length 0 rs[i]).len r.1 := by
      rw [Store.len_upd]
      exact Store.lt_len_of_get ha
    have h₃ : ((s'.upd m.store.length 0 rs[i]).upd r.1 (r.2 + lda * i) ss[i]).get
        m.store.length 0 = some rs[i] := by
      rw [Store.get_upd_of_buf_ne (Ne.symm hrL)]
      exact Store.get_upd_self hT _
    have hz₃ : s.2 + lda * i <
        ((s'.upd m.store.length 0 rs[i]).upd r.1 (r.2 + lda * i) ss[i]).len s.1 := by
      rw [Store.len_upd, Store.len_upd]
      exact Store.lt_len_of_get hb
    refine wp_seq (wp_call_un (hI .copy) rfl rfl rfl trivial ha rfl hT ?_)
    refine wp_seq (wp_call_un (hI .copy) rfl rfl rfl trivial h₂ rfl hz₂ ?_)
    refine wp_call_un (hI .copy) rfl rfl rfl trivial h₃ rfl hz₃ ?_
    exact ⟨_, rfl, ((hfr.upd (Or.inr rfl) _).upd (Or.inl (Or.inl (Fp.inView_apply.mpr
      ⟨rfl, i, by simpa using hi, by simp⟩))) _).upd (Or.inl (Or.inr (Or.inl
        (Fp.inView_apply.mpr ⟨rfl, i, by simpa using hi, by simp⟩)))) _,
      hsw.step hi hlda ha hb (List.getElem?_eq_getElem hi₁) (List.getElem?_eq_getElem hi₂)
        hrL hsL hdc⟩
  · rintro m' ⟨s', rfl, hfr, hsw⟩
    refine ⟨hfr, fun s₂ _ hb₂ => ⟨rfl, [ss, rs], ?_, rfl, rfl⟩⟩
    refine Mem.readViews_of_cons (Store.readView_eq_some_iff.mpr ⟨by simpa using hslen,
      fun k hk => ?_⟩) (Mem.readViews_of_cons (Store.readView_eq_some_iff.mpr
        ⟨by simpa using hrlen, fun k hk => ?_⟩) rfl)
    · have hk' : k < n := by simpa using hk
      rw [View.offset_runs_one]
      exact ((hb₂ r.1 hl.1).2 _).trans (((hsw k hk').1).trans (if_pos hk'))
    · have hk' : k < n := by simpa using hk
      rw [View.offset_runs_one]
      exact ((hb₂ s.1 hl.2).2 _).trans (((hsw k hk').2).trans (if_pos hk'))

/-! ### Two rows of one matrix -/

variable [Inhabited K]

/-- The entries of row `t` of a matrix with `p` rows and `n` columns stored by columns. -/
def row (As : List K) (p n t : ℕ) : List K :=
  (List.range n).map fun c => As.getD (p * c + t) default

/-- The matrix stored by columns with rows `i` and `j` exchanged: entry `q` is in column `q / p`
and row `q % p`. -/
def swappedRows (As : List K) (p n i j : ℕ) : List K :=
  (List.range (p * n)).map fun q =>
    As.getD (p * (q / p) + (if q % p = i then j else if q % p = j then i else q % p)) default

omit [Has ScalarOp Op] [Inhabited K] in
/-- Entry `k` of row `t` is inside the block of the matrix. -/
theorem row_bound {p n t k : ℕ} (ht : t < p) (hk : k < n) : p * k + t < p * n := by
  have h := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hk)
  rw [Nat.mul_succ] at h
  omega

omit [Has ScalarOp Op] in
theorem getElem?_row (As : List K) (p t : ℕ) {n c : ℕ} (hc : c < n) :
    (row As p n t)[c]? = some (As.getD (p * c + t) default) := by
  rw [row, List.getElem?_map, List.getElem?_range hc, Option.map_some]

omit [Has ScalarOp Op] in
theorem getElem?_swappedRows (As : List K) (i j : ℕ) {p n q : ℕ} (hq : q < p * n) :
    (swappedRows As p n i j)[q]? = some (As.getD
      (p * (q / p) + (if q % p = i then j else if q % p = j then i else q % p)) default) := by
  rw [swappedRows, List.getElem?_map, List.getElem?_range hq, Option.map_some]

omit [Has ScalarOp Op] in
/-- A row of a matrix that is read as one block is read as a view of it. -/
theorem readView_row {st : Store K} {b off p n : ℕ} {As : List K}
    (h : st.readBlock b off (p * n) = some As) {t : ℕ} (ht : t < p) :
    st.readView b (off + t) ⟨1, some (n, p)⟩ = some (row As p n t) := by
  have hAl : As.length = p * n := Store.length_of_readBlock h
  refine Store.readView_of_readBlock h (by simp [row]) fun k hk => ?_
  have hk' : k < n := by simpa using hk
  have hb := row_bound ht hk'
  have hlt : t + p * k < As.length := by omega
  rw [View.offset_runs_one, getElem?_row As p t hk', List.getElem?_eq_getElem hlt,
    List.getD_eq_getElem?_getD, Nat.add_comm (p * k) t, List.getElem?_eq_getElem hlt,
    Option.getD_some]
  exact ⟨by omega, rfl⟩

omit [Has ScalarOp Op] [Inhabited K] in
/-- The cells of a row are cells of the block of the matrix. -/
theorem inView_row_le (b off n : ℕ) {p t : ℕ} (ht : t < p) :
    Fp.inView b (off + t) ⟨1, some (n, p)⟩ ≤ Store.inBlock b off (p * n) := by
  intro b' c h
  obtain ⟨rfl, k, hk, rfl⟩ := Fp.inView_apply.mp h
  have hb := row_bound ht (show k < n by simpa using hk)
  rw [View.offset_runs_one]
  exact ⟨rfl, by omega, by omega⟩

omit [Has ScalarOp Op] [Inhabited K] in
/-- An entry of another row is not a cell of the row. -/
theorem not_inView_row (b off n : ℕ) {p t q : ℕ} (ht : t < p) (hq : q % p ≠ t) :
    ¬ Fp.inView b (off + t) ⟨1, some (n, p)⟩ b (off + q) := by
  intro h
  obtain ⟨-, k, -, e⟩ := Fp.inView_apply.mp h
  rw [View.offset_runs_one] at e
  refine hq ?_
  rw [show q = t + p * k by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-- Exchange rows `i` and `j` of a matrix with `p` rows and `n` columns, stored by columns as
one block: the two rows are operands of `swapRows` at offsets `i` and `j` of the block, with
leading dimension `p`. -/
def swapMatrixRows : Routine Op Tst := routine% [p, n, i, j] (A : p * n) → (A) {
  run (swapRows (Op := Op) (Tst := Tst)) [n, p] (A[i], A[j])
}

/-- For rows `i < j < p`, the block holds the matrix with the two rows exchanged. -/
def swapMatrixRowsSpec : Routine.Spec K :=
  spec% [p, n, i, j] (As) → (As') requires i < j ∧ j < p ensures As' = swappedRows As p n i j

/-- The exchange of two rows of one matrix meets its specification. -/
theorem swapMatrixRows_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (swapMatrixRows (Op := Op) (Tst := Tst)).Meets I swapMatrixRowsSpec := by
  routine_intro [p, n, i, j] (A) reads (As)
  obtain ⟨hij, hjp⟩ : i < j ∧ j < p := hpre
  have hi : i < p := lt_trans hij hjp
  have hsw := swapRows_meets (Op := Op) (Tst := Tst) (M := M) hI
  have hfit : ∀ t < p, (⟨1, some (n, p)⟩ : View).Fits (A.2 + t) (m.store.len A.1) :=
    fun t ht k hk => by
      have hb := row_bound ht (show k < n by simpa using hk)
      rw [View.offset_runs_one]
      omega
  refine (hsw.call (d := [n, p]) (args := [(A.1, A.2 + i), (A.1, A.2 + j)])
    (xs := [row As p n i, row As p n j]) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_).mono ?_
    fun ν hfr ⟨hpos, ys, hys, hpost⟩ => ?_
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> exact hl
  · exact Routine.separatedAt_of_blocks rfl ⟨⟨fun b c h₁ h₂ => h₂.elim
      (Fp.disj_inView_of_residues (show i + 1 ≤ j by omega) (show j + 1 ≤ p by omega) b c h₁)
      False.elim, fun _ _ _ h => h, trivial⟩, fun _ _ _ h => h, trivial, fun _ _ h _ => h⟩
  · exact Mem.readViews_of_cons (readView_row hAs hi)
      (Mem.readViews_of_cons (readView_row hAs hjp) rfl)
  · change 0 < p
    omega
  · exact ⟨hfit i hi, hfit j hjp, trivial⟩
  · intro b c h
    have h' : Fp.inView A.1 (A.2 + i) ⟨1, some (n, p)⟩ b c ∨
        Fp.inView A.1 (A.2 + j) ⟨1, some (n, p)⟩ b c ∨ False := h
    rcases h' with h | h | h
    · exact Or.inl (inView_row_le A.1 A.2 n hi b c h)
    · exact Or.inl (inView_row_le A.1 A.2 n hjp b c h)
    · exact h.elim
  · have hys' : ν.readViews [(A.1, A.2 + i), (A.1, A.2 + j)]
        [⟨1, some (n, p)⟩, ⟨1, some (n, p)⟩] = some ys := hys
    obtain ⟨ri, Y, hri, hY, rfl⟩ := Mem.readViews_cons_eq_some.mp hys'
    obtain ⟨rj, Z, hrj, hZ, rfl⟩ := Mem.readViews_cons_eq_some.mp hY
    obtain rfl : [] = Z := Option.some.inj hZ
    obtain ⟨rfl, rfl⟩ : ri = row As p n j ∧ rj = row As p n i := hpost
    have hfr' : m.store.EqOff (Fp.inView A.1 (A.2 + i) ⟨1, some (n, p)⟩ ⊔
        (Fp.inView A.1 (A.2 + j) ⟨1, some (n, p)⟩ ⊔ ⊥)) ν.store := hfr
    refine ⟨hpos, [swappedRows As p n i j], Mem.readBlocks_of_cons
      (Store.readBlock_eq_some_iff.mpr ⟨by simp [swappedRows], fun q hq => ?_⟩) rfl, rfl⟩
    have hc : q / p < n := Nat.div_lt_of_lt_mul hq
    have hq' := Nat.div_add_mod q p
    rw [getElem?_swappedRows As i j hq]
    by_cases h1 : q % p = i
    · have h := Store.get_of_readView hri (k := q / p) (by simpa using hc)
      rw [View.offset_runs_one, getElem?_row As p j hc] at h
      rw [if_pos h1, show A.2 + q = A.2 + i + p * (q / p) by omega]
      exact h
    · by_cases h2 : q % p = j
      · have h := Store.get_of_readView hrj (k := q / p) (by simpa using hc)
        rw [View.offset_runs_one, getElem?_row As p i hc] at h
        rw [if_neg h1, if_pos h2, show A.2 + q = A.2 + j + p * (q / p) by omega]
        exact h
      · rw [if_neg h1, if_neg h2, hq', hfr'.get_eq (by
          rintro (h | h | h)
          · exact not_inView_row A.1 A.2 n hi h1 h
          · exact not_inView_row A.1 A.2 n hjp h2 h
          · exact h)]
        exact Store.get_of_readBlock hAs hq default

/-! ### Instruction counts

The count of a tree does not depend on where the cells of its operands are: a periodic operand
costs the same index arithmetic as any other offset. -/

/-- The instruction polynomial of the scaling of a vector with increment, evaluated by the
kernel: `16 n + 11`, whatever the increment. -/
theorem countPoly_scalStrided :
    ((scalStrided (Op := ScalarOp) (Tst := Empty)).close 2 2).countPoly =
      [(11, []), (16, [0])] := by
  rfl

/-- The instruction polynomial of the exchange of two rows of one matrix, evaluated by the
kernel: `34 n + 33` for `n` columns, whatever the leading dimension and the two rows. -/
theorem countPoly_swapMatrixRows :
    ((swapMatrixRows (Op := ScalarOp) (Tst := Empty)).close 4 1).countPoly =
      [(33, []), (34, [1])] := by
  rfl

end NLAlib.Ops.Examples.Strided
