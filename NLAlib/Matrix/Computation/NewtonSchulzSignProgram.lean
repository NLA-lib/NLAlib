/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSignProgram.Blocks

/-!
# The Newton–Schulz sign program computes `newtonSchulzSign`

The refinement of the program `NLAlib.newtonSchulzSignProg` to the shallow
`NLAlib.newtonSchulzSign`. Under any interpretation whose kernel `mm` is a routine on interleaved
pairs (`NLAlib.Computation.IsMatMulKernel`) and whose semantics decides flags, **every successful
run computes exactly `NLAlib.newtonSchulzSign` on the machine of the semantics and the routine**
(`NLAlib.Computation.ScalarSem.toFloatMachine`; the machine's other black boxes are arbitrary, since
the algorithm does not use them), and under the standard model with every value in range the run
succeeds when the machine's test passes within the step limit. The counts are bounded by
`NLAlib.newtonSchulzSignCount`.

## Main results

* `NLAlib.holds_of_exec_newtonSchulzSignProg`, `NLAlib.exists_exec_newtonSchulzSignProg`: the
  refinement (partial equality, success) for the builder from any state.
* `NLAlib.newtonSchulzSignProg.toStmt_compiled`,
  `NLAlib.newtonSchulzSignProg.holds_of_exec_compiled`,
  `NLAlib.newtonSchulzSignProg.exists_exec_compiled`,
  `NLAlib.newtonSchulzSignProg.cnt_le_of_exec_compiled`: the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- The scaling, the first test and the loop of `NLAlib.newtonSchulzSignProg`, from the state after
the four instructions. -/
private theorem nsH_tail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
    {σ st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {b η : K}
    (hA : pairLayout.Holds σ.store p A ao.eval A₀)
    (hb : σ.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hη : σ.store.read p t 0 = some η)
    (hone : σ.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : σ.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (Builder.run do
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))) σ =
        some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p X xo.eval (newtonSchulzLoop M η F (M.hermScale A₀ b)) ∧
      (∀ q b' i, b' ≠ t → b' ≠ W → b' ≠ V →
        blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = σ.store.read q b' i) ∧
      st'.store.shape = σ.store.shape ∧ st'.pos = σ.pos := by
  intro M
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hcY : blockDisjoint (par, po.eval + 1, 1) (X, xo.eval, 2 * (n * n)) = true := by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXp ⊢
    omega
  have htestc : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ' : St P K C),
      exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
        >>= f).run σ' = (exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩
          ⟨t, 0⟩ ⟨t, 1⟩).run σ').bind (exec I (f ()).run) :=
    exec_run_bind_newtonSchulzTestBlock
  rw [exec_run_bind I (b := zhermScale (ι := ι) p (.const n) A ao ⟨par, po + 1⟩ X xo)
    (fun _ => rfl)] at h
  obtain ⟨σ₅, h₅, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hX₅, hfr₅, hsh₅, hpos₅⟩ := holds_of_exec_zhermScale (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p n hA hb hXA hcY h₅
  have hr₅ : ∀ i, σ₅.store.read p t i = σ.store.read p t i := fun i => hfr₅ p t i (hd _ _ _ _ htX)
  rw [htestc] at h
  obtain ⟨σ₆, h₆, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hW₆, -, hf₆, hfr₆, hsh₆, hpos₆⟩ := holds_of_exec_newtonSchulzTestBlock
    (toNat := toNat) (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hX₅ ((hr₅ 3).trans hone) ((hr₅ 4).trans hlo)
    ((hr₅ 0).trans hη) hWX hWV (by simp [htW, htV])
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₆
  change exec I (.seq (.whileFuel _ _ _ _ _ _) .skip) σ₆ = some st' at h
  rw [exec_seq_skip] at h
  have hr₆ : ∀ i, i ≠ 1 → σ₆.store.read p t i = σ.store.read p t i := fun i h =>
    (hfr₆ p t i htW htV (blockDisjoint_cell_of_ne h)).trans (hr₅ i)
  obtain ⟨hX', hfr', hsh', hpos'⟩ := holds_of_exec_whileFuel_newtonSchulz hmm p hflag n
    (j := F) (fuel := .const F + 1) rfl
    (hX₅.of_forall_read_eq fun i _ _ => hfr₆ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm))
    hW₆ ((hr₆ 0 (by omega)).trans hη) ((hr₆ 3 (by omega)).trans hone)
    ((hr₆ 4 (by omega)).trans hlo) hf₆ hWX hVX hWV htX htW htV h
  refine ⟨hX', fun q b' i hbt hbW hbV hbX => ?_, hsh'.trans (hsh₆.trans hsh₅),
    hpos'.trans (hpos₆.trans hpos₅)⟩
  exact (hfr' q b' i hbt hbW hbV hbX).trans ((hfr₆ q b' i hbW hbV (hd _ _ _ _ hbt)).trans
    (hfr₅ q b' i hbX))

/-- The body of `NLAlib.newtonSchulzSignProg` inside its allocations. -/
private theorem nsH_setup {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (htA : n = 0 ∨ t ≠ A) (htp : t ≠ par)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (Builder.run do
      ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
      ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
      ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
      ins (.lit p ⟨t, 3⟩ 1)
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))) st =
        some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, b' ≠ t → b' ≠ W → b' ≠ V →
        blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  change exec I (.seq (.instr _) (.seq (.instr _) (.seq (.instr _) (.seq (.instr _)
    (.seq (.named _ _ _) (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩
      ⟨t, 1⟩ >>= fun _ => stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))).run)))))
    st = some st' at h
  obtain ⟨v, s₁, hv, hs₁, h⟩ := exists_of_exec_seq_litIdx h
  obtain ⟨a, c, w, s₂, ha, hc, hw, hs₂, h⟩ := exists_of_exec_seq_bin h
  obtain ⟨a', w', s₃, ha', hw', hs₃, h⟩ := exists_of_exec_seq_un h
  obtain ⟨o, s₄, ho, hs₄, h⟩ := exists_of_exec_seq_lit h
  change st.store.write p t 2 v = some s₁ at hs₁
  change s₁.write p t 0 w = some s₂ at hs₂
  change s₂.write p t 4 w' = some s₃ at hs₃
  change s₃.write p t 3 o = some s₄ at hs₄
  change s₁.read p par po.eval = some a at ha
  change s₁.read p t 2 = some c at hc
  change s₂.read p t 0 = some a' at ha'
  rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl (Ne.symm htp)), hε, Option.some_inj] at ha
  rw [Store.read_of_write_eq_some hs₁, Option.some_inj] at hc
  rw [Store.read_of_write_eq_some hs₂, Option.some_inj] at ha'
  subst ha hc ha'
  have hMη : (I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)) = w := by
    change (I.sem.bin p .div ε ((I.sem.lit p (((4 * n : ℕ)) : ℚ)).getD default)).getD default = w
    have hv' : I.sem.lit p (((4 * n : ℕ)) : ℚ) = some v := hv
    rw [hv', Option.getD_some, hw, Option.getD_some]
  have hMneg : (I.sem.toFloatMachine p toNat mmR qrR unif normal).neg w = w' := by
    change (I.sem.un p .neg w).getD default = w'; rw [hw']; rfl
  have hMone : (I.sem.toFloatMachine p toNat mmR qrR unif normal).one = o := by
    change (I.sem.lit p 1).getD default = o; rw [ho]; rfl
  have hfr₄ : ∀ q b i, b ≠ t → s₄.read q b i = st.store.read q b i := fun q b i h => by
    rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl h), Store.read_of_write_eq_some_of_ne hs₃
      (Or.inl h), Store.read_of_write_eq_some_of_ne hs₂ (Or.inl h),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl h)]
  have hsh₄ : s₄.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hs₄, Store.shape_of_write_eq_some hs₃,
      Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]
  obtain ⟨hX', hfr', hsh', hpos'⟩ := nsH_tail (toNat := toNat) (qrR := qrR) (unif := unif)
    (normal := normal) hmm p hflag n F (η := w)
    (σ := { st with store := s₄, cnt := _ })
    (by
      rcases htA with rfl | htA
      · exact fun i => i.elim0
      · exact hA.of_forall_read_eq fun i _ _ => hfr₄ _ _ _ htA.symm)
    ((hfr₄ _ _ _ htp.symm).trans hb)
    hXA hXp (by
      change s₄.read p t 0 = some w
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₂)
    (by rw [hMone]; exact Store.read_of_write_eq_some hs₄)
    (by
      change s₄.read p t 4 = _
      rw [hMneg, Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₃) hWX hVX hWV htX htW htV h
  refine ⟨?_, fun q b' i hbt hbW hbV hbX => (hfr' q b' i hbt hbW hbV hbX).trans
    (hfr₄ q b' i hbt), hsh'.trans hsh₄, hpos'⟩
  unfold newtonSchulzSign
  rw [hMη]
  exact hX'

/-- The refinement of the Newton–Schulz sign program, partial equality: if kernel `mm` of `I`
is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a successful
run of `NLAlib.newtonSchulzSignProg` at size $n$ and step limit $F$, from a state whose block at
`A` holds the stored $\mathbf{A}$ and whose cells `po`, `po + 1` of `par` hold $\varepsilon$ and
$b$, with the output block at `X` (an existing buffer at tag `p` of at least $2n^2$ cells from
`xo`, so not one of the program's scratch buffers) disjoint from both, ends with the output block
holding
$$\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$$
computed by `NLAlib.newtonSchulzSign` with step limit $F$ on the machine `M` of the semantics at
`p` with product `mmR` (for every choice of the machine's other black boxes, which the algorithm
does not use); every cell outside the output block is unchanged, the store shape and the tape
positions too. No printed source. -/
theorem holds_of_exec_newtonSchulzSignProg {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (h : exec I (newtonSchulzSignProg p mm (.const n) (.const F) A ao par po X xo).run st =
      some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hXlt : X < st.store.size := by
    obtain ⟨len, hXsh, -⟩ := hX
    have := (Array.getElem?_eq_some_iff.mp hXsh).1
    rwa [Store.size_shape] at this
  have hprog : (newtonSchulzSignProg p mm (.const n) (.const F) A ao par po X xo).run =
      .seq (.alloc p 5 fun t => .alloc p (2 * (.const n * .const n)) fun W =>
        .alloc p (2 * (.const n * .const n)) fun V => (Builder.run do
          ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
          ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
          ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
          ins (.lit p ⟨t, 3⟩ 1)
          zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
          stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
            newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
            newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)))) .skip :=
    rfl
  rw [hprog, exec_seq_skip, exec_alloc] at h
  obtain ⟨st₁, h, e₁⟩ := Option.map_eq_some_iff.mp h
  rw [exec_alloc] at h
  obtain ⟨st₂, h, e₂⟩ := Option.map_eq_some_iff.mp h
  rw [exec_alloc] at h
  obtain ⟨st₃, h₃, e₃⟩ := Option.map_eq_some_iff.mp h
  clear h
  subst e₁ e₂ e₃
  have hlt : ∀ {β i : ℕ} {v : K}, st.store.read p β i = some v → β < st.store.size :=
    fun h => Store.lt_size_of_read_eq_some h
  have hplt := hlt hε
  have hAn : n = 0 ∨ st.store.size ≠ A := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr (Nat.ne_of_gt (hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩)))
  have hA0 : pairLayout.Holds (((st.store.push (p, Array.replicate (IExp.eval 5) none)).push
      (p, Array.replicate (2 * (IExp.const n * IExp.const n)).eval none)).push
      (p, Array.replicate (2 * (IExp.const n * IExp.const n)).eval none)) p A ao.eval A₀ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact fun i => i.elim0
    · exact hA.of_forall_read_eq fun i _ _ =>
        Store.read_push_push_push_of_lt (hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩))
  obtain ⟨hX', hfr', hsh', hpos'⟩ := nsH_setup (toNat := toNat) (qrR := qrR) (unif := unif)
    (normal := normal) hmm p hflag n F hA0 ((Store.read_push_push_push_of_lt hplt).trans hε)
    ((Store.read_push_push_push_of_lt hplt).trans hb) hXA hXp hAn (by omega)
    (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by omega) (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (h := h₃)
  have hsz : st₃.store.size = st.store.size + 3 := by
    rw [Store.size_eq_of_shape_eq hsh']; simp
  refine ⟨hX'.of_forall_read_eq fun i _ _ => Store.read_pop_pop_pop_of_lt (by omega),
    fun q b' i hb' => ?_, ?_, ?_⟩
  · rcases Nat.lt_or_ge b' st.store.size with hb'' | hb''
    · rw [Store.read_pop_pop_pop_of_lt (by omega), hfr' q b' i (by omega)
        (by simp only [Array.size_push]; omega)
        (by simp only [Array.size_push]; omega) hb', Store.read_push_push_push_of_lt hb'']
    · rw [Store.read_eq_none_of_size_le (by simp; omega), Store.read_eq_none_of_size_le hb'']
  · change Store.shape (Array.pop (Array.pop (Array.pop st₃.store))) = _
    rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, hsh']
    simp [Store.shape]
  · exact hpos'

private theorem nsProg_body {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K} {st : St P K C} {S : Array (P × ℕ)}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A)) (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hS : st.store.shape = S) (hWS : S[W]? = some (p, 2 * (n * n)))
    (hVS : S[V]? = some (p, 2 * (n * n))) (htS : S[t]? = some (p, 5)) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    ∃ st₁, exec I (Builder.run do
      newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩) st =
        some st₁ ∧
      pairLayout.Holds st₁.store p X xo.eval (newtonSchulzRounded M A) ∧
      pairLayout.Holds st₁.store p W 0 (mmR (newtonSchulzRounded M A) (newtonSchulzRounded M A)) ∧
      st₁.store.read p t 0 = some η ∧ st₁.store.read p t 3 = some M.one ∧
      st₁.store.read p t 4 = some (M.neg η) ∧
      st₁.store.read p t 1 = some
        (if newtonSchulzTest M η (newtonSchulzRounded M A) then M.zero else M.one) ∧
      st₁.store.shape = S := by
  intro M
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hstep : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ : St P K C),
      exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩ >>= f).run σ =
        (exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩).run σ).bind
          (exec I (f ()).run) :=
    exec_run_bind_newtonSchulzStepBlock
  have hsh : ∀ {σ : St P K C} {b : ℕ} {l : ℕ}, σ.store.shape = S → S[b]? = some (p, l) →
      σ.store.shape[b]? = some (p, l) := fun h h' => by rw [h]; exact h'
  obtain ⟨σ, hσ⟩ := exists_exec_newtonSchulzStepBlock hmm hsem p hu n (c := ⟨t, 2⟩) hA hW hWX
    hVX hWV htW htV (hd _ _ _ _ htX) ⟨_, hsh hS hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hS htS) (by norm_num))
  obtain ⟨hXσ, hfrσ, hshσ, -⟩ := holds_of_exec_newtonSchulzStepBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n hA hW hWX hVX hWV htW htV
    (hd _ _ _ _ htX) hσ
  have hrσ : ∀ i, i ≠ 2 → σ.store.read p t i = st.store.read p t i := fun i hi =>
    hfrσ p t i htW htV (hd _ _ _ _ htX) (blockDisjoint_cell_of_ne hi)
  have hSσ := hshσ.trans hS
  obtain ⟨σ₁, h₁⟩ := exists_exec_newtonSchulzTestBlock hmm hsem p n (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hWV
    (by simp [htW, htV]) (by simp [blockDisjoint]) (by simp [blockDisjoint])
    ⟨_, hsh hSσ hWS, le_rfl⟩ ⟨_, hsh hSσ hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hSσ htS) (by norm_num))
  obtain ⟨hW₁, -, hf₁, hfr₁, hsh₁, -⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hWV
    (by simp [htW, htV]) (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₁
  have hr₁ : ∀ i, i ≠ 1 → i ≠ 2 → σ₁.store.read p t i = st.store.read p t i := fun i h1 h2 =>
    (hfr₁ p t i htW htV (blockDisjoint_cell_of_ne h1)).trans (hrσ i h2)
  exact ⟨σ₁, by rw [hstep, hσ, Option.bind_some]; exact h₁,
    hXσ.of_forall_read_eq fun i _ _ => hfr₁ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm),
    hW₁, (hr₁ 0 (by omega) (by omega)).trans hη, (hr₁ 3 (by omega) (by omega)).trans hone,
    (hr₁ 4 (by omega) (by omega)).trans hlo, hf₁, hsh₁.trans hSσ⟩

private theorem nsProg_loop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K} {S : Array (P × ℕ)}
    (hz : dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero ≠
      dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hWS : S[W]? = some (p, 2 * (n * n))) (hVS : S[V]? = some (p, 2 * (n * n)))
    (htS : S[t]? = some (p, 5)) (m : ℕ) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    ∀ (fuel : IExp ℕ) (st : St P K C) (A : Matrix (Fin n) (Fin n) (K × K)), fuel.eval = m + 1 →
      st.store.shape = S → pairLayout.Holds st.store p X xo.eval A →
      pairLayout.Holds st.store p W 0 (mmR A A) → st.store.read p t 0 = some η →
      st.store.read p t 3 = some M.one → st.store.read p t 4 = some (M.neg η) →
      st.store.read p t 1 = some (if newtonSchulzTest M η A then M.zero else M.one) →
      (∃ k ≤ m, newtonSchulzTest M η ((newtonSchulzRounded M)^[k] A) = true) →
      ∃ st', exec I (.whileFuel fuel p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)) st =
          some st' := by
  intro M
  have hstop : ∀ (fuel : IExp ℕ) (j : ℕ) (st : St P K C), fuel.eval = j + 1 →
      st.store.read p t 1 = some M.zero → st.store.read p t 3 = some M.one →
      ∃ st', exec I (.whileFuel fuel p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)) st =
          some st' := by
    intro fuel j st hfuel h1 h3
    rw [exec_whileFuel_of_eval_eq_succ I hfuel]
    have hz' : (dec p M.zero = dec p M.one) = False := eq_false hz
    simp only [cmpStep, IExp.eval_ofNat, h1, h3, Option.bind_some, hsem.cmp_eq, Option.map_some,
      hz', decide_false, Bool.false_eq_true, if_false]
    exact ⟨_, rfl⟩
  induction m with
  | zero =>
    intro fuel st A hfuel _ _ _ _ hone _ hf ⟨k, hk, htk⟩
    obtain rfl : k = 0 := by omega
    exact hstop fuel 0 st hfuel (by rw [hf, if_pos (by simpa using htk)]) hone
  | succ m ih =>
    intro fuel st A hfuel hS hA hW hη hone hlo hf ⟨k, hk, htk⟩
    by_cases ht : newtonSchulzTest M η A = true
    · exact hstop fuel _ st hfuel (by rw [hf, if_pos ht]) hone
    rw [exec_whileFuel_of_eval_eq_succ I hfuel]
    simp only [cmpStep, IExp.eval_ofNat, hf, if_neg ht, hone, Option.bind_some, hsem.cmp_eq,
      Option.map_some, decide_true, if_true]
    obtain ⟨σ₁, h₁, hX₁, hW₁, hη₁, hone₁, hlo₁, hf₁, hsh₁⟩ := nsProg_body hmm hsem p hu n
      (st := { st with cnt := st.cnt + I.charge (.cmp p) }) hA hW hη hone hlo hWX hVX hWV htX
      htW htV hS hWS hVS htS
    rw [h₁, Option.bind_some]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
      rcases k with _ | k
      · exact absurd htk ht
      · omega⟩
    exact ih (.const (m + 1)) σ₁ _ rfl hsh₁ hX₁ hW₁ hη₁ hone₁ hlo₁ hf₁
      ⟨k', by omega, by rwa [Function.iterate_succ_apply] at htk⟩

private theorem nsProg_tail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ} {σ : St P K C} {S : Array (P × ℕ)}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {b η : K}
    (hA : pairLayout.Holds σ.store p A ao.eval A₀)
    (hb : σ.store.read p par (po.eval + 1) = some b) (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, S[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (hη : σ.store.read p t 0 = some η)
    (hone : σ.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : σ.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hz : dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero ≠
      dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hS : σ.store.shape = S) (hWS : S[W]? = some (p, 2 * (n * n)))
    (hVS : S[V]? = some (p, 2 * (n * n))) (htS : S[t]? = some (p, 5))
    (htest : ∃ k ≤ F, newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal) η
      ((newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal))^[k]
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A₀ b)) = true) :
    ∃ st', exec I (Builder.run do
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))) σ =
        some st' := by
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hsh : ∀ {σ' : St P K C} {b : ℕ} {l : ℕ}, σ'.store.shape = S → S[b]? = some (p, l) →
      σ'.store.shape[b]? = some (p, l) := fun h h' => by rw [h]; exact h'
  have hcY : blockDisjoint (par, po.eval + 1, 1) (X, xo.eval, 2 * (n * n)) = true := by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXp ⊢
    omega
  obtain ⟨σ₅, h₅⟩ := exists_exec_zhermScale (I := I) (ι := ι) p n (X := A) (xo := ao)
    (c := ⟨par, po + 1⟩) (Y := X) (yo := xo) hA hb hXA hcY hsem hb0 (by rw [hS]; exact hX)
  obtain ⟨hX₅, hfr₅, hsh₅, -⟩ := holds_of_exec_zhermScale (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p n hA hb hXA hcY h₅
  have htestc : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ' : St P K C),
      exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
        >>= f).run σ' = (exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩
          ⟨t, 0⟩ ⟨t, 1⟩).run σ').bind (exec I (f ()).run) :=
    exec_run_bind_newtonSchulzTestBlock
  rw [exec_run_bind I (b := zhermScale (ι := ι) p (.const n) A ao ⟨par, po + 1⟩ X xo)
      (fun _ => rfl),
    h₅, Option.bind_some, htestc]
  have hr₅ : ∀ i, σ₅.store.read p t i = σ.store.read p t i := fun i => hfr₅ p t i (hd _ _ _ _ htX)
  have hS₅ := hsh₅.trans hS
  obtain ⟨σ₆, h₆⟩ := exists_exec_newtonSchulzTestBlock hmm hsem p n (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hX₅ ((hr₅ 3).trans hone) ((hr₅ 4).trans hlo)
    ((hr₅ 0).trans hη) hWX hWV (by simp [htW, htV])
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) ⟨_, hsh hS₅ hWS, le_rfl⟩
    ⟨_, hsh hS₅ hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hS₅ htS) (by norm_num))
  obtain ⟨hW₆, -, hf₆, hfr₆, hsh₆, -⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hX₅ ((hr₅ 3).trans hone) ((hr₅ 4).trans hlo)
    ((hr₅ 0).trans hη) hWX hWV (by simp [htW, htV])
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₆
  rw [h₆, Option.bind_some]
  change ∃ st', exec I (.seq (.whileFuel _ _ _ _ _ _) .skip) σ₆ = some st'
  rw [exec_seq_skip]
  have hr₆ : ∀ i, i ≠ 1 → σ₆.store.read p t i = σ.store.read p t i := fun i h =>
    (hfr₆ p t i htW htV (blockDisjoint_cell_of_ne h)).trans (hr₅ i)
  exact nsProg_loop hmm hsem p hu n hz hWX hVX hWV htX htW htV hWS hVS htS F (.const F + 1) σ₆ _
    rfl (hsh₆.trans hS₅)
    (hX₅.of_forall_read_eq fun i _ _ => hfr₆ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm))
    hW₆ ((hr₆ 0 (by omega)).trans hη) ((hr₆ 3 (by omega)).trans hone)
    ((hr₆ 4 (by omega)).trans hlo) hf₆ htest

private theorem nsProg_setup {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X t W V : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (htA : t ≠ A) (htp : t ≠ par)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hWS : st.store.shape[W]? = some (p, 2 * (n * n)))
    (hVS : st.store.shape[V]? = some (p, 2 * (n * n))) (htS : st.store.shape[t]? = some (p, 5))
    (htest : ∃ k ≤ F, newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal)
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)))
      ((newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal))^[k]
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A₀ b)) = true) :
    ∃ st', exec I (Builder.run do
      ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
      ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
      ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
      ins (.lit p ⟨t, 3⟩ 1)
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))) st =
        some st' := by
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  change ∃ st', exec I (.seq (.instr _) (.seq (.instr _) (.seq (.instr _) (.seq (.instr _)
    (.seq (.named _ _ _) (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩
      ⟨t, 1⟩ >>= fun _ => stmt (.whileFuel (.const F + 1) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩))).run)))))
    st = some st'
  -- the literal `4n`, the threshold, its negation and the literal `1`
  obtain ⟨v, hv⟩ := hsem.lit_ok p (((4 * IExp.const n).eval : ℕ) : ℚ) trivial
  have hv0 : dec p v ≠ 0 := by
    obtain ⟨δ, hδ, hdec⟩ := hsem.lit_err p _ v hv
    rw [hdec]
    refine mul_ne_zero (by simp; omega) ?_
    linarith [(abs_lt.mp (hδ.trans_lt hu)).1]
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape v htS (show 2 < 5 by norm_num)
  obtain ⟨w, hw⟩ := hsem.bin_ok p .div ε v trivial (fun _ => hv0) trivial
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape w
    (by rw [Store.shape_of_write_eq_some hs₁]; exact htS) (show 0 < 5 by norm_num)
  obtain ⟨w', hw', -⟩ := hsem.neg p w
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape w'
    (by rw [Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]; exact htS)
    (show 4 < 5 by norm_num)
  obtain ⟨o, ho, ho1⟩ := hlit p 1 le_rfl
  have ho' : I.sem.lit p 1 = some o := by simpa using ho
  obtain ⟨s₄, hs₄⟩ := Store.exists_write_eq_some_of_getElem?_shape o
    (by rw [Store.shape_of_write_eq_some hs₃, Store.shape_of_write_eq_some hs₂,
      Store.shape_of_write_eq_some hs₁]; exact htS) (show 3 < 5 by norm_num)
  rw [exec_seq_instr_litIdx I (dst := ⟨t, 2⟩) hv hs₁,
    exec_seq_instr_bin I (dst := ⟨t, 0⟩) (x := ⟨par, po⟩) (y := ⟨t, 2⟩)
      ((Store.read_of_write_eq_some_of_ne hs₁ (Or.inl htp.symm)).trans hε)
      (Store.read_of_write_eq_some hs₁) hw hs₂,
    exec_seq_instr_un I (dst := ⟨t, 4⟩) (x := ⟨t, 0⟩) (Store.read_of_write_eq_some hs₂) hw' hs₃,
    exec_seq_instr_lit I (dst := ⟨t, 3⟩) ho' hs₄]
  -- the machine's values of the cells
  have hM4 : (I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n) = v := by
    change (I.sem.lit p (((4 * IExp.const n).eval : ℕ) : ℚ)).getD default = v
    rw [hv]; rfl
  have hMη : (I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)) = w := by
    rw [hM4]; change (I.sem.bin p .div ε v).getD default = w; rw [hw]; rfl
  have hMneg : (I.sem.toFloatMachine p toNat mmR qrR unif normal).neg w = w' := by
    change (I.sem.un p .neg w).getD default = w'; rw [hw']; rfl
  have hMone : (I.sem.toFloatMachine p toNat mmR qrR unif normal).one = o := by
    change (I.sem.lit p 1).getD default = o; rw [ho']; rfl
  obtain ⟨z, hz⟩ := hsem.lit_ok p 0 trivial
  have hMzero : (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero = z := by
    change (I.sem.lit p 0).getD default = z; rw [hz]; rfl
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, h⟩ := hsem.lit_err p 0 z hz
    simpa using h
  have hfr₄ : ∀ q b i, b ≠ t → s₄.read q b i = st.store.read q b i := fun q b i h => by
    rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl h), Store.read_of_write_eq_some_of_ne hs₃
      (Or.inl h), Store.read_of_write_eq_some_of_ne hs₂ (Or.inl h),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl h)]
  have hsh₄ : s₄.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hs₄, Store.shape_of_write_eq_some hs₃,
      Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]
  obtain ⟨k, hk, htk⟩ := htest
  rw [hMη] at htk
  exact nsProg_tail hmm hsem p hu n F (S := st.store.shape) (η := w)
    (hA.of_forall_read_eq fun i _ _ => hfr₄ _ _ _ htA.symm) ((hfr₄ _ _ _ htp.symm).trans hb) hb0
    hXA hXp hX (by
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₂)
    (by rw [hMone]; exact Store.read_of_write_eq_some hs₄)
    (by rw [hMneg, Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num))]
        exact Store.read_of_write_eq_some hs₃)
    (by rw [hMzero, hMone, hdz, ho1]; norm_num) hWX hVX hWV htX htW htV hsh₄ hWS hVS htS
    ⟨k, hk, htk⟩

/-- The refinement of the Newton–Schulz sign program, success: under the standard model at
$u$ with every value in range, $u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the
routine `mmR` on interleaved pairs, $n \ge 1$, $b$ decodes to a nonzero value, the output block at
`X` (tag `p`) has $2n^2$ cells, and the machine's test passes at some iterate $k \le F$ of the
rounded step from `M.hermScale A b`, then the run of `NLAlib.newtonSchulzSignProg` at step limit
$F$ succeeds (hypotheses on the inputs as `NLAlib.holds_of_exec_newtonSchulzSignProg`). No
printed source. -/
theorem exists_exec_newtonSchulzSignProg {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (htest : ∃ k ≤ F, newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal)
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)))
      ((newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal))^[k]
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A₀ b)) = true) :
    ∃ st', exec I (newtonSchulzSignProg p mm (.const n) (.const F) A ao par po X xo).run st =
      some st' := by
  have hlt : ∀ {β i : ℕ} {v : K}, st.store.read p β i = some v → β < st.store.size :=
    fun h => Store.lt_size_of_read_eq_some h
  have hAlt := hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩)
  have hplt := hlt hε
  have hXlt : X < st.store.size := by
    obtain ⟨len, hXsh, -⟩ := hX
    have := (Array.getElem?_eq_some_iff.mp hXsh).1
    rwa [Store.size_shape] at this
  change ∃ st', exec I (.seq (.alloc p 5 _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine Option.exists_map_eq_some ?_
  change ∃ a, exec I (.alloc p _ _) _ = some a
  rw [exec_alloc]
  refine Option.exists_map_eq_some ?_
  change ∃ a, exec I (.alloc p _ _) _ = some a
  rw [exec_alloc]
  refine Option.exists_map_eq_some ?_
  obtain ⟨htS, hWS, hVS⟩ := Store.getElem?_shape_push_push_push st.store p (IExp.eval 5)
    (IExp.eval (2 * (.const n * .const n))) (IExp.eval (2 * (.const n * .const n)))
  have hP : ∀ {β : ℕ} (q : P) (i : ℕ), β < st.store.size → _ := fun {β} q i h =>
    And.intro (Store.read_push_push_push_of_lt (s := st.store) (p := p) (q := q)
      (a := IExp.eval 5) (b := (2 * (IExp.const n * .const n)).eval)
      (c := (2 * (IExp.const n * .const n)).eval) (i := i) h)
      (Store.getElem?_shape_push_push_push_of_lt (s := st.store) (p := p)
      (a := IExp.eval 5) (b := (2 * (IExp.const n * .const n)).eval)
      (c := (2 * (IExp.const n * .const n)).eval) h)
  exact nsProg_setup hmm hsem hlit p hu n F hn
    (hA.of_forall_read_eq fun i _ _ => (hP p i hAlt).1) ((hP p _ hplt).1.trans hε)
    ((hP p _ hplt).1.trans hb) hb0 hXA hXp (by rw [(hP p 0 hXlt).2]; exact hX)
    (by omega) (by omega) (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by omega) (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by simpa using hWS) (by simpa using hVS) (by simpa using htS) htest

/-! ### The registered tree -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The registered tree instantiates to the builder: at the sizes $N$ and $(F)$ the tree
`NLAlib.newtonSchulzSignProg.compiled` is `NLAlib.newtonSchulzSignProg` on the declared buffers
$0$, $1$, $2$ from offset $0$. No printed source. -/
theorem newtonSchulzSignProg.toStmt_compiled (p : P) (mm : ι) (N : ℕ) (n : Fin 1 → ℕ) :
    (newtonSchulzSignProg.compiled p mm).toStmt N n =
      ProgFamily.inst (r := 1) (b := 3) (fun _ _ N n h =>
        (newtonSchulzSignProg p mm N (n 0) (h 0) 0 (h 1) 0 (h 2) 0).run) N n := by
  rfl

/-- The registered tree computes `newtonSchulzSign`: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run of the tree
`NLAlib.newtonSchulzSignProg.compiled` at the sizes $N$ and $(F)$ from the initial state with the
stored $\mathbf{A}$, the stored $\varepsilon$, $b$ and $2N^2$ empty cells as declared buffers
ends with declared buffer $2$ holding $\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$ on
the machine of the semantics with product `mmR`, step limit $F$. No printed source. -/
theorem newtonSchulzSignProg.holds_of_exec_compiled {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (hflag : I.sem.DecidesFlags p) (N F : ℕ)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (ε b : K) {st' : St P K C}
    (h : (newtonSchulzSignProg.compiled p mm).exec I N ![F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some ε, some b],
        Array.replicate (2 * (N * N)) none]) = some st') :
    pairLayout.Holds st'.store p 2 0
      (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) := by
  rw [Prog.exec_eq_exec_toStmt, newtonSchulzSignProg.toStmt_compiled] at h
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some, #[some ε, some b],
    Array.replicate (2 * (N * N)) none] with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  have hε : (inputState (C := C) p bufs).store.read p 1 0 = some ε := by
    simp [inputState, Store.read, bufs]
  have hb1 : (inputState (C := C) p bufs).store.read p 1 (0 + 1) = some b := by
    simp [inputState, Store.read, bufs]
  have h' : exec I (newtonSchulzSignProg p mm (.const N) (.const F) 0 0 1 0 2 0).run
      (inputState p bufs) = some st' := h
  exact (holds_of_exec_newtonSchulzSignProg hmm p hflag N F hA hε hb1
    (by simp [blockDisjoint]) (by simp [blockDisjoint])
    ⟨2 * (N * N), by simp [inputState, Store.shape, bufs], by simp⟩ h').1

/-- The registered tree succeeds under the standard model at $u$ with every value in range,
$u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, $N \ge 1$, $b$ decodes to a nonzero value and the machine's test passes at some iterate
$k \le F$ (as `NLAlib.exists_exec_newtonSchulzSignProg`), from the initial state of
`NLAlib.newtonSchulzSignProg.holds_of_exec_compiled`. No printed source. -/
theorem newtonSchulzSignProg.exists_exec_compiled {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 1)
    (p : P) (hu : u p < 1) (N F : ℕ) (hN : 0 < N) (A₀ : Matrix (Fin N) (Fin N) (K × K))
    (ε b : K) (hb0 : dec p b ≠ 0)
    (htest : ∃ k ≤ F, newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal)
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * N)))
      ((newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal))^[k]
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A₀ b)) = true) :
    ∃ st' : St P K C, (newtonSchulzSignProg.compiled p mm).exec I N ![F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some ε, some b],
        Array.replicate (2 * (N * N)) none]) = some st' := by
  rw [Prog.exec_eq_exec_toStmt, newtonSchulzSignProg.toStmt_compiled]
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (k := 0) (Y := A₀)
    (bufs := [(pairLayout.toArray A₀).map some, #[some ε, some b],
      Array.replicate (2 * (N * N)) none]) rfl
  have hε : (inputState (C := C) p [(pairLayout.toArray A₀).map some, #[some ε, some b],
      Array.replicate (2 * (N * N)) none]).store.read p 1 0 = some ε := by
    simp [inputState, Store.read]
  have hb : (inputState (C := C) p [(pairLayout.toArray A₀).map some, #[some ε, some b],
      Array.replicate (2 * (N * N)) none]).store.read p 1 (0 + 1) = some b := by
    simp [inputState, Store.read]
  obtain ⟨st', h⟩ := exists_exec_newtonSchulzSignProg hmm hsem hlit p hu N F hN
    (A := 0) (par := 1) (X := 2) (ao := .const 0) (po := .const 0) (xo := .const 0)
    (A₀ := A₀) (ε := ε) (b := b) hA hε hb hb0
    (by simp [blockDisjoint]) (by simp [blockDisjoint])
    ⟨2 * (N * N), by simp [inputState, Store.shape], by simp⟩ htest
  exact ⟨st', h⟩

/-- Twice the sum of the indices below $N$ is at most $N^2$. -/
private theorem two_mul_sum_range_le (N : ℕ) : 2 * (List.range N).sum ≤ N * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.sum_append, List.sum_singleton]
    nlinarith

omit [Inhabited K] in
/-- The counts and the memory of the registered tree: under the standard charge (one per
operation), every successful run of `NLAlib.newtonSchulzSignProg.compiled` at the sizes $N$ and
$(F)$ adds at most `NLAlib.newtonSchulzSignCount p mm N F` to the counts and raises the peak
memory at tag `p` by at most the $4N^2 + 5$ scratch cells above the current memory (by nothing at
any other tag). No printed source. -/
theorem newtonSchulzSignProg.cnt_le_of_exec_compiled {mm : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : IsUnitCharge I) (p : P) (N F : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (newtonSchulzSignProg.compiled p mm).exec I N ![F] st = some st') :
    st'.cnt ≤ st.cnt + newtonSchulzSignCount p mm N F ∧
      ∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + if q = p then 4 * (N * N) + 5 else 0) := by
  have hb := (newtonSchulzSignProg.compiled p mm).bounds_staticCost_of_exec_eq_some I N ![F] h
  have hcharge : I.charge = fun k => Finsupp.single k 1 := hc.charge_eq
  have hb' := hb.mono (b := ⟨newtonSchulzSignCount p mm N F,
    fun q => if q = p then 4 * (N * N) + 5 else 0, _⟩) ?_ ?_ le_rfl
  · exact ⟨hb'.count, hb'.peak⟩
  · rw [hcharge]
    intro k
    change (FStmt.staticCost (fun k => Finsupp.single k 1) I.width
      (newtonSchulzSignProg.compiled (ι := ι) p mm) (Fin.cons N ![F])).count k ≤ _
    change (StaticCost.seq _ _).count k ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.branch, StaticCost.alloc,
      StaticCost.step, StaticCost.zero, StaticCost.repetitions, StaticCost.sequence_count_apply,
      Instr.kind, Instr.subst, IExp.evalIn, Finsupp.add_apply, Finsupp.sup_apply,
      Finsupp.smul_apply, List.map_const', List.sum_replicate, List.length_range,
      Finsupp.zero_apply]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, Fin.cons_one,
      Matrix.Fin.cons_vecCons, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
      Matrix.cons_val_fin_one, Fin.val_eq_zero, Fin.mk_one, add_zero, zero_add, smul_eq_mul,
      List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    have h2 : ∀ x : ℕ, ![N, F, x] ⟨2, by omega⟩ = x := fun _ => rfl
    simp only [h2, IExp.evalIn, Matrix.cons_val_zero, newtonSchulzSignCount, Finsupp.smul_apply,
      Finsupp.add_apply, smul_eq_mul, List.sum_map_mul_right, List.map_id']
    have hS := two_mul_sum_range_le N
    generalize (List.range N).sum = S at hS ⊢
    have hFS := Nat.mul_le_mul_left F hS
    classical
    cases k <;> simp only [Finsupp.single_apply, OpKind.bin.injEq, OpKind.un.injEq,
      OpKind.lit.injEq, OpKind.cmp.injEq, OpKind.copy.injEq, OpKind.kcall.injEq, reduceCtorEq,
      ite_false, mul_zero, add_zero, zero_add, max_self, Nat.zero_max, Nat.max_zero, le_refl]
    all_goals split_ifs <;> nlinarith [hS, hFS]
  · intro q
    change (FStmt.staticCost I.charge I.width
      (newtonSchulzSignProg.compiled (ι := ι) p mm) (Fin.cons N ![F])).cells q ≤ _
    change (StaticCost.seq _ _).cells q ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.branch,
      StaticCost.step, StaticCost.zero, StaticCost.repetitions, IExp.evalIn, Instr.kind,
      Instr.subst]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero,
      Matrix.Fin.cons_vecCons, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
      StaticCost.sequence_cells_mk, List.range_eq_nil, max_self, add_zero, Nat.max_zero,
      ite_self]
    split_ifs <;> omega

end NLAlib
