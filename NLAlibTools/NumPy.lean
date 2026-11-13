/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.Float
import NLAlib.Matrix.Computation.DeflationProgramTree

/-!
# Printing first-order programs as NumPy

The emitter prints a first-order tree (`NLAlib.Computation.FStmt`), so the code emitted for a
result is printed from the very tree the result is about: a registered tree such as
`NLAlib.hutchppProg.compiled` (`docs/design/Computation.md`, F1 and F11 step C). Variables are de
Bruijn levels: handle `j` is printed `b{j}` and index variable `j` is printed `i{j}`, so the free
variables of a program `Prog P ι r b` are the parameters of the emitted function: the oracle
dimension `i0`, the sizes `i1`, …, `i{r}` and the declared buffers `b0`, …, `b{b-1}`. An `alloc`
in scope of `nb` handles binds `b{nb}`, a `loop` in scope of `ni` indices binds `i{ni}`. Index
expressions are printed as Python arithmetic. `named` kernels are printed as calls into a short
NumPy prelude (`NLAlibTools.numpyPrelude`), or inlined. Fresh buffers use `np.full(len, np.nan, dtype=...)`,
so a read before a write shows as `nan`. The default dtype is inferred from `A` and the declared
buffers, promoted to at least float64. `scalarDtype` overrides it per precision tag when complex
or wider values enter through other hooks. The emitted code is an unverified translation, for
differential testing (`docs/design/Computation.md` §8): below, the emitted Hutch++ runs under
NumPy, when it is installed, and agrees with the Lean `Float` run of the same tree.
An index binder raises `ValueError` on a failed conversion or a floor above its bound, matching
the strict binder in the model.
For a subsingleton identifier type, oracle `apply` defaults to the square NumPy matrix `A`.
Other identifier types require an explicit `oracleName` binding to a matrix expression (for
example, `A` or `operators[0]`). Missing bindings raise `NotImplementedError`. Distinct
identifiers are dispatched separately, including an operator and its adjoint.
Oracle writes reject incompatible scalar kinds, including complex results into real buffers;
use a complex scratch dtype and an explicit real-part instruction when that conversion is intended.
Emitted black-box kernel calls require an explicit `kernelName` binding from each kernel identifier
to a Python callable expression. An unbound call raises `NotImplementedError`; different
kernel identifiers are never silently replaced by one anonymous callback. A non-inlined `named`
node calls its external implementation instead of emitting its body; that implementation remains
responsible for any internal kernel calls.
-/

-- A tools file: `#eval` and `#guard` are its point.
set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

/-- An index variable. -/
def idxName {ni : ℕ} (v : Fin ni) : String := s!"i{v.val}"

/-- A handle. -/
def bufName {nb : ℕ} (v : Fin nb) : String := s!"b{v.val}"

/-- An index expression as Python arithmetic: subtraction truncates at zero and a remainder
by zero is its dividend, matching `Nat.mod`. -/
def emitIExp {ni : ℕ} : IExp (Fin ni) → String
  | .var v => idxName v
  | .const n => toString n
  | .add a b => s!"({emitIExp a} + {emitIExp b})"
  | .sub a b => s!"max({emitIExp a} - {emitIExp b}, 0)"
  | .mul a b => s!"({emitIExp a} * {emitIExp b})"
  | .mod a b => s!"(lambda a, b: a % b if b else a)({emitIExp a}, {emitIExp b})"

/-- A cell as a Python subscript. -/
def emitCell {nb ni : ℕ} (c : Cell (Fin nb) (Fin ni)) : String :=
  s!"{bufName c.buf}[{emitIExp c.idx}]"

/-- A kernel argument. -/
def emitArg {nb ni : ℕ} : Arg (Fin nb) (Fin ni) → String
  | .buf v => bufName v
  | .idx e => emitIExp e
  | .cell c => s!"{bufName c.buf}, {emitIExp c.idx}"

/-- A comparison operator. -/
def emitCmp : CmpOp → String
  | .eq => "==" | .lt => "<" | .le => "<="

/-- Indentation. -/
def pad (n : ℕ) : String := String.ofList (List.replicate (4 * n) ' ')

/-- A scalar instruction as a Python assignment. -/
def emitInstr {P : Type} {nb ni : ℕ} : Instr P (Fin nb) (Fin ni) → String
  | .lit _ dst q => s!"{emitCell dst} = {q.num} / {q.den}"
  | .litIdx _ dst e => s!"{emitCell dst} = float({emitIExp e})"
  | .bin _ b dst x y =>
      let o := match b with
        | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .shl => "<<" | .shr => ">>"
        | .band => "&" | .bor => "|" | .bxor => "^"
      s!"{emitCell dst} = {emitCell x} {o} {emitCell y}"
  | .un _ u dst x =>
      let f := match u with
        | .neg => s!"-{emitCell x}" | .conj => s!"np.conj({emitCell x})"
        | .re => s!"np.real({emitCell x})" | .sqrt => s!"np.sqrt({emitCell x})"
        | .bnot => s!"~{emitCell x}"
      s!"{emitCell dst} = {f}"
  | .copy _ dst src => s!"{emitCell dst} = {emitCell src}"
  | .convert _ _ dst src => s!"{emitCell dst} = {emitCell src}"
  | .draw _ dist dst =>
      let f := match dist with
        | .gaussian => "draw_gaussian()" | .rademacher => "draw_rademacher()"
        | .uniform => "draw_uniform()"
      s!"{emitCell dst} = {f}"

/-- A first-order statement as Python lines at depth `d`. A black-box call uses its explicit
`kernelName` binding to a trusted Python callable expression, or raises `NotImplementedError`
when reached. The caller supplies bindings and implementations matching each kernel. -/
private def emitFWith {P ι : Type} (inline : Bool) {nb ni : ℕ} (s : FStmt P ι nb ni) (d : ℕ)
    (kernelName : ι → Option String := fun _ => none)
    (oracleName : ι → Option String := fun _ => none)
    (scalarDtype : P → String := fun _ => "np.float64") : List String :=
  match s with
  | .skip => []
  | .seq s t => emitFWith inline s d kernelName oracleName scalarDtype ++
      emitFWith inline t d kernelName oracleName scalarDtype
  | .instr i => [pad d ++ emitInstr i]
  | .apply oracle _ dst dOff src sOff cols =>
      match oracleName oracle with
      | none => [pad d ++ "raise NotImplementedError('unbound oracle: supply oracleName')"]
      | some matrix =>
          let a := s!"({matrix})"
          let w := s!"{a}.shape[0] * {emitIExp cols}"
          [pad d ++ s!"np.copyto({bufName dst}[{emitIExp dOff}:{emitIExp dOff} + {w}], ({a} @ " ++
            s!"{bufName src}[{emitIExp sOff}:{emitIExp sOff} + {w}].reshape(({a}.shape[0], " ++
            s!"{emitIExp cols}), order='F')).reshape(-1, order='F'), casting='same_kind')"]
  | .rom _ dst i => [pad d ++ s!"{emitCell dst} = ROM[{emitIExp i}]"]
  | .alloc p len body =>
      [pad d ++ s!"b{nb} = np.full({emitIExp len}, np.nan, dtype={scalarDtype p})"] ++
        emitFWith inline body d kernelName oracleName scalarDtype ++ [pad d ++ s!"del b{nb}"]
  | .loop n body =>
      let ls := emitFWith inline body (d + 1) kernelName oracleName scalarDtype
      [pad d ++ s!"for i{ni} in range({emitIExp n}):"] ++
        (if ls.isEmpty then [pad (d + 1) ++ "pass"] else ls)
  | .whileFuel fuel _ cmp x y body =>
      [pad d ++ s!"for _ in range({emitIExp fuel}):",
        pad (d + 1) ++ s!"if not ({emitCell x} {emitCmp cmp} {emitCell y}): break"] ++
        emitFWith inline body (d + 1) kernelName oracleName scalarDtype ++
        [pad d ++ "else:", pad (d + 1) ++ "raise RuntimeError('out of fuel')"]
  | .ite _ cmp x y t e =>
      let lt := emitFWith inline t (d + 1) kernelName oracleName scalarDtype
      let le := emitFWith inline e (d + 1) kernelName oracleName scalarDtype
      [pad d ++ s!"if {emitCell x} {emitCmp cmp} {emitCell y}:"] ++
        (if lt.isEmpty then [pad (d + 1) ++ "pass"] else lt) ++
        [pad d ++ "else:"] ++ (if le.isEmpty then [pad (d + 1) ++ "pass"] else le)
  | .named name args body =>
      if inline then emitFWith inline body d kernelName oracleName scalarDtype
      else [pad d ++ s!"{name}({", ".intercalate (args.map emitArg)})"]
  | .kcall kernel _ dims ins outs =>
      match kernelName kernel with
      | none => [pad d ++ "raise NotImplementedError('unbound kernel: supply kernelName')"]
      | some name =>
          let ins' := ins.map fun x => s!"({bufName x.1}, {emitIExp x.2})"
          let outs' := outs.map fun x => s!"({bufName x.1}, {emitIExp x.2})"
          [pad d ++ s!"({name})([{", ".intercalate (dims.map emitIExp)}], " ++
            s!"[{", ".intercalate ins'}], [{", ".intercalate outs'}])"]
  | .bindIdx _ x bound body =>
      [pad d ++ s!"if not (0 <= {emitCell x}): raise ValueError('bindIdx: negative value')",
        pad d ++ s!"i{ni} = int(np.floor({emitCell x}))",
        pad d ++ s!"if i{ni} > {emitIExp bound}: raise ValueError('bindIdx: above the bound')"] ++
        emitFWith inline body d kernelName oracleName scalarDtype

/-- A first-order statement as Python lines at depth `d`, with a Python callable for each
kernel identifier. -/
def emitF {P ι : Type} (inline : Bool) (kname : ι → String) {nb ni : ℕ}
    (s : FStmt P ι nb ni) (d : ℕ)
    (oracleName : ι → Option String := by
      first
      | exact (fun (α : Type) (_ : Subsingleton α) (_ : α) => some "A") _ inferInstance
      | exact fun _ => none)
    (scalarDtype : P → String := fun _ => "np.float64") : List String :=
  emitFWith inline s d (fun o => some (kname o)) oracleName scalarDtype

/-- A program `Prog P ι r b` as a Python function `name(A, i0, …, i{r}, b0, …, b{b-1})`.
A total `kname` supplies Python callable expressions. Its default, an empty name, leaves a
kernel unbound. The optional `kernelName` supplies a partial mapping directly.
An unbound call raises `NotImplementedError` when reached.
An `apply` defaults to `A` when the caller can infer `Subsingleton ι`; otherwise `oracleName`
must bind its identifier to a square NumPy matrix expression. Explicit partial bindings stay
partial, including for subsingleton types.
Scratch defaults to the common dtype of `A` and the declared buffers, at least float64.
Use `scalarDtype` per tag when other hooks introduce complex or wider scalar values.
Non-inlined `named` nodes instead delegate their whole bodies to external implementations. -/
def emitProg {P ι : Type} {r b : ℕ} (inline : Bool) (name : String) (prog : Prog P ι r b)
    (kname : ι → String := fun _ => "")
    (kernelName : ι → Option String := fun o =>
      let f := kname o
      if f.isEmpty then none else some f)
    (oracleName : ι → Option String := by
      first
      | exact (fun (α : Type) (_ : Subsingleton α) (_ : α) => some "A") _ inferInstance
      | exact fun _ => none)
    (scalarDtype : P → Option String := fun _ => none) : String :=
  let params := ["A"] ++ (List.range (r + 1)).map (s!"i{·}") ++ (List.range b).map (s!"b{·}")
  let inputs := ["A"] ++ (List.range b).map (s!"b{·}") ++ ["np.float64"]
  let dtype := s!"np.result_type({", ".intercalate inputs})"
  let body := emitFWith inline prog 1 kernelName oracleName
    (fun p => (scalarDtype p).getD dtype)
  "\n".intercalate ([s!"def {name}({", ".intercalate params}):"] ++
    if body.isEmpty then [pad 1 ++ "pass"] else body)

/-- Execute emitted index expressions and small programs using only Python's standard library.
Checks literal, variable and nested zero remainders against Lean's evaluator, ordinary nonzero
remainders, empty functions, and uniform-draw/kernel-call hooks in both kernel modes.
Python failures fail the tools build. -/
def emitterRegressionTest : IO Unit := do
  let expressions : List (IExp (Fin 2)) := [
    .mod 7 0, .mod 0 0, .mod 7 3, .mod (.var 0) (.var 1),
    .mod (.mod (.var 0) 0) (.sub (.var 1) (.var 1)),
    .add 2 (.mod (.mul 3 (.var 0)) (.sub (.var 1) 1))]
  let mut lines := []
  for a in [0, 1, 7] do
    for b in [0, 1, 3] do
      lines := lines ++ [s!"i0 = {a}", s!"i1 = {b}"]
      for e in expressions do
        let expected := e.evalIn (fun i => if i.val == 0 then a else b)
        lines := lines ++ [s!"assert ({emitIExp e}) == {expected}"]
  let programs : List (Prog Unit Unit 0 0) := [.skip, .seq .skip .skip,
    .named "noop_kernel" [] .skip, .loop 0 .skip, .loop 2 .skip]
  lines := lines ++ ["def noop_kernel(): pass"]
  for inline in [false, true] do
    for program in programs do
      lines := lines ++ [emitProg inline "noop" program, "assert noop(None, 0) is None"]
  -- A zero remainder also works as an emitted buffer offset, not only as a bare expression.
  let write : Prog Unit Unit 0 1 :=
    .instr (.litIdx () ⟨0, .mod 0 0⟩ (.mod 7 0))
  lines := lines ++ [emitProg true "write" write, "out = [None]", "write(None, 0, out)",
    "assert out == [7.0]"]
  -- New draw and kernel paths retain total remainders in dimensions and block offsets.
  let hooked : Prog Unit Unit 0 2 :=
    .seq (.instr (.draw () .uniform ⟨0, .mod 1 0⟩))
      (.kcall () () [.mod (.var 0) 0] [(0, .mod 1 0)] [(1, .mod 2 0)])
  lines := lines ++ ["def draw_uniform(): events.append('uniform'); return 0.25",
    "def kernel(dims, ins, outs):",
    "    assert dims == [3] and len(ins) == len(outs) == 1",
    "    src, soff = ins[0]; dst, doff = outs[0]",
    "    assert soff == 1 and doff == 2",
    "    events.append('kernel'); dst[doff] = src[soff] + dims[0]"]
  for inline in [false, true] do
    lines := lines ++ [emitProg inline "hooked" hooked (fun _ => "kernel"), "events = []",
      "src = [11, 22, 33]; dst = [44, 55, 66, 77]", "hooked(None, 3, src, dst)",
      "assert events == ['uniform', 'kernel']",
      "assert src == [11, 0.25, 33] and dst == [44, 55, 3.25, 77]"]
  let out ← IO.Process.output { cmd := "python3", args := #["-c", "\n".intercalate lines] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"emitter regression failed: {out.stderr}"
  IO.println ("NumPy emitter regressions passed (54 index cases, 10 empty bodies, " ++
    "buffer offset, 2 uniform/kernel programs)")

#eval emitterRegressionTest

/-- Execute two distinct black-box kernels under a loop in both inline modes. Missing and
partially supplied bindings must reject the unbound call, even if `kernel` exists in Python. -/
def kernelBindingRegressionTest : IO Unit := do
  let program : Prog Unit Bool 0 2 := .loop 1
    (.seq (.kcall false () [1] [(0, 0)] [(1, 0)])
      (.kcall true () [1] [(1, 0)] [(0, 0)]))
  let bindings : Bool → Option String := fun k => some (if k then "second" else "first")
  let partialBindings : Bool → Option String := fun k => if k then none else some "first"
  let mut lines := [
    "def kernel(*args): raise AssertionError('anonymous callback used')",
    "def first(dims, ins, outs):",
    "    assert dims == [1] and len(ins) == len(outs) == 1",
    "    src, si = ins[0]; dst, di = outs[0]",
    "    events.append('first'); dst[di] = src[si] + 1",
    "def second(dims, ins, outs):",
    "    assert dims == [1] and len(ins) == len(outs) == 1",
    "    src, si = ins[0]; dst, di = outs[0]",
    "    events.append('second'); dst[di] = 2 * src[si]"]
  for inline in [false, true] do
    lines := lines ++ [emitProg inline "bound" program (kernelName := bindings),
      "events = []; src = [2]; dst = [0]", "bound(None, 0, src, dst)",
      "assert events == ['first', 'second'] and src == [6] and dst == [3]"]
    for (name, binding, expectedEvents, expectedDst) in
        [("unbound", fun _ => none, "[]", "[0]"),
         ("partial", partialBindings, "['first']", "[3]")] do
      lines := lines ++ [emitProg inline name program (kernelName := binding),
        "events = []; src = [2]; dst = [0]", "try:", s!"    {name}(None, 0, src, dst)",
        "except NotImplementedError as error:", "    assert 'unbound kernel' in str(error)",
        "else:", "    raise AssertionError('unbound kernel was accepted')",
        s!"assert events == {expectedEvents} and src == [2] and dst == {expectedDst}"]
  let out ← IO.Process.output { cmd := "python3", args := #["-c", "\n".intercalate lines] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"kernel binding regression failed: {out.stderr}"
  IO.println "NumPy kernel binding regressions passed (6 dispatch/rejection cases)"

#eval kernelBindingRegressionTest

/-- The NumPy prelude: the BLAS kernels the programs call by name. -/
def numpyPrelude : String := "\n".intercalate [
  "import numpy as np",
  "def dot(d, di, x, xo, y, yo, n): d[di] = np.vdot(x[xo:xo+n], y[yo:yo+n])",
  "def axpy(a, ai, x, xo, y, yo, n): y[yo:yo+n] += a[ai] * x[xo:xo+n]",
  "def scal(a, ai, x, xo, n): x[xo:xo+n] *= a[ai]",
  "def rscl(a, ai, x, xo, n): x[xo:xo+n] /= a[ai]",
  "def copy(x, xo, y, yo, n): y[yo:yo+n] = x[xo:xo+n]",
  "def nrm2(d, di, x, xo, n): d[di] = np.linalg.norm(x[xo:xo+n])"]

/-- Execute emitted legacy single-oracle, two-oracle, complex scratch and unbound-oracle programs.
The complex test promotes real declared buffers using the complex matrix; an explicit per-tag
choice also handles complex values introduced by an oracle outside those inputs.
Skipped when Python or NumPy is unavailable, like the differential tests below. -/
def oracleAndScratchRegressionTest : IO Unit := do
  let probe ← IO.Process.output { cmd := "python3", args := #["-c", "import numpy"] }
    |>.toBaseIO
  match probe with
  | .ok out =>
    if out.exitCode != 0 then IO.println "oracle/scratch tests skipped: no NumPy"; return
  | .error _ => IO.println "oracle/scratch tests skipped: no python3"; return
  let stack : Prog Unit Bool 0 2 := .loop 1
    (.seq (.apply false () 1 0 0 0 1) (.apply true () 0 0 1 0 1))
  let legacyUnit : Prog Unit Unit 0 2 := .apply () () 1 0 0 0 1
  let legacyPUnit : Prog Unit PUnit 0 2 := .apply PUnit.unit () 1 0 0 0 1
  let temp : Prog Unit Bool 0 2 := .alloc () 1
    (.seq (.apply false () 2 0 0 0 1) (.instr (.copy () ⟨1, 0⟩ ⟨2, 0⟩)))
  let external : Prog Unit Bool 0 2 := .alloc () 1
    (.seq (.apply false () 2 0 0 0 1) (.instr (.un () .re ⟨1, 0⟩ ⟨2, 0⟩)))
  let typed : Prog Bool Unit 0 1 := .alloc false 1 (.alloc true 1
    (.seq (.instr (.draw true .uniform ⟨2, 0⟩))
      (.seq (.instr (.bin true .mul ⟨2, 0⟩ ⟨2, 0⟩ ⟨2, 0⟩))
        (.seq (.instr (.un false .re ⟨1, 0⟩ ⟨2, 0⟩))
          (.instr (.copy false ⟨0, 0⟩ ⟨1, 0⟩))))))
  let mut lines := [numpyPrelude, "import warnings", "warnings.simplefilter('error')",
    "operators = [np.array([[2.0]]), np.array([[3.0]])]"]
  for inline in [false, true] do
    lines := lines ++ [emitProg inline "legacy_unit" legacyUnit,
      emitProg inline "legacy_punit" legacyPUnit,
      "src = np.array([1.0]); dst = np.zeros(1)",
      "legacy_unit(operators[0], 1, src, dst)", "assert dst[0] == 2",
      "dst[:] = 0", "legacy_punit(operators[0], 1, src, dst)", "assert dst[0] == 2",
      emitProg inline "stack" stack
      (oracleName := fun o => some (if o then "operators[1]" else "operators[0]")),
      "src = np.array([1.0]); dst = np.zeros(1)", "stack(operators[0], 1, src, dst)",
      "assert src[0] == 6 and dst[0] == 2"]
    for (name, binding, expectedDst) in
        [("unbound", fun (_ : Bool) => (none : Option String), "0"),
         ("partial", fun (o : Bool) => if o then none else some "operators[0]", "2")] do
      let emitted := if name == "unbound" then emitProg inline name stack
        else emitProg inline name stack (oracleName := binding)
      lines := lines ++ [emitted,
        "src = np.array([1.0]); dst = np.zeros(1)", "try:",
        s!"    {name}(operators[0], 1, src, dst)", "except NotImplementedError as error:",
        "    assert 'unbound oracle' in str(error)", "else:",
        "    raise AssertionError('unbound oracle was accepted')",
        s!"assert src[0] == 1 and dst[0] == {expectedDst}"]
    lines := lines ++ [emitProg inline "via_temp" temp (oracleName := fun _ => some "A"),
      "A = np.array([[1+2j]])", "src = np.array([1.0]); dst = np.zeros(1, dtype=complex)",
      "via_temp(A, 1, src, dst)", "assert dst[0] == 1+2j",
      emitProg inline "adjoint" stack
        (oracleName := fun o => some (if o then "A.conj().T" else "A")),
      "src = np.array([1+0j]); dst = np.zeros(1, dtype=complex)",
      "adjoint(A, 1, src, dst)", "assert src[0] == 5 and dst[0] == 1+2j",
      emitProg inline "typed" typed
        (scalarDtype := fun p => some (if p then "np.complex128" else "np.float64")),
      "def draw_uniform(): return 1+2j", "dst = np.zeros(1)",
      "typed(None, 1, dst)", "assert dst[0] == -3",
      "complex_operator = np.array([[1+2j]])",
      emitProg inline "external_reject" external (oracleName := fun _ => some "complex_operator"),
      "src = np.array([1.0]); dst = np.zeros(1)", "try:",
      "    external_reject(None, 1, src, dst)", "except TypeError:", "    pass", "else:",
      "    raise AssertionError('complex oracle result was silently truncated')",
      "assert dst[0] == 0",
      emitProg inline "external_real" external (oracleName := fun _ => some "complex_operator")
        (scalarDtype := fun _ => some "np.complex128"),
      "external_real(None, 1, src, dst)", "assert dst[0] == 1"]
  let out ← IO.Process.output { cmd := "python3", args := #["-c", "\n".intercalate lines] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"oracle/scratch regression failed: {out.stderr}"
  IO.println "NumPy oracle/scratch regressions passed (20 execution/rejection cases)"

#eval oracleAndScratchRegressionTest

/-- The registered tree `NLAlib.hutchppProg.compiled` as a NumPy function
`hutchpp(A, i0, i1, i2, b0)`: `i0` is $N$, `i1` is $k$, `i2` is $\ell$, and the estimate is
written to `b0[0]`; with a `draw_rademacher` hook. -/
def hutchppPython (inline : Bool) : String :=
  emitProg inline "hutchpp" (hutchppProg.compiled (P := Unit) (ι := Unit) () () .rademacher)
    (oracleName := fun _ => some "A")

#eval IO.println (numpyPrelude ++ "\n" ++ hutchppPython false)

/-- The registered tree `NLAlib.deflateProg.compiled` as a NumPy function
`deflate(A, i0, i1, b0, b1)`, inlined, with the kernel names `mm` and `qr` printed (the S1d
check that kernel calls are told apart). -/
def deflatePython : String :=
  emitProg true "deflate" (deflateProg.compiled (P := Unit) (ι := Bool) () true false)
    fun o => cond o "mm" "qr"

#guard (deflatePython.splitOn "(mm)([").length == 2 && (deflatePython.splitOn "(qr)([").length == 2

/-- A stored value copied through an index binder of bound `i1`, as the NumPy function
`idx_copy(A, i0, i1, b0, b1)`. -/
def idxCopyPython : String :=
  emitProg false "idx_copy" (P := Unit) (ι := Unit) (r := 1) (b := 2)
    (.bindIdx () ⟨0, .const 0⟩ (.var 1) (.instr (.litIdx () ⟨1, .const 0⟩ (.var 2))))

-- The binder is emitted strict, as the model's `Exec.exec` and `exactSem.toNat`: no clamp.
#guard (idxCopyPython.splitOn "min(max").length == 1 &&
  (idxCopyPython.splitOn "raise ValueError").length == 3

/-- **Strictness test**: the emitted binder raises `ValueError` where the model's run fails (a
negative value, a value above the bound) and floors where it succeeds; skipped when NumPy is not
installed. -/
def strictBindTest : IO Unit := do
  let probe ← IO.Process.output { cmd := "python3", args := #["-c", "import numpy"] }
    |>.toBaseIO
  match probe with
  | .ok out =>
    if out.exitCode != 0 then IO.println "strictness test skipped: no NumPy"; return
  | .error _ => IO.println "strictness test skipped: no python3"; return
  let script := "\n".intercalate [numpyPrelude, idxCopyPython,
    "def run(v, bound):",
    "    out = np.full(1, np.nan)",
    "    try: idx_copy(None, 1, bound, np.array([v]), out)",
    "    except ValueError: return 'fail'",
    "    return repr(float(out[0]))",
    "print(run(-1.0, 5), run(-0.5, 5), run(1.0, 0), run(2.7, 3), run(float('nan'), 5))"]
  let out ← IO.Process.output { cmd := "python3", args := #["-c", script] }
  let got := out.stdout.trimAscii.toString
  unless out.exitCode == 0 && got == "fail fail fail 2.0 fail" do
    throw <| IO.userError s!"the emitted binder is not strict: {got} {out.stderr}"
  IO.println s!"strict binder: {got}"

#eval strictBindTest

/-- A Python script that runs the emitted Hutch++ on the matrix `A₀` with the sign tape and
prints the estimate. -/
def hutchppScript (inline : Bool) (k ℓ : ℕ) : String :=
  let rows := ", ".intercalate (A₀.toList.map fun r => "[" ++ ", ".intercalate
    (r.toList.map toString) ++ "]")
  let tape := ", ".intercalate (signTape.map toString)
  "\n".intercalate [numpyPrelude, hutchppPython inline,
    s!"A = np.array([{rows}])", s!"tape = [{tape}]",
    "def draw_rademacher(): return tape.pop(0)",
    "out = np.full(1, np.nan)", s!"hutchpp(A, 5, {k}, {ℓ}, out)", "print(repr(float(out[0])))"]

/-- **Differential test**: the emitted Hutch++, run by NumPy, agrees with the Lean `Float` run
of the same registered tree (`NLAlibTools.hutchppTreeRun`) to six digits, in both modes and on
both rows of the design note's table; skipped when NumPy is not installed. -/
def differentialTest : IO Unit := do
  let probe ← IO.Process.output { cmd := "python3", args := #["-c", "import numpy"] }
    |>.toBaseIO
  match probe with
  | .ok out =>
    if out.exitCode != 0 then IO.println "differential test skipped: no NumPy"; return
  | .error _ => IO.println "differential test skipped: no python3"; return
  for (k, ℓ) in [(2, 1), (5, 1)] do
    for inline in [false, true] do
      let out ← IO.Process.output
        { cmd := "python3", args := #["-c", hutchppScript inline k ℓ] }
      let some lean := (hutchppTreeRun k ℓ).bind (·.1.head?)
        | throw <| IO.userError "the Lean run of the tree fails"
      let py := out.stdout.trimAscii.toString
      unless out.exitCode == 0 && (py.toList.all fun c => c.isDigit || c == '.' || c == '-') do
        throw <| IO.userError s!"the emitted code fails: {out.stderr}"
      unless (lean - parseFloat py).abs < 1e-6 do
        throw <| IO.userError s!"k = {k}, ℓ = {ℓ}: NumPy {py}, Lean {lean}"
      IO.println s!"k = {k}, ℓ = {ℓ}, inline {inline}: NumPy {py} agrees with Lean {lean}"
where
  /-- A decimal literal as a `Float`. -/
  parseFloat (s : String) : Float :=
    let (neg, s) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
    let parts := s.splitOn "."
    let ip := (parts.head?.bind String.toNat?).getD 0
    let fp := parts[1]?.getD ""
    let v := Float.ofNat ip + Float.ofNat (fp.toNat?.getD 0) / Float.ofNat (10 ^ fp.length)
    if neg then -v else v

#eval differentialTest

end NLAlibTools
