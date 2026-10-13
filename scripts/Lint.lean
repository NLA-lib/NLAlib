import NLAlib
import Batteries.Tactic.Lint

/-! # Environment linters

Mathlib's `#lint` over the whole library: docstrings (`docBlame`), simp-lemma hygiene
(`simpNF`, `simpVarHead`), unused arguments, instance validity, `Type*` universe style and the
rest of the standard set. Run with `lake env lean scripts/Lint.lean`. -/

#lint in NLAlib
