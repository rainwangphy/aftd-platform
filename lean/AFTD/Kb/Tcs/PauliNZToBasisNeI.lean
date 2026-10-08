import AFTD.Prelude
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliNZ
import AFTD.Kb.Tcs.PauliNZToBasis

/-!
# PauliNZ.toBasis_ne_I

Topic: quantum   Node: 0d94f4e0a9b7

Provenance: helper lemma. TCSlib, `PauliNZ.toBasis_ne_I`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Non-identity Paulis embed away from the identity. Write $\{X, Y, Z\}$ for the three non-identity Pauli labels, embedded in the natural way
into the full Pauli basis $\{I, X, Y, Z\}$. Then the image of every such label differs
from the identity element $I$.
-/

set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open scoped Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Complex Matrix in
lemma PauliNZ.toBasis_ne_I : ∀ a : PauliNZ, a.toBasis ≠ PauliBasis.I := by
  intro a; cases a <;> simp [PauliNZ.toBasis]
