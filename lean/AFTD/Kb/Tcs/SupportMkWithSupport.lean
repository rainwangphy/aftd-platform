import AFTD.Prelude
import AFTD.Kb.Tcs.PauliNZ
import AFTD.Kb.Tcs.PauliNZToBasisNeI
import AFTD.Kb.Tcs.MkWithSupport
import AFTD.Kb.Tcs.Support

/-!
# support_mkWithSupport

Topic: quantum   Node: 1fdee7fff8f9

Provenance: helper lemma. TCSlib, `support_mkWithSupport`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Support of a Pauli string built from prescribed data. Fix $n$, a finset $S \subseteq \mathrm{Fin}\,n$, and an assignment $f : S \to \{X,Y,Z\}$
of a non-identity Pauli to each coordinate in $S$. Let $p$ be the Pauli string of length
$n$ that equals $f(i)$ at each $i \in S$ and equals the identity $I$ at every coordinate
outside $S$. Then the support of $p$ — the set of coordinates where $p$ differs from $I$
— is exactly $S$.
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
lemma support_mkWithSupport {n : ℕ} (S : Finset (Fin n)) (f : S → PauliNZ) :
    support (mkWithSupport S f) = S := by
  classical
  ext i
  simp [support, mkWithSupport, PauliNZ.toBasis_ne_I]
