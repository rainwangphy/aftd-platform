import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorSphere
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.IsNondegenerate
import AFTD.Kb.Tcs.CardPauliErrorsLe
import AFTD.Kb.Tcs.ErrorSphereDimension
import AFTD.Kb.Tcs.FinrankHn
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.InstFiniteDimensionalComplexSubtypeHnMemSubmodule
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliErrorsLe

/-!
# quantum_hamming_bound_raw

Topic: quantum   Node: 392ad8b35cdf

Provenance: helper lemma. TCSlib, `quantum_hamming_bound_raw`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Quantum Hamming bound for non-degenerate codes. Let $C \le \mathcal{H}_n$ be a subspace of the $n$-qubit Hilbert space that is a
non-degenerate quantum code correcting $t$ errors, and suppose its complex dimension is
$\dim_{\mathbb{C}} C = 2^{k}$ for some natural number $k$. Then
\[
\left(\sum_{j=0}^{t}\binom{n}{j}\,3^{j}\right)\cdot 2^{k} \;\le\; 2^{n}.
\]
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
/-- Quantum Hamming bound (raw form): for a non-degenerate `[[n, k]]` quantum code correcting t errors, the total dimension of the error sphere does not exceed the ambient space. -/
theorem quantum_hamming_bound_raw
    (n k t : ℕ) (C : Submodule ℂ (Hn n))
    (h_dim : Module.finrank ℂ C = 2^k)
    (h_nondeg : IsNondegenerate n C t) :
    (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2 ^ k ≤ 2 ^ n := by
  classical
  have h_sphere :
      Module.finrank ℂ (ErrorSphere n t C)
        = (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2 ^ k := by
    simpa [h_dim, card_pauliErrorsLe, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (error_sphere_dimension (n:=n) (t:=t) (C:=C) h_nondeg)

  have h_le :
      Module.finrank ℂ (ErrorSphere n t C) ≤ 2^n := by
    have : Module.finrank ℂ (ErrorSphere n t C) ≤ Module.finrank ℂ (Hn n) :=
      Submodule.finrank_le (ErrorSphere n t C)
    simpa [finrank_Hn n] using this

  simpa [h_sphere] using h_le
