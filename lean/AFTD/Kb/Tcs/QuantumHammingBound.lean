import AFTD.Prelude
import AFTD.Kb.Tcs.Hn
import AFTD.Kb.Tcs.IsNondegenerate
import AFTD.Kb.Tcs.QuantumHammingBoundRaw
import AFTD.Kb.Tcs.CodeProjApply
import AFTD.Kb.Tcs.InstFintypePauliString
import AFTD.Kb.Tcs.InstFiniteDimensionalComplexSubtypeHnMemSubmodule

/-!
# quantum_hamming_bound

Topic: quantum   Node: a2094487ed44

Provenance: formalization of a published result. Source: Quantum Hamming bound for non-degenerate codes, as formalized in TCSlib (`quantum_hamming_bound`). Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumHamming.lean (Apache-2.0); 1 verbatim; compiled here.

Quantum Hamming bound for non-degenerate codes. Let $C \le \mathcal{H}_n$ be a subspace of the $n$-qubit Hilbert space whose complex
dimension is $\dim_{\mathbb{C}} C = 2^k$, and suppose $k \le n$. If $C$ is a
non-degenerate code correcting $t$ errors — meaning it satisfies the Knill–Laflamme
condition $P_C\,E^\dagger F\,P_C = \lambda_{EF}\,P_C$ for all Pauli strings $E,F$ of
weight at most $t$, and moreover $P_C\,E^\dagger F\,P_C = 0$ whenever $E \ne F$, where
$P_C$ is the orthogonal projection onto $C$ — then
\[
\sum_{j=0}^{t} \binom{n}{j}\, 3^{\,j} \;\le\; 2^{\,n-k}.
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
/-- Quantum Hamming bound: a non-degenerate `[[n, k]]` quantum code correcting t errors satisfies `∑ j ∈ Finset.range (t + 1), C(n, j) * 3^j ≤ 2^(n - k)`. -/
theorem quantum_hamming_bound
    (n k t : ℕ) (C : Submodule ℂ (Hn n))
    (h_dim : Module.finrank ℂ C = 2^k)
    (h_nondeg : IsNondegenerate n C t)
    (hkn : k ≤ n) :
    ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j ≤ 2 ^ (n - k) := by
  classical
  have hraw :=
    quantum_hamming_bound_raw (n := n) (k := k) (t := t) (C := C) h_dim h_nondeg

  -- rewrite RHS: 2^n = 2^((n-k)+k) = 2^(n-k) * 2^k
  have hmul :
      (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2^k
        ≤ (2^(n - k)) * 2^k := by
      rwa [ ← pow_add, Nat.sub_add_cancel hkn ]
  have hkpos : 0 < 2^k := Nat.two_pow_pos k
  exact Nat.le_of_mul_le_mul_right hmul hkpos
