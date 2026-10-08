import AFTD.Prelude

/-!
# codeA

Topic: information   Node: 3f0e33d8fce4

Provenance: formalization of a published result. Source: TCSlib, `codeA`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

For naturals $n$ and $d$, $A(n,d)$ is the supremum of the cardinalities $k$ for which
there is a finite set $C$ of binary codewords $\mathrm{Fin}\,n \to \mathrm{Bool}$ with
$|C| = k$ and such that any two distinct $x, y \in C$ differ in at least $d$
coordinates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
/-- **Definition 1 (maximum code size)** from the source file. For integers `n ≥ 1` and `1 ≤ d ≤ n`, `codeA n d` denotes the maximum size of a binary code `C ⊆ {0,1}^n` with minimum Hamming distance at least `d`. The Hamming distance between two codewords is defined as the number of coordinates at which they differ. -/
noncomputable def codeA (n d : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (C : Finset (Fin n → Bool)),
    C.card = k ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      (Finset.univ.filter fun i => x i ≠ y i).card ≥ d}
