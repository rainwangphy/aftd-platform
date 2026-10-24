import AFTD.Prelude

/-!
# is_two_four_code

Topic: information   Node: 351e9fc85c6c

Provenance: formalization of a published result. Source: arXiv:2610.30613, Section 1

A set of codewords $C \subseteq (\mathrm{Fin}\, n \to \mathrm{Fin}\, q)$ is a $\{2, 4\}$-code if any two distinct codewords $x, y \in C$ have Hamming distance $\mathrm{hammingDist}(x, y) \in \{2, 4\}$.
-/

/-- A subset C of (Fin n → Fin q) is a {2,4}-code if every pair of distinct codewords has Hamming distance 2 or 4. -/
def is_two_four_code {n q : ℕ} (C : Set (Fin n → Fin q)) : Prop := ∀ x ∈ C, ∀ y ∈ C, x ≠ y → hammingDist x y = 2 ∨ hammingDist x y = 4
