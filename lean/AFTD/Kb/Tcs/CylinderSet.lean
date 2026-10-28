import AFTD.Prelude

/-!
# cylinder_set

Topic: combinatorics   Node: 64da4b4cd0d7

Provenance: formalization of a published result. Source: arXiv:2610.34758 Lemma 2.3, Eq (2.6)

The cylinder set $E_A \subset (\mathbb{Z}/p\mathbb{Z})^d$ associated to a subspace $W$, a vector $e$, and a subset $A \subset \mathbb{Z}/p\mathbb{Z}$, defined by $E_A = \{w + a \cdot e : w \in W, a \in A\}$.
-/

/-- The cylinder set formed by translating a subspace along scalar multiples of a vector. -/
def cylinder_set (d : ℕ) {p : ℕ} (W : Submodule (ZMod p) (Fin d → ZMod p)) (e : Fin d → ZMod p) (A : Set (ZMod p)) : Set (Fin d → ZMod p) := { x | ∃ w ∈ W, ∃ a ∈ A, x = w + a • e }
