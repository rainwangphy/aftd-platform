import AFTD.Prelude

/-!
# is_lattice_translate

Topic: graphs   Node: a15c4962ed9a

Provenance: formalization of a published result. Source: arXiv:2611.18633 Theorem 4.3

For S T : Finset (ℤ × ℤ), is_lattice_translate S T holds if there exists t : ℤ × ℤ such that S = T.map ⟨(· + t), add_left_injective t⟩.
-/

/-- Predicate that S is a lattice translate of T in ℤ × ℤ. -/
def is_lattice_translate (S T : Finset (ℤ × ℤ)) : Prop := ∃ t : ℤ × ℤ, S = T.map ⟨(· + t), add_left_injective t⟩
