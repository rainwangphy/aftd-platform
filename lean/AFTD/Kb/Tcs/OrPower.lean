import AFTD.Prelude

/-!
# or_power

Topic: information   Node: 9535bbe770d4

Provenance: formalization of a published result. Source: arXiv:2610.41977, Eq. (1.1)

The n-th OR-power (co-normal power) of a simple graph G has vertex set Fin n → V, with an edge between x and y if and only if there exists some coordinate i such that x(i) is adjacent to y(i) in G.
-/

/-- The n-th OR-power (co-normal power) of a simple graph G: two words of length n are adjacent if and only if they are adjacent in at least one coordinate. -/
def or_power {V : Type*} (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) := {
  Adj := fun x y => ∃ i : Fin n, G.Adj (x i) (y i)
  symm := ⟨fun _ _ ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  loopless := ⟨fun _ ⟨_i, hi⟩ => G.loopless.irrefl _ hi⟩
}
