import AFTD.Prelude

/-!
# cubic_paley_graph

Topic: graphs   Node: e07782fc0936

Provenance: formalization of a published result. Source: arXiv:2610.27510 (The achromatic number of Paley graphs, Peisert graphs, and related Cayley graphs), Sec. 1, the k-th power Paley graph G_k(q) for k = 3

G_3(q): vertex set F_q, with distinct x, y adjacent iff x − y ∈ (F_q^×)^3. Defined over any commutative ring; the difference of distinct vertices is nonzero, so it is a nonzero cube.
-/

/-- The cubic Paley graph G_3(q) on a commutative ring F (the paper's case: F a finite field of order q ≡ 1 mod 6): distinct x, y are adjacent iff x − y is a cube (necessarily a nonzero one). -/
def cubic_paley_graph (F : Type*) [CommRing F] : SimpleGraph F where
  Adj x y := x ≠ y ∧ ∃ z : F, x - y = z ^ 3
  symm := ⟨by
    rintro x y ⟨hxy, z, hz⟩
    exact ⟨fun h => hxy h.symm, -z, by rw [← neg_sub, hz]; ring⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
