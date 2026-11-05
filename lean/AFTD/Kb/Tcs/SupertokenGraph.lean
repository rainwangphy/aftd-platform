import AFTD.Prelude

/-!
# supertoken_graph

Topic: graphs   Node: 6671f87f9e6f

Provenance: formalization of a published result. Source: arXiv:2611.06275, Section 1

The supertoken graph F^s_{k x 1}(G) of a simple graph G has as vertices the k-tuples of vertices of G with at most s occurrences of any vertex, where two configurations are adjacent if they differ at exactly one token moved along an edge of G.
-/

/-- The supertoken graph F^s_{k x 1}(G) with k distinguishable tokens and maximum capacity s per vertex. -/
def supertoken_graph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k s : ℕ) :
    SimpleGraph { x : Fin k → V // ∀ v : V, (Finset.univ.filter (fun i => x i = v)).card ≤ s } := {
  Adj := fun x y => ∃ i : Fin k, G.Adj (x.1 i) (y.1 i) ∧ ∀ j : Fin k, j ≠ i → x.1 j = y.1 j
  symm := ⟨by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨i, hadj, heq⟩
    exact ⟨i, G.adj_symm hadj, fun j hj => (heq j hj).symm⟩⟩
  loopless := ⟨by
    rintro ⟨x, hx⟩ ⟨i, hadj, -⟩
    exact G.loopless.irrefl (x i) hadj⟩
}
