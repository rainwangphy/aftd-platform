import AFTD.Prelude

/-!
# simple_graph_clique_blowup

Topic: graphs   Node: 15cf10e97bae

Provenance: formalization of a published result. Source: arXiv:2610.09300 (On graphs whose powers are well-covered), Sec. 1 and proof of Theorem 1.6 (clique blow-up, graph composition with cliques). Vertices are pairs ⟨i, x⟩ with x : Fin (a i).

The clique blow-up H = G[K_{a_1}, …, K_{a_n}]: each vertex v_i of G is replaced by a clique Q_i on a_i vertices, and distinct vertices x ∈ Q_i, y ∈ Q_j are adjacent iff i = j or v_i v_j ∈ E(G).
-/

/-- The clique blow-up `G[K_{a_1}, …, K_{a_n}]`: each vertex `i` is replaced by a clique on `a i` vertices, and vertices in different cliques are adjacent when their parts are. -/
def simple_graph_clique_blowup {V : Type*} (G : SimpleGraph V) (a : V → ℕ) :
    SimpleGraph (Σ i, Fin (a i)) where
  Adj p q := (p.1 = q.1 ∧ p ≠ q) ∨ G.Adj p.1 q.1
  symm := ⟨fun (p q : Σ i, Fin (a i)) (h : (p.1 = q.1 ∧ p ≠ q) ∨ G.Adj p.1 q.1) => by
    rcases h with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr h.symm⟩
  loopless := ⟨fun (p : Σ i, Fin (a i)) (h : (p.1 = p.1 ∧ p ≠ p) ∨ G.Adj p.1 p.1) => by
    rcases h with ⟨-, h⟩ | h
    · exact h rfl
    · exact G.loopless.irrefl _ h⟩
