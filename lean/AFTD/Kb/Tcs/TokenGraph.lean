import AFTD.Prelude

/-!
# token_graph

Topic: graphs   Node: 61aceca909a0

Provenance: formalization of a published result. Source: arXiv:2610.28936 Definition 2.5

The k-token graph F_k(G) of a simple graph G has as vertices the k-subsets of V(G), with two k-subsets adjacent whenever their symmetric difference consists of two adjacent vertices in G.
-/

/-- The k-token graph of a simple graph G. -/
def token_graph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph { s : Finset V // s.card = k } := {
  Adj := fun x y => ∃ u v : V, G.Adj u v ∧ symmDiff x.val y.val = {u, v}
  symm := ⟨by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨u, v, hadj, hdiff⟩
    refine ⟨u, v, hadj, ?_⟩
    rw [symmDiff_comm, hdiff]⟩
  loopless := ⟨by
    rintro ⟨x, hx⟩ ⟨u, v, hadj, hdiff⟩
    have hne : u ≠ v := G.ne_of_adj hadj
    have hcard : ({u, v} : Finset V).card = 2 := Finset.card_pair hne
    have h0 : (symmDiff x x).card = 0 := by simp
    rw [hdiff] at h0
    omega⟩
}
