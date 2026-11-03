import AFTD.Prelude

/-!
# multigraph_truncation

Topic: graphs   Node: 4060d9d5c4bc

Provenance: formalization of a published result. Source: arXiv:2610.41950 (Strong edge-colourings of truncations of cubic graphs), Section 1: definition of the truncation T(G) of a loopless cubic multigraph

The truncation T(G) of a multigraph G with vertex type V and edge type E, the multigraph given by its endpoint map ends : E → Sym2 V (parallel edges are distinct elements of E). T(G) is a SimpleGraph on the subtype of ports {p : V × E // p.1 ∈ ends p.2}, i.e. the incidences (v, e) with v an endpoint of e. Two ports p, q are adjacent iff p ≠ q ∧ (p.1.1 = q.1.1 ∨ p.1.2 = q.1.2): distinct ports at the same vertex v of G (the edges of the canonical triangle Δ_v, called internal) or distinct ports on the same edge e of G (the edge (u,e)(v,e) for e = uv, called external).
-/

def multigraph_truncation {V E : Type*} (ends : E → Sym2 V) :
    SimpleGraph {p : V × E // p.1 ∈ ends p.2} where
  Adj p q := p ≠ q ∧ (p.1.1 = q.1.1 ∨ p.1.2 = q.1.2)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp Eq.symm Eq.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
