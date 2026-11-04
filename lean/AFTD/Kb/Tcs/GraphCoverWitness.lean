import AFTD.Prelude

/-!
# GraphCoverWitness

Topic: combinatorics   Node: 914562687ef0

Provenance: helper lemma. step towards simple_graph_five_noncycle_independent_cover_witness

Predicate on a five-vertex graph G and a family J of vertex-sets: each J t is independent in G and avoids its own index t, the total size ∑_t |J t| is at least 11, and every nonempty independent vertex set S contains a vertex t with S disjoint from J t.
-/

/-- Packages the conclusion of the five-vertex cover witness: independent sets J t (t ∉ J t), total size ≥ 11, meeting every nonempty independent set S at some t ∈ S with S ∩ J t = ∅. -/
def GraphCoverWitness (G : SimpleGraph (Fin 5)) (J : Fin 5 → Finset (Fin 5)) : Prop := (∀ t, G.IsIndepSet (J t) ∧ t ∉ J t) ∧
  11 ≤ Finset.univ.sum (fun t => (J t).card) ∧
  ∀ S : Finset (Fin 5), S.Nonempty → G.IsIndepSet S → ∃ t ∈ S, Disjoint S (J t)
