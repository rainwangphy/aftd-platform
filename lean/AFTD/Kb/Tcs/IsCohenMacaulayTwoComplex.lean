import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_cohen_macaulay_two_complex

Topic: combinatorics   Node: 65b70cfaa99d

Provenance: formalization of a published result. Source: arXiv:2610.27083 Question 6.2; Duval et al. (2016) Adv. Math. 299, 381-395

A finite simplicial complex given by a set of facets in a linearly ordered vertex type V is defined to be Cohen-Macaulay over a field k if: (1) facets is nonempty; (2) every facet has cardinality 3; (3) the 1-skeleton graph is connected on its vertices; (4) for every vertex v in the complex and all vertices u and w with u ≠ v and w ≠ v such that {u, v} and {w, v} are each a subset of some facet in facets, u and w are reachable from each other in the link graph of v (the simple graph with edges {a, b} such that {a, b, v} is in facets); and (5) every 1-cycle over k supported on ordered edges u < v is the boundary of some 2-chain over k supported on ordered triangles u < v < w.
-/

/-- A finite simplicial complex given by facets is Cohen-Macaulay over a field k if it is pure 2-dimensional, connected, has connected vertex links, and has vanishing first homology. -/
def is_cohen_macaulay_two_complex {V : Type*} [DecidableEq V] [LinearOrder V]
    (facets : Finset (Finset V)) (k : Type*) [Field k] : Prop :=
  let verts := facets.biUnion id
  let edges := (verts ×ˢ verts).filter fun ⟨u, v⟩ => u < v ∧ {u, v} ∈ facets.biUnion Finset.powerset
  let triangles := (verts ×ˢ (verts ×ˢ verts)).filter fun ⟨u, v, w⟩ => u < v ∧ v < w ∧ {u, v, w} ∈ facets
  let skel : SimpleGraph V := SimpleGraph.fromRel (fun u v => ∃ σ ∈ facets, u ∈ σ ∧ v ∈ σ)
  facets.Nonempty ∧
  (∀ σ ∈ facets, σ.card = 3) ∧
  (∀ u ∈ verts, ∀ w ∈ verts, skel.Reachable u w) ∧
  (∀ v ∈ verts, ∀ u w, {u, v} ∈ facets.biUnion Finset.powerset → {w, v} ∈ facets.biUnion Finset.powerset →
    u ≠ v → w ≠ v → (SimpleGraph.fromRel (fun a b => {a, b, v} ∈ facets)).Reachable u w) ∧
  (∀ c : (V × V) → k,
    ((∀ e, e ∉ edges → c e = 0) ∧
     ∀ x ∈ verts, edges.sum (fun ⟨u, v⟩ => (if u = x then c (u, v) else 0) - (if v = x then c (u, v) else 0)) = 0) →
    ∃ b : (V × V × V) → k,
      ∀ e ∈ edges,
        c e = triangles.sum (fun ⟨u, v, w⟩ =>
          (if e = (v, w) then b (u, v, w) else 0) -
          (if e = (u, w) then b (u, v, w) else 0) +
          (if e = (u, v) then b (u, v, w) else 0)))
