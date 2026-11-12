import AFTD.Prelude

/-!
# graph_defect

Topic: combinatorics   Node: e5dea1056f8b

Provenance: formalization of a published result. Source: arXiv:2611.14160 Definition 3.6

Let G be a graph on a finite vertex type α and let t be a natural number. The defect def_t(G) is the least nonnegative integer d such that every Z_t-labeling of the complete graph on 2|α| vertices either has the property that every copy of G has a vertex-disjoint copy of the same weight, or contains two copies of G of different weights on some vertex subset of size at most |α| + d.
-/

/-- The defect def_t(G) of a graph G on n vertices is the least nonnegative integer d such that every Z_t-labeling of K_{2n} either has a vertex-disjoint copy of the same weight for every copy of G, or some set of at most n+d vertices contains two copies of G with different weights. -/
noncomputable def graph_defect {α : Type*} [Fintype α] (G : SimpleGraph α) (t : ℕ) : ℕ :=
  sInf {d : ℕ |
    let copyWeight (C : SimpleGraph.TopEdgeLabeling (Fin (2 * Fintype.card α)) (ZMod t))
        (f : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))) : ZMod t :=
      open Classical in ∑ e : G.edgeSet, C (f.mapEdgeSet e)
    ∀ (C : SimpleGraph.TopEdgeLabeling (Fin (2 * Fintype.card α)) (ZMod t)),
      (∀ (f₁ : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))),
        ∃ (f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))),
          Disjoint (Set.range f₁) (Set.range f₂) ∧
          copyWeight C f₁ = copyWeight C f₂) ∨
      (∃ (U : Finset (Fin (2 * Fintype.card α))), U.card ≤ Fintype.card α + d ∧
        ∃ (f₁ f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))),
          (∀ v, f₁ v ∈ U) ∧ (∀ v, f₂ v ∈ U) ∧
          copyWeight C f₁ ≠ copyWeight C f₂)}
