import AFTD.Prelude

/-!
# has_induced_k4_subdivision

Topic: graphs   Node: eecd313e00e6

Provenance: formalization of a published result. Source: arXiv:2610.32404, definition of ISK4-freeness and Lemma 11.1. The standard induced subdivision is encoded by six paths with disjoint interiors whose union is induced.

A graph G contains an induced subdivision of K4: there are four distinct branch vertices and one simple path for each of their six unordered pairs. No branch vertex is internal to a path; distinct paths share only branch vertices; and every G-edge between vertices of their union is an edge of one of the paths.
-/

/-- Contains an induced subdivision of K4, encoded by six internally disjoint simple paths between four distinct branch vertices, with no extra edges on their union. -/
def has_induced_k4_subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
∃ (b : Fin 4 → V), Function.Injective b ∧
    ∃ (P : (e : {ij : Fin 4 × Fin 4 // ij.1 < ij.2}) →
      G.Walk (b e.val.1) (b e.val.2)),
      (∀ e, (P e).IsPath) ∧
      (∀ e i, b i ∈ (P e).support → i = e.val.1 ∨ i = e.val.2) ∧
      (∀ e f, e ≠ f → ∀ v, v ∈ (P e).support → v ∈ (P f).support →
        ∃ i, v = b i) ∧
      (∀ x y, (∃ e, x ∈ (P e).support) → (∃ e, y ∈ (P e).support) →
        G.Adj x y → ∃ e, s(x, y) ∈ (P e).edges)
