import AFTD.Prelude

/-!
# has_vertex_disjoint_paths

Topic: approximation   Node: e5a7fabe5f88

Provenance: formalization of a published result. Source: arXiv:2611.06209, Section 4

A graph Q and p terminal pairs (s_i, t_i) admit mutually vertex-disjoint paths if there exist paths P_i from s_i to t_i whose vertex sets are pairwise disjoint.
-/

/-- Existence of mutually vertex-disjoint paths in graph Q connecting p terminal pairs. -/
def has_vertex_disjoint_paths {V : Type*}
    (Q : SimpleGraph V) (p : ℕ) (s t : Fin p → V) : Prop := ∃ P : (i : Fin p) → Q.Walk (s i) (t i),
    (∀ i, (P i).IsPath) ∧ ∀ i j, i ≠ j → (P i).support.Disjoint (P j).support
