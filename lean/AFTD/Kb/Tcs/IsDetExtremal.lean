import AFTD.Prelude

/-!
# is_det_extremal

Topic: graphs   Node: f746198e65b4

Provenance: formalization of a published result. Source: arXiv:2611.16649 Sec. 1, p. 2

A finite graph G is det-extremal if it admits an equitable bipartition into parts of equal size n such that the absolute value of the determinant of its biadjacency matrix equals the permanent.
-/

/-- A finite bipartite graph is det-extremal if its biadjacency matrix has |det B| = per B. -/
def is_det_extremal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := ∃ (n : ℕ) (f g : Fin n → V),
    Function.Injective f ∧ Function.Injective g ∧
    Disjoint (Set.range f) (Set.range g) ∧
    (Set.range f ∪ Set.range g = Set.univ) ∧
    (∀ i j, ¬ G.Adj (f i) (f j)) ∧ (∀ i j, ¬ G.Adj (g i) (g j)) ∧
    |Matrix.det (fun i j => if G.Adj (f i) (g j) then (1 : ℤ) else 0)| =
      Matrix.permanent (fun i j => if G.Adj (f i) (g j) then (1 : ℤ) else 0)
