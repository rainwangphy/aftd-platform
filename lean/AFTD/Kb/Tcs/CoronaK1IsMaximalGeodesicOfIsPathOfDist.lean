import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.Tcs.IsMaximalGeodesic

/-!
# corona_k1_is_maximal_geodesic_of_isPath_of_dist

Topic: graphs   Node: 5d3c170aec9d

Provenance: helper lemma. step towards edge_geodesic_transversal_number_corona_k1

In the corona product corona_k1 G of a finite graph G, every walk between distinct pendant leaves Sum.inr u and Sum.inr v that is a path and has length equal to the distance between them is a maximal geodesic.
-/

lemma corona_k1_is_maximal_geodesic_of_isPath_of_dist_dist_le
    {V : Type*} (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (p : (corona_k1 G).Walk (Sum.inr u) (Sum.inr v)) :
    (corona_k1 G).dist (Sum.inl u) (Sum.inr v) ≤ p.length := by
  cases p with
  | nil => contradiction
  | cons h p' =>
    rename_i w
    cases w with
    | inl x =>
      have hx : u = x := h
      subst hx
      have hle := SimpleGraph.dist_le p'
      simp only [SimpleGraph.Walk.length_cons]
      omega
    | inr x =>
      exact False.elim h

/-- Every shortest path (geodesic) between distinct pendant leaves in the corona product corona_k1 G is a maximal geodesic. -/
theorem corona_k1_is_maximal_geodesic_of_isPath_of_dist
    {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (p : (corona_k1 G).Walk (Sum.inr u) (Sum.inr v))
    (hp : p.IsPath ∧ p.length = (corona_k1 G).dist (Sum.inr u) (Sum.inr v)) :
    is_maximal_geodesic p := by
  refine ⟨hp, ?_, ?_⟩
  · intro w hw
    cases w with
    | inl x =>
      have hx : x = u := hw
      cases hx
      exact corona_k1_is_maximal_geodesic_of_isPath_of_dist_dist_le G u v huv p
    | inr x =>
      exact False.elim hw
  · intro w hw
    cases w with
    | inl x =>
      have hx : v = x := hw
      cases hx
      rw [SimpleGraph.dist_comm]
      have hrev := corona_k1_is_maximal_geodesic_of_isPath_of_dist_dist_le G v u huv.symm p.reverse
      rw [SimpleGraph.Walk.length_reverse] at hrev
      exact hrev
    | inr x =>
      exact False.elim hw
