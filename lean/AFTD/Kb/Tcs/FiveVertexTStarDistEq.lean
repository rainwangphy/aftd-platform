import AFTD.Prelude
import AFTD.Kb.Tcs.FiveVertexTStar
import AFTD.Kb.Tcs.FiveVertexTStarAdjDecidable

/-!
# five_vertex_t_star_dist_eq

Topic: graphs   Node: 8e4eaca5db16

Provenance: helper lemma. step towards lly_positive_edge_connectivity_threshold_five

In the T-graph: d(0,1) = 1, d(0,2) = 2, d(3,1) = 2, d(4,1) = 2, d(3,2) = d(4,2) = 3.
-/

lemma five_vertex_t_star_dist_eq_walk_length_le_two {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.length ≤ 2) :
    u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v := by
  cases p with
  | nil => exact Or.inl rfl
  | cons h1 q =>
    cases q with
    | nil => exact Or.inr (Or.inl h1)
    | cons h2 r =>
      cases r with
      | nil => exact Or.inr (Or.inr ⟨_, h1, h2⟩)
      | cons h3 s =>
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega

/-- The six distances in the T-graph that both Wasserstein bounds need. `dist 0 2 = 2` by the triangle inequality through 1 plus non-adjacency; `dist 3 2 = 3` is the only non-trivial one: upper bound by the triangle 3-0-1-2, lower bound because a walk of length at most 2 would give a common neighbour of 3 and 2, and 3's only neighbour is 0 which is not adjacent to 2. -/
theorem five_vertex_t_star_dist_eq :
    five_vertex_t_star.dist 0 1 = 1 ∧ five_vertex_t_star.dist 0 2 = 2 ∧
      five_vertex_t_star.dist 3 1 = 2 ∧ five_vertex_t_star.dist 4 1 = 2 ∧
      five_vertex_t_star.dist 3 2 = 3 ∧ five_vertex_t_star.dist 4 2 = 3 := by
  have hconn : five_vertex_t_star.Connected := by decide
  have d01 : five_vertex_t_star.dist 0 1 = 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj]
    decide
  have d12 : five_vertex_t_star.dist 1 2 = 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj]
    decide
  have d30 : five_vertex_t_star.dist 3 0 = 1 := by
    rw [SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj]
    decide
  have d40 : five_vertex_t_star.dist 4 0 = 1 := by
    rw [SimpleGraph.dist_comm, SimpleGraph.dist_eq_one_iff_adj]
    decide
  have d02 : five_vertex_t_star.dist 0 2 = 2 := by
    have hle : five_vertex_t_star.dist 0 2 ≤ 2 := by
      have := hconn.dist_triangle (u := 0) (v := 1) (w := 2)
      omega
    have hlt : 1 < five_vertex_t_star.dist 0 2 :=
      hconn.one_lt_dist_of_ne_of_not_adj (by decide) (by decide)
    omega
  have d31 : five_vertex_t_star.dist 3 1 = 2 := by
    have hle : five_vertex_t_star.dist 3 1 ≤ 2 := by
      have := hconn.dist_triangle (u := 3) (v := 0) (w := 1)
      omega
    have hlt : 1 < five_vertex_t_star.dist 3 1 :=
      hconn.one_lt_dist_of_ne_of_not_adj (by decide) (by decide)
    omega
  have d41 : five_vertex_t_star.dist 4 1 = 2 := by
    have hle : five_vertex_t_star.dist 4 1 ≤ 2 := by
      have := hconn.dist_triangle (u := 4) (v := 0) (w := 1)
      omega
    have hlt : 1 < five_vertex_t_star.dist 4 1 :=
      hconn.one_lt_dist_of_ne_of_not_adj (by decide) (by decide)
    omega
  have d32 : five_vertex_t_star.dist 3 2 = 3 := by
    have hle : five_vertex_t_star.dist 3 2 ≤ 3 := by
      have := hconn.dist_triangle (u := 3) (v := 0) (w := 2)
      omega
    have hgt : ¬ (five_vertex_t_star.dist 3 2 ≤ 2) := by
      intro hle2
      obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist 3 2
      have hp2 : p.length ≤ 2 := by omega
      have hcases := five_vertex_t_star_dist_eq_walk_length_le_two p hp2
      revert hcases
      decide
    omega
  have d42 : five_vertex_t_star.dist 4 2 = 3 := by
    have hle : five_vertex_t_star.dist 4 2 ≤ 3 := by
      have := hconn.dist_triangle (u := 4) (v := 0) (w := 2)
      omega
    have hgt : ¬ (five_vertex_t_star.dist 4 2 ≤ 2) := by
      intro hle2
      obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist 4 2
      have hp2 : p.length ≤ 2 := by omega
      have hcases := five_vertex_t_star_dist_eq_walk_length_le_two p hp2
      revert hcases
      decide
    omega
  exact ⟨d01, d02, d31, d41, d32, d42⟩
