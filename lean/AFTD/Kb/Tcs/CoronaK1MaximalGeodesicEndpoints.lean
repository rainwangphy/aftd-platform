import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.Tcs.IsMaximalGeodesic

/-!
# corona_k1_maximal_geodesic_endpoints

Topic: graphs   Node: eb949b18949e

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 5 (The Edge Geodesic Transversal Problem)

For every finite type V with 2 ≤ Fintype.card V and every connected simple graph G on V, if p is a walk between x and y in corona_k1 G such that is_maximal_geodesic p, then there exist u v : V such that x = Sum.inr u ∧ y = Sum.inr v ∧ u ≠ v.
-/

lemma corona_k1_maximal_geodesic_endpoints_is_maximal_geodesic_reverse {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : is_maximal_geodesic p) : is_maximal_geodesic p.reverse := by
  refine ⟨⟨hp.1.1.reverse, ?_⟩, ?_, ?_⟩
  · rw [p.length_reverse, hp.1.2, G.dist_comm]
  · intro w hw
    rw [p.length_reverse]
    have := hp.2.2 w (G.adj_symm hw)
    rwa [G.dist_comm]
  · intro w hw
    rw [p.length_reverse]
    have := hp.2.1 w (G.adj_symm hw)
    rwa [G.dist_comm]

lemma corona_k1_maximal_geodesic_endpoints_exists_adj_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (u : V) : ∃ v : V, G.Adj u v := by
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (Nat.succ_le_iff.mp hn)
  obtain ⟨v, hv⟩ := exists_ne u
  obtain ⟨p⟩ := hG u v
  cases p with
  | nil => contradiction
  | cons hadj rest => exact ⟨_, hadj⟩

lemma corona_k1_maximal_geodesic_endpoints_adj_inr_inv {V : Type*} (G : SimpleGraph V) (u : V) {w : V ⊕ V}
    (h : (corona_k1 G).Adj (Sum.inr u) w) : w = Sum.inl u := by
  cases w with
  | inl v => exact congr_arg Sum.inl (h : u = v).symm
  | inr v => cases h

lemma corona_k1_maximal_geodesic_endpoints_walk_from_inr_length_le {V : Type*} (G : SimpleGraph V) (u : V) (y : V ⊕ V)
    (q : (corona_k1 G).Walk (Sum.inr u) y) (hy : y ≠ Sum.inr u) :
    (corona_k1 G).dist (Sum.inl u) y + 1 ≤ q.length := by
  cases q with
  | nil => contradiction
  | cons hadj rest =>
    have := corona_k1_maximal_geodesic_endpoints_adj_inr_inv G u hadj
    subst this
    have := (corona_k1 G).dist_le rest
    simp only [SimpleGraph.Walk.length_cons]
    omega

lemma corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl_of_ne {V : Type*} (G : SimpleGraph V) (u : V) (y : V ⊕ V)
    (p : (corona_k1 G).Walk (Sum.inl u) y) (hy : y ≠ Sum.inr u)
    (hp : is_maximal_geodesic p) : False := by
  have hadj : (corona_k1 G).Adj (Sum.inr u) (Sum.inl u) := rfl
  have hr : (corona_k1 G).Reachable (Sum.inr u) y := ⟨SimpleGraph.Walk.cons hadj p⟩
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  have hlen := corona_k1_maximal_geodesic_endpoints_walk_from_inr_length_le G u y q hy
  rw [hq] at hlen
  have hmax := hp.2.1 (Sum.inr u) hadj
  have hlen_p := hp.1.2
  omega

lemma corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl_inr {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (u : V)
    (p : (corona_k1 G).Walk (Sum.inl u) (Sum.inr u)) (hp : is_maximal_geodesic p) : False := by
  obtain ⟨v, huv⟩ := corona_k1_maximal_geodesic_endpoints_exists_adj_of_connected G hG hn u
  have hadj_w : (corona_k1 G).Adj (Sum.inl v) (Sum.inl u) := huv.symm
  have hdist_w := hp.2.1 (Sum.inl v) hadj_w
  have hp_len : p.length = 1 := by
    rw [hp.1.2]
    exact SimpleGraph.dist_eq_one_iff_adj.mpr (by exact rfl)
  rw [hp_len] at hdist_w
  have hlt : (corona_k1 G).dist (Sum.inl v) (Sum.inr u) < 2 := by omega
  interval_cases hd : (corona_k1 G).dist (Sum.inl v) (Sum.inr u)
  · rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at hd
    rcases hd with h1 | h2
    · contradiction
    · apply h2
      have h1 : (corona_k1 G).Adj (Sum.inl v) (Sum.inl u) := huv.symm
      have h2 : (corona_k1 G).Adj (Sum.inl u) (Sum.inr u) := rfl
      exact ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)⟩
  · rw [SimpleGraph.dist_eq_one_iff_adj] at hd
    have : (v = u) := hd
    subst this
    exact G.loopless.irrefl _ huv

lemma corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (hn : 2 ≤ Fintype.card V) (u : V) (y : V ⊕ V)
    (p : (corona_k1 G).Walk (Sum.inl u) y) (hp : is_maximal_geodesic p) : False := by
  by_cases hy : y = Sum.inr u
  · subst hy
    exact corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl_inr G hG hn u p hp
  · exact corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl_of_ne G u y p hy hp

lemma corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inr_self {V : Type*} (G : SimpleGraph V) (u : V)
    (p : (corona_k1 G).Walk (Sum.inr u) (Sum.inr u)) (hp : is_maximal_geodesic p) : False := by
  have hadj : (corona_k1 G).Adj (Sum.inl u) (Sum.inr u) := rfl
  have hdist := hp.2.1 (Sum.inl u) hadj
  have hlen : p.length = 0 := by
    rw [hp.1.2]
    exact SimpleGraph.dist_self
  rw [hlen] at hdist
  have hadj_dist : (corona_k1 G).dist (Sum.inl u) (Sum.inr u) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  omega

/-- Every maximal geodesic in G ⊙ K_1 has both endpoints at distinct pendant leaves. -/
theorem corona_k1_maximal_geodesic_endpoints
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    {x y : V ⊕ V} (p : (corona_k1 G).Walk x y) (hp : is_maximal_geodesic p) :
    ∃ u v : V, x = Sum.inr u ∧ y = Sum.inr v ∧ u ≠ v := by
  cases x with
  | inl u =>
    exfalso
    exact corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl G hG hn u y p hp
  | inr u =>
    cases y with
    | inl v =>
      exfalso
      have hp_rev := corona_k1_maximal_geodesic_endpoints_is_maximal_geodesic_reverse hp
      exact corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inl G hG hn v (Sum.inr u) p.reverse hp_rev
    | inr v =>
      refine ⟨u, v, rfl, rfl, ?_⟩
      rintro rfl
      exact corona_k1_maximal_geodesic_endpoints_not_maximal_geodesic_inr_self G u p hp
