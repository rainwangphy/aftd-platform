import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCliqueBlowup

/-!
# simple_graph_clique_blowup_edist

Topic: graphs   Node: d8a9eb0bc526

Provenance: helper lemma. Claim 1 in the proof of arXiv:2610.09300 (On graphs whose powers are well-covered), Theorem 1.6; serves forall_power_well_covered_iff_clique_blowup.

In the clique blow-up H of G, two vertices x ∈ Q_i and y ∈ Q_j with i ≠ j are at the same distance in H as v_i and v_j in G (including distance ∞ when disconnected).
-/

theorem simple_graph_clique_blowup_walk_proj {V : Type*} (G : SimpleGraph V) (a : V → ℕ)
    {p q : Σ i, Fin (a i)} (w : (simple_graph_clique_blowup G a).Walk p q) :
    ∃ w' : G.Walk p.1 q.1, w'.length ≤ w.length := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | @cons x y z h w ih =>
    obtain ⟨w', hw'⟩ := ih
    rw [SimpleGraph.Walk.length_cons]
    have h' : (x.1 = y.1 ∧ x ≠ y) ∨ G.Adj x.1 y.1 := h
    rcases h' with ⟨hxy, -⟩ | h'
    · exact ⟨w'.copy hxy.symm rfl, by rw [SimpleGraph.Walk.length_copy]; omega⟩
    · exact ⟨SimpleGraph.Walk.cons h' w', by rw [SimpleGraph.Walk.length_cons]; omega⟩

theorem simple_graph_clique_blowup_walk_lift {V : Type*} (G : SimpleGraph V) (a : V → ℕ)
    (ha : ∀ i, 0 < a i) {i j : V} (w : G.Walk i j) :
    ∀ p q : Σ i, Fin (a i), p.1 = i → q.1 = j → 1 ≤ w.length →
      ∃ w' : (simple_graph_clique_blowup G a).Walk p q, w'.length ≤ w.length := by
  induction w with
  | nil => intro p q _ _ h; simp at h
  | @cons x y z h w ih =>
    intro p q hp hq _
    by_cases hw : w.length = 0
    · have hyz : y = z := SimpleGraph.Walk.eq_of_length_eq_zero hw
      have hadj : (simple_graph_clique_blowup G a).Adj p q :=
        Or.inr (by rw [hp, hq, ← hyz]; exact h)
      refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
      simp
    · obtain ⟨w', hw'⟩ := ih ⟨y, ⟨0, ha y⟩⟩ q rfl hq (Nat.one_le_iff_ne_zero.2 hw)
      have hadj : (simple_graph_clique_blowup G a).Adj p ⟨y, ⟨0, ha y⟩⟩ :=
        Or.inr (by rw [hp]; exact h)
      refine ⟨SimpleGraph.Walk.cons hadj w', ?_⟩
      simp only [SimpleGraph.Walk.length_cons]; omega

theorem simple_graph_clique_blowup_edist {V : Type*} (G : SimpleGraph V) (a : V → ℕ)
    (ha : ∀ i, 0 < a i) (p q : Σ i, Fin (a i)) (hpq : p.1 ≠ q.1) :
    (simple_graph_clique_blowup G a).edist p q = G.edist p.1 q.1 := by
  apply le_antisymm
  · by_cases htop : G.edist p.1 q.1 = ⊤
    · rw [htop]; exact le_top
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
    have h1 : 1 ≤ w.length := by
      by_contra h0
      exact hpq (SimpleGraph.Walk.eq_of_length_eq_zero (p := w) (by omega))
    obtain ⟨w', hw'⟩ := simple_graph_clique_blowup_walk_lift G a ha w p q rfl rfl h1
    calc (simple_graph_clique_blowup G a).edist p q ≤ w'.length := SimpleGraph.edist_le w'
      _ ≤ w.length := by exact_mod_cast hw'
      _ = G.edist p.1 q.1 := hw
  · by_cases htop : (simple_graph_clique_blowup G a).edist p q = ⊤
    · rw [htop]; exact le_top
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
    obtain ⟨w', hw'⟩ := simple_graph_clique_blowup_walk_proj G a w
    calc G.edist p.1 q.1 ≤ w'.length := SimpleGraph.edist_le w'
      _ ≤ w.length := by exact_mod_cast hw'
      _ = _ := hw
