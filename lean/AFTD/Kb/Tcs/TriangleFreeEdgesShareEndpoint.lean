import AFTD.Prelude

/-!
# triangle_free_edges_share_endpoint

Topic: graphs   Node: f30624a175d6

Provenance: helper lemma. arXiv:2611.07924, Section 6, Theorem 6.1 proof

If a simple graph H with at least one edge is triangle-free and every pair of edges shares at least one vertex, then all edges of H share a common endpoint.
-/

/-- If a simple graph with at least one edge is triangle-free and every two edges intersect, then all edges share a common vertex. -/
theorem triangle_free_edges_share_endpoint {V : Type*} (H : SimpleGraph V)
    (he : ∃ a b : V, H.Adj a b)
    (htri : H.CliqueFree 3)
    (hpair : ∀ u v x y : V, H.Adj u v → H.Adj x y →
      u = x ∨ u = y ∨ v = x ∨ v = y) :
    ∃ c : V, ∀ u v : V, H.Adj u v → u = c ∨ v = c := by
  classical
  have tri_contra : ∀ {x y z : V}, H.Adj x y → H.Adj y z → H.Adj x z →
      x ≠ y → x ≠ z → y ≠ z → False := by
    intro x y z hxy hyz hxz hne1 hne2 hne3
    apply htri ({x, y, z} : Finset V)
    rw [SimpleGraph.isNClique_iff]
    constructor
    · rw [SimpleGraph.isClique_iff]
      simp [Set.Pairwise, hxy, hyz, hxz, H.adj_comm]
    · simp [hne1, hne2, hne3]
  obtain ⟨a, b, hab⟩ := he
  by_cases halla : ∀ u v : V, H.Adj u v → u = a ∨ v = a
  · exact ⟨a, halla⟩
  · push Not at halla
    obtain ⟨p, q, hpq, hpa, hqa⟩ := halla
    have hpbq : p = b ∨ q = b := by
      rcases hpair p q a b hpq hab with h | h | h | h
      · exact absurd h hpa
      · exact Or.inl h
      · exact absurd h hqa
      · exact Or.inr h
    refine ⟨b, ?_⟩
    intro u v huv
    by_contra hcon
    push Not at hcon
    obtain ⟨hub, hvb⟩ := hcon
    have hua_or_hva : u = a ∨ v = a := by
      rcases hpair u v a b huv hab with h | h | h | h
      · exact Or.inl h
      · exact absurd h hub
      · exact Or.inr h
      · exact absurd h hvb
    rcases hpbq with hpb | hqb
    · rcases hua_or_hva with hua | hva
      · have hqv : q = v := by
          rcases hpair p q u v hpq huv with h | h | h | h
          · exact absurd (by rw [← hua, ← h, hpb] : a = b) hab.ne
          · exact absurd (by rw [← h, hpb] : v = b) hvb
          · exact absurd (by rw [h, hua] : q = a) hqa
          · exact h
        rw [hpb] at hpq
        rw [hua, hqv.symm] at huv
        exact tri_contra hab hpq huv hab.ne hqa.symm hpq.ne
      · have hqu : q = u := by
          rcases hpair p q u v hpq huv with h | h | h | h
          · exact absurd (by rw [← h, hpb] : u = b) hub
          · exact absurd (by rw [← hva, ← h, hpb] : a = b) hab.ne
          · exact h
          · exact absurd (by rw [h, hva] : q = a) hqa
        rw [hpb] at hpq
        rw [hva, hqu.symm] at huv
        exact tri_contra hab hpq huv.symm hab.ne hqa.symm hpq.ne
    · rcases hua_or_hva with hua | hva
      · have hpv : p = v := by
          rcases hpair p q u v hpq huv with h | h | h | h
          · exact absurd (by rw [h, hua] : p = a) hpa
          · exact h
          · exact absurd (by rw [← hua, ← h, hqb] : a = b) hab.ne
          · exact absurd (by rw [← h, hqb] : v = b) hvb
        rw [hqb] at hpq
        rw [hua, hpv.symm] at huv
        exact tri_contra hab hpq.symm huv hab.ne hpa.symm hpq.ne.symm
      · have hpu : p = u := by
          rcases hpair p q u v hpq huv with h | h | h | h
          · exact h
          · exact absurd (by rw [← hva, h] : p = a) hpa
          · exact absurd (by rw [← h, hqb] : u = b) hub
          · exact absurd (by rw [← hva, ← h, hqb] : a = b) hab.ne
        rw [hqb] at hpq
        rw [hva, hpu.symm] at huv
        exact tri_contra hab hpq.symm huv.symm hab.ne hpa.symm hpq.ne.symm
