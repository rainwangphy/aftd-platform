import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Tcs.IsClawFreeTripleNeighbors

/-!
# op309_clawfree_cubic_at_most_one_triangle_free_edge

Topic: graphs   Node: cedb3e0b9658

Provenance: helper lemma. Step towards op309_claw_free_cubic_rich_neighbor_five (OP-309): the triangle-free edges of a claw-free cubic graph form a matching.

In a finite claw-free cubic graph, no vertex has two distinct edges that lie in no triangle; that is, if vx and vy are distinct edges and neither has a common neighbour of its endpoints, we get a contradiction.
-/

theorem op309_clawfree_cubic_at_most_one_triangle_free_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hclaw : IsClawFree G)
    (hdegree : ∀ v, G.degree v = 3) (v x y : V)
    (hx : G.Adj v x) (hy : G.Adj v y) (hxy : x ≠ y)
    (hxT : ∀ w, ¬ (G.Adj v w ∧ G.Adj x w)) (hyT : ∀ w, ¬ (G.Adj v w ∧ G.Adj y w)) :
    False := by
  have h3 : (G.neighborFinset v).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact hdegree v
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp h3
  have ha : G.Adj v a := (G.mem_neighborFinset v a).mp (by rw [hN]; simp)
  have hb : G.Adj v b := (G.mem_neighborFinset v b).mp (by rw [hN]; simp)
  have hc : G.Adj v c := (G.mem_neighborFinset v c).mp (by rw [hN]; simp)
  have tri : ∃ p q, p ≠ q ∧ G.Adj v p ∧ G.Adj v q ∧ G.Adj p q := by
    rcases is_claw_free_triple_neighbors G hclaw v a b c ha hb hc hab hbc hac with h | h | h
    · exact ⟨a, b, hab, ha, hb, h⟩
    · exact ⟨a, c, hac, ha, hc, h⟩
    · exact ⟨b, c, hbc, hb, hc, h⟩
  obtain ⟨p, q, hpq, hp, hq, hpq'⟩ := tri
  have hpx : p ≠ x := by rintro rfl; exact hxT q ⟨hq, hpq'⟩
  have hpy : p ≠ y := by rintro rfl; exact hyT q ⟨hq, hpq'⟩
  have hqx : q ≠ x := by rintro rfl; exact hxT p ⟨hp, hpq'.symm⟩
  have hqy : q ≠ y := by rintro rfl; exact hyT p ⟨hp, hpq'.symm⟩
  have hsub : ({p, q, x, y} : Finset V) ⊆ G.neighborFinset v := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rw [G.mem_neighborFinset]
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({p, q, x, y} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hxy]
    · simp [hqx, hqy]
    · simp [hpq, hpx, hpy]
  have := Finset.card_le_card hsub
  rw [hcard, G.card_neighborFinset_eq_degree, hdegree] at this
  omega
