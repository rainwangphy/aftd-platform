import AFTD.Prelude
import AFTD.Kb.Tcs.IsCograph
import AFTD.Kb.Tcs.IsDistanceHereditary

/-!
# cograph_is_distance_hereditary

Topic: graphs   Node: 83be708aa655

Provenance: formalization of a published result. Source: arXiv:2610.13820, Fact 4.4

Every finite cograph is distance-hereditary.
-/

private lemma cograph_is_distance_hereditary_dist_le_two {α : Type*} (F : SimpleGraph α)
    (hF : is_cograph F) (u v : α) : F.dist u v ≤ 2 := by
  by_contra h
  have hne : F.dist u v ≠ 0 := by omega
  obtain ⟨p, hp, hlen⟩ := SimpleGraph.Reachable.exists_path_of_dist
    (SimpleGraph.Reachable.of_dist_ne_zero hne)
  have hlen3 : 3 ≤ p.length := by omega
  have hinj := hp.getVert_injOn
  have hdist : ∀ i j : ℕ, i ≤ p.length → j ≤ p.length → i ≠ j →
      p.getVert i ≠ p.getVert j := by
    intro i j hi hj hij heq
    exact hij (hinj hi hj heq)
  have hchord : ∀ i j : ℕ, i + 2 ≤ j → j ≤ p.length → ¬ F.Adj (p.getVert i) (p.getVert j) := by
    intro i j hij hj hadj
    have hi : i ≤ p.length := by omega
    have hlen' : ((p.take i).append ((hadj.toWalk).append (p.drop j))).length
        = i + 1 + (p.length - j) := by
      simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
        SimpleGraph.Walk.drop_length, Nat.min_eq_left hi]
      omega
    have hle := F.dist_le ((p.take i).append ((hadj.toWalk).append (p.drop j)))
    rw [hlen'] at hle
    omega
  refine hF ⟨p.getVert 0, p.getVert 1, p.getVert 2, p.getVert 3,
    hdist 0 1 (by omega) (by omega) (by decide),
    hdist 0 2 (by omega) (by omega) (by decide),
    hdist 0 3 (by omega) (by omega) (by decide),
    hdist 1 2 (by omega) (by omega) (by decide),
    hdist 1 3 (by omega) (by omega) (by decide),
    hdist 2 3 (by omega) (by omega) (by decide),
    p.adj_getVert_succ (by omega), p.adj_getVert_succ (by omega),
    p.adj_getVert_succ (by omega),
    hchord 0 2 (by omega) (by omega), hchord 0 3 (by omega) (by omega),
    hchord 1 3 (by omega) (by omega)⟩

private lemma cograph_is_distance_hereditary_induce {α : Type*} (F : SimpleGraph α) (s : Set α)
    (hF : is_cograph F) : is_cograph (SimpleGraph.induce s F) := by
  rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, eab, ebc, ecd, nac, nad, nbd⟩
  refine hF ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hab (Subtype.ext h)
  · exact fun h => hac (Subtype.ext h)
  · exact fun h => had (Subtype.ext h)
  · exact fun h => hbc (Subtype.ext h)
  · exact fun h => hbd (Subtype.ext h)
  · exact fun h => hcd (Subtype.ext h)
  · exact SimpleGraph.induce_adj.mp eab
  · exact SimpleGraph.induce_adj.mp ebc
  · exact SimpleGraph.induce_adj.mp ecd
  · exact fun h => nac (SimpleGraph.induce_adj.mpr h)
  · exact fun h => nad (SimpleGraph.induce_adj.mpr h)
  · exact fun h => nbd (SimpleGraph.induce_adj.mpr h)

/-- Every finite cograph is distance-hereditary. -/
theorem cograph_is_distance_hereditary {α : Type*} [Fintype α] (F : SimpleGraph α)
    (hF : is_cograph F) : is_distance_hereditary F := by
  intro s u v hreach
  let φ : (SimpleGraph.induce s F) →g F :=
    { toFun := Subtype.val, map_rel' := fun {x y} h => SimpleGraph.induce_adj.mp h }
  have hreachF : F.Reachable (↑u) (↑v) := hreach.map φ
  have h1 : F.dist (↑u) (↑v) ≤ (SimpleGraph.induce s F).dist u v := by
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    have h := F.dist_le (p.map φ)
    rw [SimpleGraph.Walk.length_map, hp] at h
    exact h
  have h2 : F.dist (↑u) (↑v) ≤ 2 := cograph_is_distance_hereditary_dist_le_two F hF _ _
  have h3 : (SimpleGraph.induce s F).dist u v ≤ 2 :=
    cograph_is_distance_hereditary_dist_le_two (SimpleGraph.induce s F)
      (cograph_is_distance_hereditary_induce F s hF) _ _
  by_cases heq : (↑u : α) = ↑v
  · have hv : v = u := (Subtype.ext heq).symm
    simp [hv]
  have huv : u ≠ v := fun h => heq (by rw [h])
  by_cases hadj : F.Adj (↑u) (↑v)
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj,
      SimpleGraph.dist_eq_one_iff_adj.mpr (SimpleGraph.induce_adj.mpr hadj)]
  · have hpos1 : 0 < F.dist (↑u) (↑v) := hreachF.pos_dist_of_ne heq
    have hne1 : F.dist (↑u) (↑v) ≠ 1 := fun h =>
      hadj (SimpleGraph.dist_eq_one_iff_adj.mp h)
    have hpos2 : 0 < (SimpleGraph.induce s F).dist u v := hreach.pos_dist_of_ne huv
    have hne2 : (SimpleGraph.induce s F).dist u v ≠ 1 := fun h =>
      (fun hh => hadj (SimpleGraph.induce_adj.mp hh)) (SimpleGraph.dist_eq_one_iff_adj.mp h)
    omega
