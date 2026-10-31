import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.SimpleGraphPowerWellCoveredNotBallUnionSubset
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# bipartite_ravindra_matching_power_two_well_covered_diam_le_two

Topic: graphs   Node: 2841aba4226f

Provenance: helper lemma. step towards bipartite_all_powers_well_covered_diameter_le_two

If a finite connected bipartite simple graph G admits a perfect matching M with complete bipartite neighborhoods and its second power G^2 is well-covered, then G has diameter at most 2.
-/

theorem bipartite_rav_edist_le_two_iff {V : Type*} (G : SimpleGraph V) (a b : V) :
    G.edist a b ≤ 2 ↔ a = b ∨ G.Adj a b ∨ ∃ z, G.Adj a z ∧ G.Adj z b := by
  constructor
  · intro h
    have hne : G.edist a b ≠ ⊤ := fun e => by rw [e] at h; exact absurd h (by decide)
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
    rw [← hp] at h
    have hl : p.length ≤ 2 := by exact_mod_cast h
    match p, hl with
    | .nil, _ => exact Or.inl rfl
    | .cons h1 .nil, _ => exact Or.inr (Or.inl h1)
    | .cons h1 (.cons h2 .nil), _ => exact Or.inr (Or.inr ⟨_, h1, h2⟩)
    | .cons _ (.cons _ (.cons _ q)), hl => simp at hl
  · rintro (rfl | h | ⟨z, h1, h2⟩)
    · simp
    · exact (SimpleGraph.edist_le (SimpleGraph.Walk.cons h .nil)).trans (by simp)
    · exact (SimpleGraph.edist_le (SimpleGraph.Walk.cons h1 (.cons h2 .nil))).trans (by simp)

/-- If a connected bipartite graph admits a Ravindra matching and its square G^2 is well-covered, then diam(G) <= 2. -/
theorem bipartite_ravindra_matching_power_two_well_covered_diam_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (hbip : G.IsBipartite)
    (M : SimpleGraph.Subgraph G) (hM : M.IsPerfectMatching)
    (hrav : ∀ u v : V, M.Adj u v → ∀ x y : V, G.Adj u x → G.Adj v y → G.Adj x y)
    (hwc2 : simple_graph_is_well_covered (simple_graph_power G 2)) :
    G.diam ≤ 2 := by
  classical
  obtain ⟨C⟩ := hbip
  have f2 : ∀ a b c : Fin 2, a ≠ b → b ≠ c → a = c := by decide
  have hpart : ∀ v, ∃ v', M.Adj v v' := fun v => (hM.1 (hM.2 v)).exists
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  have hmin : ∀ v, G.degree u ≤ G.degree v := fun v => hu ▸ G.minDegree_le_degree v
  -- step 3: y ∈ N(u), y' partner of y ⟹ N(y') = N(u)
  have st3 : ∀ y, G.Adj u y → ∀ y', M.Adj y y' → ∀ z, G.Adj y' z ↔ G.Adj u z := by
    intro y huy y' hyy'
    have hsub : G.neighborFinset y' ⊆ G.neighborFinset u := by
      intro z hz
      rw [SimpleGraph.mem_neighborFinset] at hz ⊢
      exact hrav y y' hyy' u z huy.symm hz
    have heq : G.neighborFinset y' = G.neighborFinset u :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree]
        exact hmin y')
    intro z
    rw [← SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborFinset, heq]
  obtain ⟨u', huu'⟩ := hpart u
  have Guu' : G.Adj u u' := M.adj_sub huu'
  -- step 4: y ∈ N(u) ⟹ N(y) ⊆ N(u')
  have st4 : ∀ y, G.Adj u y → ∀ x, G.Adj y x → G.Adj u' x := by
    intro y huy x hyx
    obtain ⟨y', hyy'⟩ := hpart y
    exact (hrav y y' hyy' x u' hyx ((st3 y huy y' hyy' u').2 Guu')).symm
  -- key: w ∈ N(u') ⟹ partner of w ∈ N(u)
  have key : ∀ w, G.Adj u' w → ∀ w', M.Adj w w' → G.Adj u w' := by
    intro w huw w' hww'
    by_contra hnot
    have Gww' : G.Adj w w' := M.adj_sub hww'
    have hsub : ∀ z, G.Adj w' z → G.Adj u' z := fun z hz => hrav w w' hww' u' z huw.symm hz
    have hcw' : C w' ≠ C u := by
      have h1 : C w' = C u' := f2 _ _ _ (C.valid Gww').symm (C.valid huw).symm
      rw [h1]; exact (C.valid Guu').symm
    have hn : ¬ G.edist u w' ≤ 2 := by
      intro h2
      rcases (bipartite_rav_edist_le_two_iff G u w').1 h2 with e | e | ⟨z, h1, h2⟩
      · exact hcw' (e ▸ rfl)
      · exact hnot e
      · exact hcw' (f2 _ _ _ (C.valid h2).symm (C.valid h1).symm)
    have h3 : (2 : ℕ∞) + 1 ≤ G.edist u w' := Order.add_one_le_of_lt (lt_of_not_ge hn)
    have hst : ((2 + 1 : ℕ) : ℕ∞) ≤ G.edist u w' := by exact_mod_cast h3
    apply simple_graph_power_well_covered_not_ball_union_subset G 2 (by norm_num) hwc2 u w' u' hst
    intro x hx
    simp only [Nat.cast_ofNat, bipartite_rav_edist_le_two_iff] at hx ⊢
    rcases hx with (rfl | e | ⟨z, h1, h2⟩) | (rfl | e | ⟨z, h1, h2⟩)
    · exact Or.inr (Or.inl Guu'.symm)
    · exact Or.inr (Or.inr ⟨u, Guu'.symm, e⟩)
    · exact Or.inr (Or.inl (st4 z h1 x h2))
    · exact Or.inr (Or.inr ⟨w, huw, Gww'⟩)
    · exact Or.inr (Or.inl (hsub x e))
    · exact Or.inr (Or.inr ⟨z, hsub z h1, h2⟩)
  -- A-vertices: N(w) = N(u)
  have stA : ∀ w, G.Adj u' w → ∀ z, G.Adj w z ↔ G.Adj u z := by
    intro w huw
    obtain ⟨w', hww'⟩ := hpart w
    exact st3 w' (key w huw w' hww') w hww'.symm
  have hall : ∀ v, G.Adj u' v ∨ G.Adj u v := by
    intro v
    obtain ⟨p⟩ := hconn.preconnected u v
    have : ∀ a b (q : G.Walk a b), (G.Adj u' a ∨ G.Adj u a) → (G.Adj u' b ∨ G.Adj u b) := by
      intro a b q
      induction q with
      | nil => exact id
      | cons hac _ ih =>
        intro ha
        apply ih
        rcases ha with ha | ha
        · exact Or.inr ((stA _ ha _).1 hac)
        · exact Or.inl (st4 _ ha _ hac)
    exact this u v p (Or.inl Guu'.symm)
  have hdist : ∀ a b, G.edist a b ≤ 2 := by
    intro a b
    rw [bipartite_rav_edist_le_two_iff]
    rcases hall a with ha | ha <;> rcases hall b with hb | hb
    · exact Or.inr (Or.inr ⟨u', ha.symm, hb⟩)
    · exact Or.inr (Or.inl ((stA a ha b).2 hb))
    · exact Or.inr (Or.inl ((stA b hb a).2 ha).symm)
    · exact Or.inr (Or.inr ⟨u, ha.symm, hb⟩)
  exact ENat.toNat_le_of_le_natCast (SimpleGraph.ediam_le_iff.2 hdist)
