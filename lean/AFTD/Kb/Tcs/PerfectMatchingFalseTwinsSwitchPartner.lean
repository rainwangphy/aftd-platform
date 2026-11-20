import AFTD.Prelude
import AFTD.Kb.Tcs.PerfectMatchingReplaceFinitePairedVertices

/-!
# perfect_matching_false_twins_switch_partner

Topic: graphs   Node: c111e5e28ed4

Provenance: helper lemma. Four-vertex matching switch for the saturated-twin equality branch of OP-1957.

If distinct vertices have identical open neighborhoods and a perfect matching contains an edge incident to one of them, another perfect matching avoids that edge.
-/

theorem perfect_matching_false_twins_switch_partner {V : Type*} (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching) (x y z : V) (hxy : x ≠ y) (htwin : G.neighborSet x = G.neighborSet y) (hxz : P.Adj x z) : ∃ Q : G.Subgraph, Q.IsPerfectMatching ∧ ¬ Q.Adj x z := by
  classical
  have hnxy : ¬ G.Adj x y := by
    intro h
    have hy : G.Adj y y := by
      change y ∈ G.neighborSet y
      rw [← htwin]
      exact h
    exact G.irrefl hy
  have hyx : ¬ G.Adj y x := fun h => hnxy h.symm
  have hmap : ∀ a b, G.Adj a b → G.Adj (Equiv.swap x y a) (Equiv.swap x y b) := by
    intro a b hab
    by_cases hax : a = x
    · subst a
      have hbx : b ≠ x := fun h => G.irrefl (h ▸ hab)
      have hby : b ≠ y := fun h => hnxy (h ▸ hab)
      have hyb : G.Adj y b := by
        change b ∈ G.neighborSet y
        rw [← htwin]
        exact hab
      simpa [Equiv.swap_apply_of_ne_of_ne hbx hby] using hyb
    · by_cases hay : a = y
      · subst a
        have hbx : b ≠ x := fun h => hyx (h ▸ hab)
        have hby : b ≠ y := fun h => G.irrefl (h ▸ hab)
        have hxb : G.Adj x b := by
          change b ∈ G.neighborSet x
          rw [htwin]
          exact hab
        simpa [Equiv.swap_apply_of_ne_of_ne hbx hby] using hxb
      · by_cases hbx : b = x
        · subst b
          have hya : G.Adj y a := by
            change a ∈ G.neighborSet y
            rw [← htwin]
            exact hab.symm
          simpa [Equiv.swap_apply_of_ne_of_ne hax hay] using hya.symm
        · by_cases hby : b = y
          · subst b
            have hxa : G.Adj x a := by
              change a ∈ G.neighborSet x
              rw [htwin]
              exact hab.symm
            simpa [Equiv.swap_apply_of_ne_of_ne hax hay] using hxa.symm
          · simpa [Equiv.swap_apply_of_ne_of_ne hax hay,
              Equiv.swap_apply_of_ne_of_ne hbx hby] using hab
  let f : G →g G := ⟨Equiv.swap x y, fun {a b} h => hmap a b h⟩
  let Q := P.map f
  have hmatch : Q.IsMatching := hP.1.map f (Equiv.swap x y).injective
  have hspan : Q.IsSpanning := by
    rw [SimpleGraph.Subgraph.isSpanning_iff]
    ext a
    simp only [Q, SimpleGraph.Subgraph.map_verts, hP.2.verts_eq_univ, Set.image_univ,
      Set.mem_univ, iff_true]
    exact ⟨(Equiv.swap x y) a, by simp [f]⟩
  refine ⟨Q, ⟨hmatch, hspan⟩, ?_⟩
  intro h
  have hzx : z ≠ x := fun h => G.irrefl (h ▸ hxz.adj_sub)
  have hzy : z ≠ y := fun h => hnxy (h ▸ hxz.adj_sub)
  have hsz : Equiv.swap x y z = z := Equiv.swap_apply_of_ne_of_ne hzx hzy
  obtain ⟨a, b, hab, ha, hb⟩ := h
  have ha' : a = y := (Equiv.swap x y).injective (by simpa [f] using ha)
  have hb' : b = z := (Equiv.swap x y).injective (by simpa [f, hsz] using hb)
  subst a
  subst b
  exact hxy (hP.1.eq_of_adj_right hxz hab)
