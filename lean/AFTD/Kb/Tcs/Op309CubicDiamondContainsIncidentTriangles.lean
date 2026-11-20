import AFTD.Prelude

/-!
# op309_cubic_diamond_contains_incident_triangles

Topic: graphs   Node: ccf906b63244

Provenance: helper lemma. Triangle and diamond decomposition for OP-309.

In a finite cubic simple graph, every triangle meeting a diamond is contained in that diamond.
-/

theorem op309_diamond_incident_nbrs3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u a b c : V) (hdeg : G.degree u = 3)
    (ha : G.Adj u a) (hb : G.Adj u b) (hc : G.Adj u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ t, G.Adj u t → t = a ∨ t = b ∨ t = c := by
  intro t ht
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hsub : ({a, b, c, t} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [G.mem_neighborFinset]
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, t} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h3)]
    · simp [hbc, Ne.symm h2]
    · simp [hab, hac, Ne.symm h1]
  have := Finset.card_le_card hsub
  rw [hcard, G.card_neighborFinset_eq_degree, hdeg] at this
  omega

theorem op309_cubic_diamond_contains_incident_triangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdegree : ∀ v, G.degree v = 3)
    (u v a b x y z : V) (hdist : [u,v,a,b].Nodup)
    (huv : G.Adj u v) (hua : G.Adj u a) (hub : G.Adj u b)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : ¬ G.Adj a b)
    (hx : x = u ∨ x = v ∨ x = a ∨ x = b)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    (y = u ∨ y = v ∨ y = a ∨ y = b) ∧
    (z = u ∨ z = v ∨ z = a ∨ z = b) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hdist
  obtain ⟨⟨huv', hua', hub'⟩, ⟨hva', hvb'⟩, hab', -⟩ := hdist
  have Nu := op309_diamond_incident_nbrs3 G u v a b (hdegree u) huv hua hub hva' hvb' hab'
  have Nv := op309_diamond_incident_nbrs3 G v u a b (hdegree v) huv.symm hva hvb hua' hub' hab'
  have hyz' : y ≠ z := hyz.ne
  -- a vertex with two adjacent neighbours y z, one of which lies in {u, v}
  have key : ∀ w, (w = a ∨ w = b) → G.Adj w u → G.Adj w v → G.Adj w y → G.Adj w z →
      (y = u ∨ y = v ∨ y = a ∨ y = b) ∧ (z = u ∨ z = v ∨ z = a ∨ z = b) := by
    intro w hw hwu hwv hwy hwz
    have huv2 : u ≠ v := huv'
    by_cases hyuv : y = u ∨ y = v
    · rcases hyuv with rfl | rfl
      · rcases Nu z hyz with h | h | h <;> simp [h]
      · rcases Nv z hyz with h | h | h <;> simp [h]
    · push Not at hyuv
      have hz : z = u ∨ z = v := by
        by_contra hz
        push Not at hz
        rcases op309_diamond_incident_nbrs3 G w u v y (hdegree w) hwu hwv hwy huv2
          (Ne.symm hyuv.1) (Ne.symm hyuv.2) z hwz with h | h | h
        · exact hz.1 h
        · exact hz.2 h
        · exact hyz' h.symm
      rcases hz with rfl | rfl
      · rcases Nu y hyz.symm with h | h | h <;> simp [h]
      · rcases Nv y hyz.symm with h | h | h <;> simp [h]
  rcases hx with rfl | rfl | rfl | rfl
  · rcases Nu y hxy with h | h | h <;> rcases Nu z hxz with h' | h' | h' <;> simp [h, h']
  · rcases Nv y hxy with h | h | h <;> rcases Nv z hxz with h' | h' | h' <;> simp [h, h']
  · exact key x (Or.inl rfl) hua.symm hva.symm hxy hxz
  · exact key x (Or.inr rfl) hub.symm hvb.symm hxy hxz
