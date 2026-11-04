import AFTD.Prelude

/-!
# wiener_index_dist_diff_twin_independent_set

Topic: graphs   Node: 831a1bac1af7

Provenance: helper lemma. arXiv:2611.01808 Lemma 2

Let G and H be simple graphs on a finite vertex type V, where G is connected. Suppose Z and X are subsets of V such that 2 ≤ Nat.card X, Z is an independent set in G (∀ u ∈ Z, ∀ v ∈ Z, ¬G.Adj u v), every vertex in Z has open neighborhood X in G (∀ z ∈ Z, G.neighborSet z = X), G ≤ H, and every edge of H is either an edge of G or has both endpoints in Z (∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z)). Then for any two vertices u and v in V: if u and v are adjacent in H but not adjacent in G, then G.dist u v = H.dist u v + 1; and if not (H.Adj u v ∧ ¬G.Adj u v), then G.dist u v = H.dist u v.
-/

private lemma wiener_index_dist_diff_twin_independent_set_twin_adj_X {V : Type*}
    (G : SimpleGraph V) (Z X : Set V)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X) :
    ∀ z ∈ Z, ∀ x ∈ X, G.Adj z x := by
  intro z hz x hx
  have h : x ∈ G.neighborSet z := by rw [hZneigh z hz]; exact hx
  rwa [SimpleGraph.mem_neighborSet] at h

private lemma wiener_index_dist_diff_twin_independent_set_new_ends {V : Type*}
    (G H : SimpleGraph V) (Z : Set V)
    (hGH_edges : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z))
    {a b : V} (hab : H.Adj a b) (hn : ¬G.Adj a b) : a ∈ Z ∧ b ∈ Z := by
  rcases hGH_edges a b hab with h | h
  · exact absurd h hn
  · exact h

private lemma wiener_index_dist_diff_twin_independent_set_Z_dist_le_two {V : Type*}
    (G : SimpleGraph V) (Z X : Set V)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X) (hXne : X.Nonempty)
    {u v : V} (hu : u ∈ Z) (hv : v ∈ Z) : G.dist u v ≤ 2 := by
  obtain ⟨x, hx⟩ := hXne
  have hux : G.Adj u x := wiener_index_dist_diff_twin_independent_set_twin_adj_X G Z X hZneigh u hu x hx
  have hvx : G.Adj v x := wiener_index_dist_diff_twin_independent_set_twin_adj_X G Z X hZneigh v hv x hx
  have hle := SimpleGraph.dist_le
    (SimpleGraph.Walk.cons hux (SimpleGraph.Walk.cons hvx.symm SimpleGraph.Walk.nil))
  simpa using hle

private lemma wiener_index_dist_diff_twin_independent_set_edge_dist_le_two {V : Type*}
    (G H : SimpleGraph V) (Z X : Set V)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X) (hXne : X.Nonempty)
    (hGH_edges : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z))
    {a b : V} (hab : H.Adj a b) : G.dist a b ≤ 2 := by
  rcases hGH_edges a b hab with h | ⟨ha, hb⟩
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr h]; norm_num
  · exact wiener_index_dist_diff_twin_independent_set_Z_dist_le_two G Z X hZneigh hXne ha hb

private lemma wiener_index_dist_diff_twin_independent_set_twin_dist {V : Type*}
    (G : SimpleGraph V) (Z X : Set V) (hGconn : G.Connected)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X)
    {u a v : V} (hu : u ∈ Z) (ha : a ∈ Z) (hva : v ≠ a) :
    G.dist u v ≤ G.dist a v := by
  obtain ⟨p, hp⟩ := hGconn.exists_walk_length_eq_dist a v
  have hpos : 0 < p.length := by rw [hp]; exact hGconn.pos_dist_of_ne hva.symm
  have hnil : ¬ p.Nil := by rwa [SimpleGraph.Walk.not_nil_iff_lt_length]
  have h1 : G.Adj a p.snd := p.adj_snd hnil
  have hsX : p.snd ∈ X := by
    rw [← hZneigh a ha]
    exact (SimpleGraph.mem_neighborSet G a p.snd).mpr h1
  have hus : G.Adj u p.snd := wiener_index_dist_diff_twin_independent_set_twin_adj_X G Z X hZneigh u hu p.snd hsX
  have hle := SimpleGraph.dist_le (SimpleGraph.Walk.cons hus p.tail)
  rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_tail_add_one hnil] at hle
  rw [hp] at hle
  exact hle

private lemma wiener_index_dist_diff_twin_independent_set_core_dist {V : Type*}
    (G H : SimpleGraph V) (Z X : Set V) (hGconn : G.Connected)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X)
    (hGH_edges : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z))
    (hXne : X.Nonempty) :
    ∀ (n : ℕ), 2 ≤ n → ∀ (u v : V) (p : H.Walk u v), p.length = n → G.dist u v ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn u v p hp
    have hnil : ¬ p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
    have htail : p.tail.length + 1 = n := by
      rw [SimpleGraph.Walk.length_tail_add_one hnil]; exact hp
    have h1 : H.Adj u p.snd := p.adj_snd hnil
    by_cases hn2 : n = 2
    · have htl1 : p.tail.length = 1 := by omega
      have hadj : H.Adj p.snd v := SimpleGraph.Walk.adj_of_length_eq_one htl1
      by_cases hG : G.Adj u p.snd
      · by_cases hG2 : G.Adj p.snd v
        · calc G.dist u v ≤ G.dist u p.snd + G.dist p.snd v := hGconn.dist_triangle
            _ = 1 + 1 := by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hG, SimpleGraph.dist_eq_one_iff_adj.mpr hG2]
            _ = n := by omega
        · have hends := wiener_index_dist_diff_twin_independent_set_new_ends G H Z hGH_edges hadj hG2
          have huX : u ∈ X := by
            rw [← hZneigh p.snd hends.1]
            exact (SimpleGraph.mem_neighborSet G p.snd u).mpr hG.symm
          have huv : G.Adj u v := (wiener_index_dist_diff_twin_independent_set_twin_adj_X G Z X hZneigh v hends.2 u huX).symm
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr huv]; omega
      · have hZua := wiener_index_dist_diff_twin_independent_set_new_ends G H Z hGH_edges h1 hG
        by_cases hveq : v = p.snd
        · rw [hveq]
          have h2' : G.dist u p.snd ≤ 2 := wiener_index_dist_diff_twin_independent_set_Z_dist_le_two G Z X hZneigh hXne hZua.1 hZua.2
          omega
        · have ht := wiener_index_dist_diff_twin_independent_set_twin_dist G Z X hGconn hZneigh hZua.1 hZua.2 hveq
          have he : G.dist p.snd v ≤ 2 := wiener_index_dist_diff_twin_independent_set_edge_dist_le_two G H Z X hZneigh hXne hGH_edges hadj
          omega
    · have hn3 : 3 ≤ n := by omega
      have htlge2 : 2 ≤ p.tail.length := by omega
      have htllt : p.tail.length < n := by omega
      have ihd : G.dist p.snd v ≤ p.tail.length := ih p.tail.length htllt htlge2 p.snd v p.tail rfl
      by_cases hG : G.Adj u p.snd
      · calc G.dist u v ≤ G.dist u p.snd + G.dist p.snd v := hGconn.dist_triangle
          _ = 1 + G.dist p.snd v := by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hG]
          _ ≤ 1 + p.tail.length := by omega
          _ = n := by omega
      · have hZua := wiener_index_dist_diff_twin_independent_set_new_ends G H Z hGH_edges h1 hG
        by_cases hveq : v = p.snd
        · rw [hveq]
          have h2' : G.dist u p.snd ≤ 2 := wiener_index_dist_diff_twin_independent_set_Z_dist_le_two G Z X hZneigh hXne hZua.1 hZua.2
          omega
        · have ht := wiener_index_dist_diff_twin_independent_set_twin_dist G Z X hGconn hZneigh hZua.1 hZua.2 hveq
          omega

/-- Distances in H differ from distances in G by 1 for newly added edges in Z, and are unchanged elsewhere. -/
theorem wiener_index_dist_diff_twin_independent_set
    {V : Type*} [Fintype V]
    (G H : SimpleGraph V) (hGconn : G.Connected)
    (Z X : Set V) (hXcard : 2 ≤ Nat.card X)
    (hZindep : ∀ u ∈ Z, ∀ v ∈ Z, ¬G.Adj u v)
    (hZneigh : ∀ z ∈ Z, G.neighborSet z = X)
    (hGH_le : G ≤ H)
    (hGH_edges : ∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ Z ∧ v ∈ Z))
    (u v : V) :
    (H.Adj u v ∧ ¬G.Adj u v → G.dist u v = H.dist u v + 1) ∧
    (¬(H.Adj u v ∧ ¬G.Adj u v) → G.dist u v = H.dist u v) := by
  have hXne : X.Nonempty := by
    by_contra hx
    rw [Set.not_nonempty_iff_eq_empty] at hx
    rw [hx] at hXcard
    simp at hXcard
  have Hconn : H.Connected := hGconn.mono hGH_le
  constructor
  · rintro ⟨hHuv, hnotG⟩
    have hHdist : H.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hHuv
    have hZuv : u ∈ Z ∧ v ∈ Z := wiener_index_dist_diff_twin_independent_set_new_ends G H Z hGH_edges hHuv hnotG
    have hGle : G.dist u v ≤ 2 := wiener_index_dist_diff_twin_independent_set_Z_dist_le_two G Z X hZneigh hXne hZuv.1 hZuv.2
    have hne : u ≠ v := hHuv.ne
    have hpos : 0 < G.dist u v := hGconn.pos_dist_of_ne hne
    have hne1 : G.dist u v ≠ 1 := by
      intro h1; exact hnotG (SimpleGraph.dist_eq_one_iff_adj.mp h1)
    have hGdist : G.dist u v = 2 := by omega
    rw [hGdist, hHdist]
  · intro hnn
    have hHG : H.dist u v ≤ G.dist u v := (hGconn u v).dist_anti hGH_le
    have hGH : G.dist u v ≤ H.dist u v := by
      rcases lt_or_ge (H.dist u v) 2 with hlt | hge
      · have hcases : H.dist u v = 0 ∨ H.dist u v = 1 := by omega
        rcases hcases with h0 | h1
        · have huveq : u = v := Hconn.dist_eq_zero_iff.mp h0
          have hg0 : G.dist u v = 0 := by rw [huveq, SimpleGraph.dist_self]
          omega
        · have hHuv : H.Adj u v := SimpleGraph.dist_eq_one_iff_adj.mp h1
          have hGuv : G.Adj u v := by
            by_contra hc; exact hnn ⟨hHuv, hc⟩
          have hgd : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hGuv
          omega
      · obtain ⟨p, hp⟩ := Hconn.exists_walk_length_eq_dist u v
        have hb : G.dist u v ≤ p.length :=
          wiener_index_dist_diff_twin_independent_set_core_dist G H Z X hGconn hZneigh hGH_edges hXne p.length (by omega) u v p rfl
        rw [← hp]; exact hb
    omega
