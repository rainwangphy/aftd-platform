import AFTD.Prelude

/-!
# simple_graph_k4_attachment_of_two_triangle_edge_covers

Topic: graphs   Node: 922ab82d4d26

Provenance: helper lemma. Elementary core of the pair-stable forced-K4 attachment reduction for simple_graph_triangle_cover_number_le_two_mul_packing_number.

Let two families P and Q meet every triangle of a graph in an edge, with all members of Q triangles. In a four-clique abcx, suppose no member of P contains ax or bx and no member of Q contains ab or cx. Then a member of P contains a vertex y outside abcx and either contains a or b with xy present, or contains x with ay or by present. Neither family needs to be a packing.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

private theorem two_of_inter_three {V : Type*} [DecidableEq V] (s : Finset V) (a b x : V)
    (h : 2 ≤ (s ∩ {a,b,x}).card) :
    (a ∈ s ∧ b ∈ s) ∨ (a ∈ s ∧ x ∈ s) ∨ (b ∈ s ∧ x ∈ s) := by
  classical
  by_contra hn
  have hle : (s ∩ {a,b,x}).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu hv
    aesop
  omega

private theorem third_vertex_of_three {V : Type*} [DecidableEq V] (s : Finset V)
    (a x : V) (hcard : s.card = 3) (ha : a ∈ s) (hx : x ∈ s) :
    ∃ y ∈ s, y ≠ a ∧ y ≠ x := by
  classical
  by_contra hn
  have hsub : s ⊆ {a,x} := by
    intro y hy
    simp only [not_exists, not_and] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hn2
    exact hn y hy (by aesop) (by aesop)
  have hc := Finset.card_le_card hsub
  have htwo := Finset.card_le_two (a := a) (b := x)
  omega

theorem two_covers_k4_attachment_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P Q : Finset (Finset V)) (a b c x : V)
    (hax : a ≠ x) (hbx : b ≠ x)
    (habx : G.IsNClique 3 ({a,b,x} : Finset V))
    (hPcover : ∀ s : Finset V, G.IsNClique 3 s → ∃ t ∈ P, 2 ≤ (t ∩ s).card)
    (hQcover : ∀ s : Finset V, G.IsNClique 3 s → ∃ t ∈ Q, 2 ≤ (t ∩ s).card)
    (hQtri : ∀ t ∈ Q, G.IsNClique 3 t)
    (hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t))
    (havoid : ∀ t ∈ Q, ¬ (a ∈ t ∧ b ∈ t) ∧ ¬ (c ∈ t ∧ x ∈ t)) :
    ∃ t ∈ P, t ≠ ({a,b,c} : Finset V) ∧ ∃ y ∈ t,
      y ∉ ({a,b,c,x} : Finset V) ∧
      (((a ∈ t ∨ b ∈ t) ∧ G.Adj x y) ∨
        (x ∈ t ∧ (G.Adj a y ∨ G.Adj b y))) := by
  classical
  obtain ⟨q, hqQ, hmeet⟩ := hQcover {a,b,x} habx
  have hqcl := hQtri q hqQ
  have hqa := havoid q hqQ
  have hv : ∃ v : V, (v = a ∨ v = b) ∧ v ∈ q ∧ x ∈ q := by
    rcases two_of_inter_three q a b x hmeet with hab | hax | hbx
    · exact False.elim (hqa.1 hab)
    · exact ⟨a, Or.inl rfl, hax.1, hax.2⟩
    · exact ⟨b, Or.inr rfl, hbx.1, hbx.2⟩
  obtain ⟨v, hvab, hvq, hxq⟩ := hv
  have hvx : v ≠ x := by rcases hvab with rfl | rfl <;> assumption
  obtain ⟨y, hyq, hyv, hyx⟩ := third_vertex_of_three q v x hqcl.card_eq hvq hxq
  have hyoutside : y ∉ ({a,b,c,x} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases hvab with rfl | rfl <;> aesop
  have hqeq : ({v,x,y} : Finset V) = q := by
    apply Finset.eq_of_subset_of_card_le
    · simp [Finset.insert_subset, hvq, hxq, hyq]
    · have hcard : ({v,x,y} : Finset V).card = 3 := by simp [hvx, hyv, hyx, Ne.symm hvx, Ne.symm hyv, Ne.symm hyx]
      have hcq := hqcl.card_eq
      omega
  have hxy : G.Adj x y := hqcl.isClique hxq hyq (Ne.symm hyx)
  have hvy : G.Adj v y := hqcl.isClique hvq hyq (Ne.symm hyv)
  obtain ⟨t, htP, htp⟩ := hPcover q hqcl
  rw [← hqeq] at htp
  have hnotvx : ¬ (v ∈ t ∧ x ∈ t) := by
    rcases hvab with rfl | rfl
    · intro h; exact (hspokes t htP).1 ⟨h.2, h.1⟩
    · intro h; exact (hspokes t htP).2 ⟨h.2, h.1⟩
  have hyt : y ∈ t := by
    rcases two_of_inter_three t v x y htp with hvx' | hvy' | hxy'
    · exact False.elim (hnotvx hvx')
    · exact hvy'.2
    · exact hxy'.2
  have htne : t ≠ ({a,b,c} : Finset V) := by
    intro h
    apply hyoutside
    rw [h] at hyt
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyt ⊢
    aesop
  rcases two_of_inter_three t v x y htp with hvx' | hvy' | hxy'
  · exact False.elim (hnotvx hvx')
  · refine ⟨t, htP, htne, y, hvy'.2, hyoutside, Or.inl ⟨?_, hxy⟩⟩
    rcases hvab with rfl | rfl <;> aesop
  · refine ⟨t, htP, htne, y, hxy'.2, hyoutside, Or.inr ⟨hxy'.1, ?_⟩⟩
    rcases hvab with rfl | rfl <;> aesop

theorem two_covers_k4_attachment {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P Q : Finset (Finset V)) (a b c x : V)
    (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset V))
    (hPcover : ∀ s : Finset V, G.IsNClique 3 s → ∃ t ∈ P, 2 ≤ (t ∩ s).card)
    (hQcover : ∀ s : Finset V, G.IsNClique 3 s → ∃ t ∈ Q, 2 ≤ (t ∩ s).card)
    (hQtri : ∀ t ∈ Q, G.IsNClique 3 t)
    (hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t))
    (havoid : ∀ t ∈ Q, ¬ (a ∈ t ∧ b ∈ t) ∧ ¬ (c ∈ t ∧ x ∈ t)) :
    ∃ t ∈ P, t ≠ ({a,b,c} : Finset V) ∧ ∃ y ∈ t,
      y ∉ ({a,b,c,x} : Finset V) ∧
      (((a ∈ t ∨ b ∈ t) ∧ G.Adj x y) ∨
        (x ∈ t ∧ (G.Adj a y ∨ G.Adj b y))) := by
  classical
  have hax : a ≠ x := by
    intro h; subst x
    have hsub : ({a,b,c,a} : Finset V) ⊆ {a,b,c} := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; aesop
    have hc := Finset.card_le_card hsub
    have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have hbx : b ≠ x := by
    intro h; subst x
    have hsub : ({a,b,c,b} : Finset V) ⊆ {a,b,c} := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢; aesop
    have hc := Finset.card_le_card hsub
    have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have hab : a ≠ b := by
    intro h; subst b
    have hsub : ({a,a,c,x} : Finset V) ⊆ {a,c,x} := by simp
    have hc := Finset.card_le_card hsub
    have h3 := Finset.card_le_three (a := a) (b := c) (c := x)
    have h4 := hk4.card_eq
    omega
  have habx : G.IsNClique 3 ({a,b,x} : Finset V) := by
    refine ⟨SimpleGraph.IsClique.subset ?_ hk4.isClique, ?_⟩
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop
    · simp [hab, hax, hbx, Ne.symm hab, Ne.symm hax, Ne.symm hbx]
  exact two_covers_k4_attachment_core G P Q a b c x hax hbx habx hPcover hQcover hQtri hspokes havoid

theorem simple_graph_k4_attachment_of_two_triangle_edge_covers (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P Q : Finset (Finset (Fin n))) (a b c x : Fin n) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) (hPcover : ∀ s : Finset (Fin n), G.IsNClique 3 s → ∃ t ∈ P, 2 ≤ (t ∩ s).card) (hQcover : ∀ s : Finset (Fin n), G.IsNClique 3 s → ∃ t ∈ Q, 2 ≤ (t ∩ s).card) (hQtri : ∀ t ∈ Q, G.IsNClique 3 t) (hspokes : ∀ t ∈ P, ¬ (x ∈ t ∧ a ∈ t) ∧ ¬ (x ∈ t ∧ b ∈ t)) (havoid : ∀ t ∈ Q, ¬ (a ∈ t ∧ b ∈ t) ∧ ¬ (c ∈ t ∧ x ∈ t)) : ∃ t ∈ P, t ≠ ({a,b,c} : Finset (Fin n)) ∧ ∃ y ∈ t, y ∉ ({a,b,c,x} : Finset (Fin n)) ∧ (((a ∈ t ∨ b ∈ t) ∧ G.Adj x y) ∨ (x ∈ t ∧ (G.Adj a y ∨ G.Adj b y))) := by
  exact two_covers_k4_attachment G P Q a b c x hk4 hPcover hQcover hQtri hspokes havoid
