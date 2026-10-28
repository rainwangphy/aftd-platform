import AFTD.Prelude
import AFTD.Kb.Tcs.IsCaterpillarIsTree
import AFTD.Kb.Tcs.IsCaterpillar
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# is_caterpillar_iso_of_card_le_three

Topic: graphs   Node: 0acbd184bd74

Provenance: helper lemma. step towards caterpillar_third_t_chromatic_specialization_fiber_le_two

Any two caterpillars on at most 3 vertices with equal vertex counts are isomorphic.
-/

open SimpleGraph in
/-- A walk from `x` to `y` with `x ≠ y` and `¬ G.Adj x y` starts with an edge from `x`
to a vertex other than `y`. -/
private lemma is_caterpillar_iso_of_card_le_three_aux_walk_nbr
    {V : Type*} {G : SimpleGraph V} {x y : V} (h : G.Reachable x y)
    (hxy : x ≠ y) (hna : ¬ G.Adj x y) : ∃ z, G.Adj x z ∧ z ≠ y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hxy
  | cons hd tl => exact ⟨_, hd, fun he => hna (he ▸ hd)⟩

open SimpleGraph in
/-- A tree contains no triangle. -/
private lemma is_caterpillar_iso_of_card_le_three_aux_no_triangle
    {V : Type*} {G : SimpleGraph V} {v x y : V} (hG : G.IsTree)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : G.Adj x y) : False := by
  have hyx : G.Adj y x := hxy.symm
  obtain ⟨p, -, huniq⟩ := hG.existsUnique_path v x
  have hpA : (Walk.cons hvx Walk.nil : G.Walk v x).IsPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨Walk.IsPath.nil, ?_⟩
    simp only [Walk.support_nil, List.mem_singleton]
    exact hvx.ne
  have hpB : (Walk.cons hvy (Walk.cons hyx Walk.nil) : G.Walk v x).IsPath := by
    rw [Walk.cons_isPath_iff]
    refine ⟨?_, ?_⟩
    · rw [Walk.cons_isPath_iff]
      refine ⟨Walk.IsPath.nil, ?_⟩
      simp only [Walk.support_nil, List.mem_singleton]
      exact hyx.ne
    · intro hmem
      rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hvy.ne h
      · exact hvx.ne h
  have hA : (Walk.cons hvx Walk.nil : G.Walk v x).length = 1 := by simp
  have hB : (Walk.cons hvy (Walk.cons hyx Walk.nil) : G.Walk v x).length = 2 := by simp
  have hlen : (Walk.cons hvx Walk.nil : G.Walk v x).length
      = (Walk.cons hvy (Walk.cons hyx Walk.nil) : G.Walk v x).length := by
    rw [huniq _ hpA, huniq _ hpB]
  rw [hA, hB] at hlen
  omega

open SimpleGraph in
/-- A tree on at most three vertices has a vertex adjacent to every other vertex. -/
private theorem is_caterpillar_iso_of_card_le_three_aux_dom
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.IsTree)
    (hle : Fintype.card V ≤ 3) : ∃ v : V, ∀ w : V, w ≠ v → G.Adj v w := by
  haveI : Nonempty V := hG.connected.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  have hconn : G.Preconnected := hG.connected.preconnected
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hlt2 | hge2
  · have hcard1 : Fintype.card V = 1 := by omega
    haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    exact ⟨Classical.arbitrary V, fun w hw => absurd (Subsingleton.elim w _) hw⟩
  · rcases Nat.lt_or_ge (Fintype.card V) 3 with hlt3 | hge3
    · have hc2 : Fintype.card V = 2 := by omega
      obtain ⟨a, b, hab, huniv⟩ :=
        (Finset.card_eq_two (s := (Finset.univ : Finset V))).mp
          (by rw [Finset.card_univ]; exact hc2)
      have hmem2 : ∀ x : V, x = a ∨ x = b := by
        intro x
        have h : x ∈ ({a, b} : Finset V) := huniv ▸ Finset.mem_univ x
        simpa using h
      refine ⟨a, fun w hw => ?_⟩
      rcases hmem2 w with h | h
      · exact absurd h hw
      · rw [h]
        obtain ⟨p⟩ := hconn a b
        cases p with
        | nil => exact absurd rfl hab
        | cons hd tl =>
            rcases hmem2 _ with h' | h'
            · exact absurd h' hd.ne'
            · exact h' ▸ hd
    · have hc3 : Fintype.card V = 3 := by omega
      obtain ⟨a, b, c, hab, hac, hbc, huniv⟩ :=
        (Finset.card_eq_three (s := (Finset.univ : Finset V))).mp
          (by rw [Finset.card_univ]; exact hc3)
      have hmem : ∀ x : V, x = a ∨ x = b ∨ x = c := by
        intro x
        have h : x ∈ ({a, b, c} : Finset V) := huniv ▸ Finset.mem_univ x
        simpa [Finset.mem_insert, Finset.mem_singleton] using h
      have third : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ z ≠ x ∧ z ≠ y :=
        fun x y hxy hna => by
          obtain ⟨z, hz1, hz2⟩ :=
            is_caterpillar_iso_of_card_le_three_aux_walk_nbr (hconn x y) hxy hna
          exact ⟨z, hz1, hz1.ne', hz2⟩
      by_cases h1 : G.Adj a b
      · by_cases h2 : G.Adj a c
        · refine ⟨a, fun w hw => ?_⟩
          rcases hmem w with h | h | h
          · exact absurd h hw
          · rw [h]; exact h1
          · rw [h]; exact h2
        · obtain ⟨z, hz1, hz2, hz3⟩ := third c a hac.symm (fun h => h2 h.symm)
          have hzb : z = b := by
            rcases hmem z with h | h | h
            · exact absurd h hz3
            · exact h
            · exact absurd h hz2
          have hbc' : G.Adj b c := (hzb ▸ hz1).symm
          refine ⟨b, fun w hw => ?_⟩
          rcases hmem w with h | h | h
          · rw [h]; exact h1.symm
          · exact absurd h hw
          · rw [h]; exact hbc'
      · obtain ⟨y, hy1, hy2, hy3⟩ := third a b hab h1
        have hyc : y = c := by
          rcases hmem y with h | h | h
          · exact absurd h hy2
          · exact absurd h hy3
          · exact h
        have hac' : G.Adj a c := hyc ▸ hy1
        obtain ⟨z, hz1, hz2, hz3⟩ := third b a hab.symm (fun h => h1 h.symm)
        have hzc : z = c := by
          rcases hmem z with h | h | h
          · exact absurd h hz3
          · exact absurd h hz2
          · exact h
        refine ⟨c, fun w hw => ?_⟩
        rcases hmem w with h | h | h
        · rw [h]; exact hac'.symm
        · rw [h]; exact (hzc ▸ hz1).symm
        · exact absurd h hw

open SimpleGraph in
/-- In a tree with at most three vertices, a vertex adjacent to every other vertex is
adjacent exactly to the other vertices. -/
private theorem is_caterpillar_iso_of_card_le_three_aux_adj
    {V : Type*} (G : SimpleGraph V) (hG : G.IsTree) {v : V}
    (hv : ∀ w : V, w ≠ v → G.Adj v w) :
    ∀ x y : V, G.Adj x y ↔ x ≠ y ∧ (x = v ∨ y = v) := by
  intro x y
  constructor
  · intro h
    refine ⟨h.ne, ?_⟩
    by_contra hc
    rw [not_or] at hc
    exact is_caterpillar_iso_of_card_le_three_aux_no_triangle hG (hv x hc.1) (hv y hc.2) h
  · rintro ⟨hxy, hxv | hyv⟩
    · rw [hxv] at hxy ⊢
      exact hv y hxy.symm
    · rw [hyv] at hxy ⊢
      exact (hv x hxy).symm

/-- Any two caterpillars on at most 3 vertices of the same order are isomorphic. -/
theorem is_caterpillar_iso_of_card_le_three
    {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
    (T₁ : SimpleGraph V₁) (T₂ : SimpleGraph V₂)
    (hT₁ : is_caterpillar T₁) (hT₂ : is_caterpillar T₂)
    (hcard : Fintype.card V₁ = Fintype.card V₂)
    (hle : Fintype.card V₁ ≤ 3) :
    Nonempty (T₁ ≃g T₂) := by
  have h1 : T₁.IsTree := is_caterpillar_isTree T₁ hT₁
  have h2 : T₂.IsTree := is_caterpillar_isTree T₂ hT₂
  have hle2 : Fintype.card V₂ ≤ 3 := hcard ▸ hle
  obtain ⟨v₁, hv₁⟩ := is_caterpillar_iso_of_card_le_three_aux_dom T₁ h1 hle
  obtain ⟨v₂, hv₂⟩ := is_caterpillar_iso_of_card_le_three_aux_dom T₂ h2 hle2
  have key₁ := is_caterpillar_iso_of_card_le_three_aux_adj T₁ h1 hv₁
  have key₂ := is_caterpillar_iso_of_card_le_three_aux_adj T₂ h2 hv₂
  obtain ⟨E⟩ := Fintype.card_eq.mp hcard
  have hex : ∀ x : V₁, E.trans (Equiv.swap (E v₁) v₂) x = v₂ ↔ x = v₁ := by
    intro x
    show Equiv.swap (E v₁) v₂ (E x) = v₂ ↔ x = v₁
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right, E.injective.eq_iff]
  have hne : ∀ x y : V₁, (E.trans (Equiv.swap (E v₁) v₂) x
      = E.trans (Equiv.swap (E v₁) v₂) y ↔ x = y) := by
    intro x y
    exact (Equiv.injective _).eq_iff
  refine ⟨RelIso.mk (E.trans (Equiv.swap (E v₁) v₂)) ?_⟩
  intro x y
  rw [key₂, key₁, hex x, hex y, ne_eq, ne_eq, hne x y]
