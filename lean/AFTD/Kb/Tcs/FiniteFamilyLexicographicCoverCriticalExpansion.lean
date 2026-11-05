import AFTD.Prelude

/-!
# finite_family_lexicographic_cover_critical_expansion

Topic: graphs   Node: d2e485efb5cf

Provenance: helper lemma. Elementary transversal exchange, the multi-point form of the private-member argument.

For a finite set family and covers H and C, suppose C has minimum cardinality and, among minimum covers, minimizes the number of points outside H. Every nonempty subset X of C outside H has strictly more than |X| points of H among those family members whose C-points all belong to X.
-/

theorem finite_family_lexicographic_cover_critical_expansion
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (H C : Finset α)
    (hH : ∀ t ∈ F, ¬ Disjoint H t)
    (hC : ∀ t ∈ F, ¬ Disjoint C t)
    (hlex : ∀ D : Finset α, (∀ t ∈ F, ¬ Disjoint D t) →
      C.card ≤ D.card ∧ (D.card = C.card → (C \ H).card ≤ (D \ H).card)) :
    ∀ X : Finset α, X ⊆ C \ H → X.Nonempty →
      X.card < (H ∩ ((F.filter (fun t => t ∩ C ⊆ X)).biUnion id)).card := by
  classical
  intro X hX hXne
  let N : Finset α := H ∩ ((F.filter (fun t => t ∩ C ⊆ X)).biUnion id)
  have hXC : X ⊆ C := fun x hx => (Finset.mem_sdiff.mp (hX hx)).1
  have hNH : N ⊆ H := Finset.inter_subset_left
  have hCN : Disjoint C N := by
    apply Finset.disjoint_left.mpr
    intro a haC haN
    have haH : a ∈ H := hNH haN
    obtain ⟨t, htF, hat⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp haN).2
    have htX : t ∩ C ⊆ X := (Finset.mem_filter.mp htF).2
    have haX : a ∈ X := htX (Finset.mem_inter.mpr ⟨hat, haC⟩)
    exact (Finset.mem_sdiff.mp (hX haX)).2 haH
  let D := (C \ X) ∪ N
  have hDN : Disjoint (C \ X) N := hCN.mono_left Finset.sdiff_subset
  have hDcover : ∀ t ∈ F, ¬ Disjoint D t := by
    intro t ht hdis
    have htX : t ∩ C ⊆ X := by
      intro a ha
      have hat := (Finset.mem_inter.mp ha).1
      have haC := (Finset.mem_inter.mp ha).2
      by_contra haX
      have haD : a ∈ D := Finset.mem_union_left N (Finset.mem_sdiff.mpr ⟨haC, haX⟩)
      exact (Finset.disjoint_left.mp hdis) haD hat
    obtain ⟨a, haH, hat⟩ := Finset.not_disjoint_iff.mp (hH t ht)
    have haN : a ∈ N := Finset.mem_inter.mpr ⟨haH,
      Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, htX⟩, hat⟩⟩
    exact (Finset.disjoint_left.mp hdis) (Finset.mem_union_right _ haN) hat
  have hDcard : D.card = C.card - X.card + N.card := by
    rw [show D = (C \ X) ∪ N from rfl, Finset.card_union_of_disjoint hDN,
      Finset.card_sdiff_of_subset hXC]
  have hDoutside : D \ H = (C \ H) \ X := by
    ext a
    simp only [D, Finset.mem_sdiff, Finset.mem_union]
    have ha : a ∈ N → a ∈ H := fun h => hNH h
    aesop
  have hDoutsidecard : (D \ H).card = (C \ H).card - X.card := by
    rw [hDoutside, Finset.card_sdiff_of_subset hX]
  obtain ⟨hminimum, hsecondary⟩ := hlex D hDcover
  have hXpos : 0 < X.card := Finset.card_pos.mpr hXne
  have hle : X.card ≤ C.card := Finset.card_le_card hXC
  have hle2 : X.card ≤ (C \ H).card := Finset.card_le_card hX
  change X.card < N.card
  by_contra hbad
  have heq : D.card = C.card := by omega
  have hh := hsecondary heq
  omega
