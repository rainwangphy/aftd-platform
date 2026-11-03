import AFTD.Prelude

/-!
# finite_family_packing_cover_certificate_map

Topic: graphs   Node: 2555b3495512

Provenance: helper lemma. Injective relabeling for the two-vertex separator route of the triangle packing campaign.

An injective relabeling transports finite-family disjoint packings and point covers, preserving the factor-two certificate.
-/

theorem finite_family_packing_cover_certificate_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (F P : Finset (Finset α)) (C : Finset α)
    (hsub : P ⊆ F) (hpack : (P : Set (Finset α)).Pairwise Disjoint)
    (hcover : ∀ A ∈ F, ¬ Disjoint A C) (hbound : C.card ≤ 2 * P.card) :
    ∃ Q : Finset (Finset β), ∃ D : Finset β,
      Q ⊆ F.image (fun s => s.map f) ∧ (Q : Set (Finset β)).Pairwise Disjoint ∧
      (∀ B ∈ F.image (fun s => s.map f), ¬ Disjoint B D) ∧ D.card ≤ 2 * Q.card := by
  classical
  let fm : Finset α ↪ Finset β := ⟨fun s => s.map f, Finset.map_injective f⟩
  let Q := P.map fm
  let D := C.map f
  have hQsub : Q ⊆ F.image (fun s => s.map f) := by
    intro A hA
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hA
    exact Finset.mem_image.mpr ⟨s,hsub hs,rfl⟩
  have hQpack : (Q : Set (Finset β)).Pairwise Disjoint := by
    intro A hA B hB hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hB
    have hne' : a ≠ b := by intro h; exact hne (congrArg fm h)
    change Disjoint (a.map f) (b.map f)
    exact (Finset.disjoint_map f).mpr (hpack ha hb hne')
  have hQcover : ∀ B ∈ F.image (fun s => s.map f), ¬ Disjoint B D := by
    intro B hB hdisj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hB
    apply hcover a ha
    exact (Finset.disjoint_map f).mp hdisj
  refine ⟨Q,D,hQsub,hQpack,hQcover,?_⟩
  simpa [Q,D] using hbound
