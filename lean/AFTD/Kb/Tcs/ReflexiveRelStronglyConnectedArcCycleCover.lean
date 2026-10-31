import AFTD.Prelude

/-!
# reflexive_rel_strongly_connected_arc_cycle_cover

Topic: graphs   Node: be1e2ff7b74a

Provenance: helper lemma. step towards simple_graph_normalized_hop_group_quadratic_word_diameter

In a strongly connected reflexive relation, every arc u → v is realised by a single cycle cover: take a simple path v = y₀ → … → y_s = u and the cycle (y₀ … y_s), which fixes all other points.
-/

/-- Every arc of a strongly connected reflexive relation is realised by one cycle cover. -/
theorem reflexive_rel_strongly_connected_arc_cycle_cover {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (hR : ∀ v, R v v) (hsc : ∀ u v : V, Relation.ReflTransGen R u v)
    {u v : V} (huv : R u v) :
    ∃ p : Equiv.Perm V, (∀ x, R x (p x)) ∧ p u = v := by
  classical
  set W : V → Finset V := fun x => Finset.univ.filter (fun y => R x y ∧ y ≠ v) with hW
  have hmemW : ∀ x y : V, R x y → y ≠ v → y ∈ W x := by
    intro x y hxy hyv
    simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxy, hyv⟩
  have hallV : ∀ T : Finset V, (∀ x ∈ T, x ≠ u) → T.card ≤ (T.biUnion W).card := by
    intro T hTD
    by_cases hv : v ∈ T
    · have hsub : T.erase v ⊆ T.biUnion W := by
        intro x hx
        rw [Finset.mem_erase] at hx
        exact Finset.mem_biUnion.mpr ⟨x, hx.2, hmemW x x (hR x) hx.1⟩
      by_contra hcon
      push Not at hcon
      have hcard : (T.erase v).card = T.card - 1 := Finset.card_erase_of_mem hv
      have hAeq : T.erase v = T.biUnion W := Finset.eq_of_subset_of_card_le hsub (by omega)
      have hclosed : ∀ x ∈ T, ∀ y, R x y → y ∈ T := by
        intro x hx y hxy
        by_cases hyv : y = v
        · rw [hyv]; exact hv
        · have : y ∈ T.biUnion W := Finset.mem_biUnion.mpr ⟨x, hx, hmemW x y hxy hyv⟩
          rw [← hAeq] at this
          exact Finset.mem_of_mem_erase this
      have key : ∀ y, Relation.ReflTransGen R v y → y ∈ T := by
        intro y h
        induction h with
        | refl => exact hv
        | tail _ hbc ih => exact hclosed _ ih _ hbc
      exact hTD u (key u (hsc v u)) rfl
    · have hsub : T ⊆ T.biUnion W := by
        intro x hx
        have hxv : x ≠ v := fun h => hv (h ▸ hx)
        exact Finset.mem_biUnion.mpr ⟨x, hx, hmemW x x (hR x) hxv⟩
      exact Finset.card_le_card hsub
  set S : Finset V := Finset.univ.erase u with hS
  have huS : u ∉ S := by simp [hS]
  have hmemS : ∀ x : V, x ≠ u → x ∈ S := by
    intro x hx; simp [hS, hx]
  have hallS : ∀ T : Finset ↥S, T.card ≤ (T.biUnion fun x => W (x : V)).card := by
    intro T
    have hfinj : Function.Injective (fun x : ↥S => (x : V)) := Subtype.val_injective
    have himg : T.image (fun x : ↥S => (x : V)) ⊆ S := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
      exact x.2
    have hcard1 : (T.image (fun x : ↥S => (x : V))).card = T.card :=
      Finset.card_image_of_injective T hfinj
    have heq : (T.biUnion fun x => W (x : V)) = (T.image fun x : ↥S => (x : V)).biUnion W := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, hz⟩
        exact ⟨(x : V), ⟨x, hx, rfl⟩, hz⟩
      · rintro ⟨z', ⟨x, hx, rfl⟩, hz⟩
        exact ⟨x, hx, hz⟩
    rw [heq, ← hcard1]
    exact hallV _ fun x hx => Finset.ne_of_mem_erase (himg hx)
  obtain ⟨g, hginj, hgmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun x : ↥S => W (x : V))).mp hallS
  have hgR : ∀ x : ↥S, R (x : V) (g x) := fun x => (Finset.mem_filter.mp (hgmem x)).2.1
  have hgv : ∀ x : ↥S, g x ≠ v := fun x => (Finset.mem_filter.mp (hgmem x)).2.2
  set F : V → V := fun x => if h : x ∈ S then g ⟨x, h⟩ else v with hF
  have hFS : ∀ x (h : x ∈ S), F x = g ⟨x, h⟩ := by
    intro x h; simp only [hF]; rw [dif_pos h]
  have hFu : F u = v := by
    simp only [hF]; rw [dif_neg huS]
  have hFinj : Function.Injective F := by
    intro a b hab
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · rw [hFS a ha, hFS b hb] at hab
        have h3 : (⟨a, ha⟩ : ↥S) = ⟨b, hb⟩ := hginj hab
        exact congrArg Subtype.val h3
      · exfalso
        rw [hFS a ha] at hab
        have h2 : F b = v := by simp only [hF]; rw [dif_neg hb]
        rw [h2] at hab
        exact hgv ⟨a, ha⟩ hab
    · by_cases hb : b ∈ S
      · exfalso
        rw [hFS b hb] at hab
        have h2 : F a = v := by simp only [hF]; rw [dif_neg ha]
        rw [h2] at hab
        exact hgv ⟨b, hb⟩ hab.symm
      · have h1 : a = u := by
          by_contra hne; exact ha (hmemS a hne)
        have h2 : b = u := by
          by_contra hne; exact hb (hmemS b hne)
        rw [h1, h2]
  have hFbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hFinj, rfl⟩
  refine ⟨Equiv.ofBijective F hFbij, ?_, ?_⟩
  · intro x
    rw [Equiv.ofBijective_apply]
    by_cases hx : x ∈ S
    · rw [hFS x hx]; exact hgR ⟨x, hx⟩
    · have hxu : x = u := by
        by_contra hne; exact hx (hmemS x hne)
      rw [hxu, hFu]; exact huv
  · rw [Equiv.ofBijective_apply]; exact hFu
