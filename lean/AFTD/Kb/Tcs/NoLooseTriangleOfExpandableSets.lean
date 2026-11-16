import AFTD.Prelude
import AFTD.Kb.Tcs.IsExpandable
import AFTD.Kb.Tcs.IsLooseTriangle
import AFTD.Kb.Tcs.CardLeOfIsExpandable

/-!
# no_loose_triangle_of_expandable_sets

Topic: combinatorics   Node: 0c9409116702

Provenance: formalization of a published result. Source: arXiv:2611.16957 Lemma 3.3 -- Ramsey numbers of loose triangles versus cliques

Let H be a hypergraph (a finite collection of finite subsets of V) and let r be a natural number. If H contains no loose triangle (for all edges e₁, e₂, e₃ in H, they do not form a loose triangle), then no three sets X₁, X₂, X₃ that are expandable in H with parameter r form a loose triangle.
-/

private lemma no_loose_triangle_of_expandable_sets_inter {V : Type*} [DecidableEq V]
    {A B S T : Finset V} (hA : A ⊆ S) (hdisj : Disjoint S (T \ A)) (hBT : B ⊆ T) :
    S ∩ B = A ∩ B := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hxS, hxB⟩
    by_cases hxA : x ∈ A
    · exact ⟨hxA, hxB⟩
    · exfalso
      exact (Finset.disjoint_left.mp hdisj) hxS (Finset.mem_sdiff.mpr ⟨hBT hxB, hxA⟩)
  · rintro ⟨hxA, hxB⟩
    exact ⟨hA hxA, hxB⟩

/-- No three expandable sets form a loose triangle in a loose-triangle-free hypergraph. -/
theorem no_loose_triangle_of_expandable_sets {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (r : ℕ) (h_no_lt : ∀ e₁ ∈ H, ∀ e₂ ∈ H, ∀ e₃ ∈ H, ¬ is_loose_triangle e₁ e₂ e₃) (X₁ X₂ X₃ : Finset V) (hX₁ : IsExpandable H r X₁) (hX₂ : IsExpandable H r X₂) (hX₃ : IsExpandable H r X₃) : ¬ is_loose_triangle X₁ X₂ X₃ := by
  intro hlt
  rw [is_loose_triangle] at hlt
  obtain ⟨_, _, _, hc12, hc23, hc13, hdisjX⟩ := hlt
  have hX₂card : X₂.card ≤ r := card_le_of_is_expandable hX₂
  have hX₃card : X₃.card ≤ r := card_le_of_is_expandable hX₃
  obtain ⟨_, hbnd₁, hexp₁⟩ := hX₁
  obtain ⟨_, hbnd₂, hexp₂⟩ := hX₂
  obtain ⟨_, hbnd₃, hexp₃⟩ := hX₃
  have hY₁card : ((X₂ ∪ X₃) \ X₁).card ≤ 2 * r := by
    have h1 := Finset.card_le_card (Finset.sdiff_subset : (X₂ ∪ X₃) \ X₁ ⊆ X₂ ∪ X₃)
    have h2 := Finset.card_union_le X₂ X₃
    omega
  obtain ⟨e₁, he₁H, hX₁sube₁, hdisj₁⟩ :=
    hexp₁ ((X₂ ∪ X₃) \ X₁) Finset.disjoint_sdiff.symm hY₁card
  have he₁card : e₁.card ≤ r := hbnd₁ e₁ he₁H
  have hY₂card : ((e₁ ∪ X₃) \ X₂).card ≤ 2 * r := by
    have h1 := Finset.card_le_card (Finset.sdiff_subset : (e₁ ∪ X₃) \ X₂ ⊆ e₁ ∪ X₃)
    have h2 := Finset.card_union_le e₁ X₃
    omega
  obtain ⟨e₂, he₂H, hX₂sube₂, hdisj₂⟩ :=
    hexp₂ ((e₁ ∪ X₃) \ X₂) Finset.disjoint_sdiff.symm hY₂card
  have he₂card : e₂.card ≤ r := hbnd₂ e₂ he₂H
  have hY₃card : ((e₁ ∪ e₂) \ X₃).card ≤ 2 * r := by
    have h1 := Finset.card_le_card (Finset.sdiff_subset : (e₁ ∪ e₂) \ X₃ ⊆ e₁ ∪ e₂)
    have h2 := Finset.card_union_le e₁ e₂
    omega
  obtain ⟨e₃, he₃H, hX₃sube₃, hdisj₃⟩ :=
    hexp₃ ((e₁ ∪ e₂) \ X₃) Finset.disjoint_sdiff.symm hY₃card
  have hA1 : e₁ ∩ X₂ = X₁ ∩ X₂ :=
    no_loose_triangle_of_expandable_sets_inter hX₁sube₁ hdisj₁ Finset.subset_union_left
  have hA2 : e₁ ∩ X₃ = X₁ ∩ X₃ :=
    no_loose_triangle_of_expandable_sets_inter hX₁sube₁ hdisj₁ Finset.subset_union_right
  have hB1 : e₂ ∩ e₁ = X₂ ∩ e₁ :=
    no_loose_triangle_of_expandable_sets_inter hX₂sube₂ hdisj₂ Finset.subset_union_left
  have hB2 : e₂ ∩ X₃ = X₂ ∩ X₃ :=
    no_loose_triangle_of_expandable_sets_inter hX₂sube₂ hdisj₂ Finset.subset_union_right
  have hC1 : e₃ ∩ e₁ = X₃ ∩ e₁ :=
    no_loose_triangle_of_expandable_sets_inter hX₃sube₃ hdisj₃ Finset.subset_union_left
  have hC2 : e₃ ∩ e₂ = X₃ ∩ e₂ :=
    no_loose_triangle_of_expandable_sets_inter hX₃sube₃ hdisj₃ Finset.subset_union_right
  have h12eq : e₁ ∩ e₂ = X₁ ∩ X₂ := by
    rw [Finset.inter_comm e₁ e₂, hB1, Finset.inter_comm X₂ e₁, hA1]
  have h23eq : e₂ ∩ e₃ = X₂ ∩ X₃ := by
    rw [Finset.inter_comm e₂ e₃, hC2, Finset.inter_comm X₃ e₂, hB2]
  have h13eq : e₁ ∩ e₃ = X₁ ∩ X₃ := by
    rw [Finset.inter_comm e₁ e₃, hC1, Finset.inter_comm X₃ e₁, hA2]
  have hcard12 : (e₁ ∩ e₂).card = 1 := by rw [h12eq]; exact hc12
  have hcard23 : (e₂ ∩ e₃).card = 1 := by rw [h23eq]; exact hc23
  have hcard13 : (e₃ ∩ e₁).card = 1 := by
    rw [hC1, Finset.inter_comm X₃ e₁, hA2, Finset.inter_comm X₁ X₃]; exact hc13
  have hsubY₃ : X₁ ∩ X₂ ⊆ (e₁ ∪ e₂) \ X₃ := by
    intro x hx
    have hx1 : x ∈ X₁ := (Finset.mem_inter.mp hx).1
    have hxnotX3 : x ∉ X₃ := (Finset.disjoint_left.mp hdisjX) hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (hX₁sube₁ hx1), hxnotX3⟩
  have hdisj_e : Disjoint (e₁ ∩ e₂) e₃ := by
    rw [h12eq]
    exact Finset.disjoint_of_subset_left hsubY₃ hdisj₃.symm
  have hne12 : e₁ ≠ e₂ := by
    intro heq
    have he1 : e₁ = X₁ ∩ X₂ := by rw [← h12eq, heq, Finset.inter_self]
    have hX₁subX₂ : X₁ ⊆ X₂ := by
      intro x hx
      have : x ∈ X₁ ∩ X₂ := he1 ▸ (hX₁sube₁ hx)
      exact (Finset.mem_inter.mp this).2
    have hinter : X₁ ∩ X₂ = X₁ := Finset.inter_eq_left.mpr hX₁subX₂
    rw [hinter] at hdisjX
    have hne : (X₃ ∩ X₁).Nonempty := Finset.card_pos.mp (by rw [hc13]; norm_num)
    obtain ⟨x, hx⟩ := hne
    have hx' := Finset.mem_inter.mp hx
    exact (Finset.disjoint_left.mp hdisjX) hx'.2 hx'.1
  have hne23 : e₂ ≠ e₃ := by
    intro heq
    have he2 : e₂ = X₂ ∩ X₃ := by rw [← h23eq, ← heq, Finset.inter_self]
    have hX₂subX₃ : X₂ ⊆ X₃ := by
      intro x hx
      have : x ∈ X₂ ∩ X₃ := he2 ▸ (hX₂sube₂ hx)
      exact (Finset.mem_inter.mp this).2
    have hsub : X₁ ∩ X₂ ⊆ X₃ := fun x hx => hX₂subX₃ (Finset.mem_inter.mp hx).2
    have hemp : X₁ ∩ X₂ = ∅ := by
      have hz : X₁ ∩ X₂ ⊆ ∅ := by
        intro x hx
        exact absurd (hsub hx) ((Finset.disjoint_left.mp hdisjX) hx)
      exact Finset.subset_empty.mp hz
    rw [hemp] at hc12
    simp at hc12
  have hne13 : e₁ ≠ e₃ := by
    intro heq
    have he1 : e₁ = X₁ ∩ X₃ := by rw [← h13eq, ← heq, Finset.inter_self]
    have hX₁subX₃ : X₁ ⊆ X₃ := by
      intro x hx
      have : x ∈ X₁ ∩ X₃ := he1 ▸ (hX₁sube₁ hx)
      exact (Finset.mem_inter.mp this).2
    have hsub : X₁ ∩ X₂ ⊆ X₃ := fun x hx => hX₁subX₃ (Finset.mem_inter.mp hx).1
    have hemp : X₁ ∩ X₂ = ∅ := by
      have hz : X₁ ∩ X₂ ⊆ ∅ := by
        intro x hx
        exact absurd (hsub hx) ((Finset.disjoint_left.mp hdisjX) hx)
      exact Finset.subset_empty.mp hz
    rw [hemp] at hc12
    simp at hc12
  exact h_no_lt e₁ he₁H e₂ he₂H e₃ he₃H (by
    rw [is_loose_triangle]
    exact ⟨hne12, hne23, hne13, hcard12, hcard23, hcard13, hdisj_e⟩)
