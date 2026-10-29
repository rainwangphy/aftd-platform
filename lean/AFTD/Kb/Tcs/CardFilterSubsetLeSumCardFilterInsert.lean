import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# card_filter_subset_le_sum_card_filter_insert

Topic: combinatorics   Node: 046e891d2b45

Provenance: helper lemma. arXiv:2610.37315 Claim 1.2

Let α be a type with decidable equality. Let ℱ be a finite family of finite subsets of α such that for all F1, F2 ∈ ℱ, the intersection F1 ∩ F2 is nonempty. For any finite subset A of α and any F ∈ ℱ, the number of sets in ℱ containing A is at most the sum over all x ∈ F of the number of sets in ℱ containing insert x A.
-/

/-- In an intersecting family, the number of edges containing A is bounded by the sum over x ∈ F of the number of edges containing A ∪ {x}. -/
lemma card_filter_subset_le_sum_card_filter_insert {α : Type*} [DecidableEq α]
    (ℱ : Finset (Finset α)) (A F : Finset α)
    (hinter : ∀ F1 ∈ ℱ, ∀ F2 ∈ ℱ, (F1 ∩ F2).Nonempty)
    (hF : F ∈ ℱ) :
    (ℱ.filter (fun F' => A ⊆ F')).card ≤
      ∑ x ∈ F, (ℱ.filter (fun F' => insert x A ⊆ F')).card := by
  set S := ℱ.filter (fun F' => A ⊆ F')
  have h1 : S.card = ∑ F' ∈ S, 1 := Finset.card_eq_sum_ones S
  have h2 : ∀ F' ∈ S, 1 ≤ (F ∩ F').card := by
    intro F' hF'
    have hF'ℱ : F' ∈ ℱ := (Finset.mem_filter.mp hF').1
    have hnonempty : (F ∩ F').Nonempty := hinter F hF F' hF'ℱ
    exact Finset.Nonempty.card_pos hnonempty
  have h3 : S.card ≤ ∑ F' ∈ S, (F ∩ F').card := by
    rw [h1]
    exact Finset.sum_le_sum h2
  have h4 : ∑ F' ∈ S, (F ∩ F').card = ∑ x ∈ F, (S.filter (fun b => x ∈ b)).card := by
    have h := (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun a b => a ∈ b) (s := F) (t := S)).symm
    have h_below : ∀ b ∈ S, (Finset.bipartiteBelow (fun a b => a ∈ b) F b).card = (F ∩ b).card := by
      intro b _
      apply congr_arg Finset.card
      ext a
      simp [Finset.bipartiteBelow]
    have h_above : ∀ a ∈ F, (Finset.bipartiteAbove (fun a b => a ∈ b) S a).card = (S.filter (fun b => a ∈ b)).card := by
      intro a _
      apply congr_arg Finset.card
      ext b
      simp [Finset.bipartiteAbove]
    rw [Finset.sum_congr rfl h_below, Finset.sum_congr rfl h_above] at h
    exact h
  have h5 : ∀ x ∈ F, (S.filter (fun b => x ∈ b)).card = (ℱ.filter (fun F' => insert x A ⊆ F')).card := by
    intro x _
    apply congr_arg Finset.card
    ext b
    simp only [S, Finset.mem_filter, Finset.insert_subset_iff]
    tauto
  have h6 : ∑ x ∈ F, (S.filter (fun b => x ∈ b)).card = ∑ x ∈ F, (ℱ.filter (fun F' => insert x A ⊆ F')).card :=
    Finset.sum_congr rfl h5
  linarith
