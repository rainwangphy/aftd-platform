import AFTD.Prelude
import AFTD.Kb.Tcs.B4Graph
import AFTD.Kb.Tcs.B4GraphAdj

/-!
# b4_cliqueNum

Topic: graphs   Node: 3c693ea6c608

Provenance: formalization of a published result. Source: arXiv:2610.21388, Section 2.2

The clique number of B_4(n_0, n_1, n_2, n_3) is max(max(n_0 + n_1, n_1 + n_3), n_2 + n_3).
-/

open SimpleGraph Finset

def b4_cliqueNum_pairBlock (n : Fin 4 → ℕ) (a b : Fin 4) : Finset (Σ i : Fin 4, Fin (n i)) :=
  ({a, b} : Finset (Fin 4)).sigma (fun _ => univ)

lemma b4_cliqueNum_card_pairBlock (n : Fin 4 → ℕ) (a b : Fin 4) (hab : a ≠ b) :
    (b4_cliqueNum_pairBlock n a b).card = n a + n b := by
  rw [b4_cliqueNum_pairBlock, card_sigma]
  simp [hab]

lemma b4_cliqueNum_mem_pairBlock_iff (n : Fin 4 → ℕ) (a b : Fin 4) (x : Σ i : Fin 4, Fin (n i)) :
    x ∈ b4_cliqueNum_pairBlock n a b ↔ x.1 = a ∨ x.1 = b := by
  simp [b4_cliqueNum_pairBlock]

lemma b4_cliqueNum_isClique_01 (n : Fin 4 → ℕ) :
    (b4_graph n).IsClique (b4_cliqueNum_pairBlock n 0 1 : Set (Σ i : Fin 4, Fin (n i))) := by
  intro x hx y hy hne
  simp only [b4_cliqueNum_pairBlock, mem_coe, mem_sigma, mem_insert, mem_singleton, mem_univ, and_true] at hx hy
  rw [b4_graph_adj]
  refine ⟨hne, ?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [hx, hy]
  · right; left; exact ⟨hx, hy⟩
  · right; right; left; exact ⟨hx, hy⟩
  · left; rw [hx, hy]

lemma b4_cliqueNum_isClique_13 (n : Fin 4 → ℕ) :
    (b4_graph n).IsClique (b4_cliqueNum_pairBlock n 1 3 : Set (Σ i : Fin 4, Fin (n i))) := by
  intro x hx y hy hne
  simp only [b4_cliqueNum_pairBlock, mem_coe, mem_sigma, mem_insert, mem_singleton, mem_univ, and_true] at hx hy
  rw [b4_graph_adj]
  refine ⟨hne, ?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [hx, hy]
  · right; right; right; left; exact ⟨hx, hy⟩
  · right; right; right; right; left; exact ⟨hx, hy⟩
  · left; rw [hx, hy]

lemma b4_cliqueNum_isClique_23 (n : Fin 4 → ℕ) :
    (b4_graph n).IsClique (b4_cliqueNum_pairBlock n 2 3 : Set (Σ i : Fin 4, Fin (n i))) := by
  intro x hx y hy hne
  simp only [b4_cliqueNum_pairBlock, mem_coe, mem_sigma, mem_insert, mem_singleton, mem_univ, and_true] at hx hy
  rw [b4_graph_adj]
  refine ⟨hne, ?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · left; rw [hx, hy]
  · right; right; right; right; right; left; exact ⟨hx, hy⟩
  · right; right; right; right; right; right; exact ⟨hx, hy⟩
  · left; rw [hx, hy]

lemma b4_cliqueNum_case_0 (n : Fin 4 → ℕ) (s : Finset (Σ i : Fin 4, Fin (n i)))
    (hc : (b4_graph n).IsClique (s : Set (Σ i : Fin 4, Fin (n i))))
    (x : Σ i : Fin 4, Fin (n i)) (hx : x ∈ s) (hx0 : x.1 = 0) :
    s ⊆ b4_cliqueNum_pairBlock n 0 1 := by
  intro y hy
  rw [b4_cliqueNum_mem_pairBlock_iff]
  by_cases hy0 : y.1 = 0
  · left; exact hy0
  · right
    have hne : x ≠ y := by
      intro h; subst h; exact hy0 hx0
    have hadj := hc hx hy hne
    rw [b4_graph_adj] at hadj
    rcases hadj.2 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hx0] at h; exact (hy0 h.symm).elim
    · exact h2
    · rw [hx0] at h1; contradiction
    · rw [hx0] at h1; contradiction
    · rw [hx0] at h1; contradiction
    · rw [hx0] at h1; contradiction
    · rw [hx0] at h1; contradiction

lemma b4_cliqueNum_case_1 (n : Fin 4 → ℕ) (s : Finset (Σ i : Fin 4, Fin (n i)))
    (hc : (b4_graph n).IsClique (s : Set (Σ i : Fin 4, Fin (n i))))
    (h_no_0 : ∀ z ∈ s, z.1 ≠ 0)
    (x : Σ i : Fin 4, Fin (n i)) (hx : x ∈ s) (hx1 : x.1 = 1) :
    s ⊆ b4_cliqueNum_pairBlock n 1 3 := by
  intro y hy
  rw [b4_cliqueNum_mem_pairBlock_iff]
  by_cases hy1 : y.1 = 1
  · left; exact hy1
  · right
    have hne : x ≠ y := by
      intro h; subst h; exact hy1 hx1
    have hadj := hc hx hy hne
    rw [b4_graph_adj] at hadj
    have hy0 : y.1 ≠ 0 := h_no_0 y hy
    rcases hadj.2 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hx1] at h; exact (hy1 h.symm).elim
    · rw [hx1] at h1; contradiction
    · rw [h2] at hy0; contradiction
    · exact h2
    · rw [hx1] at h1; contradiction
    · rw [hx1] at h1; contradiction
    · rw [hx1] at h1; contradiction

lemma b4_cliqueNum_case_23 (n : Fin 4 → ℕ) (s : Finset (Σ i : Fin 4, Fin (n i)))
    (h_no_0 : ∀ z ∈ s, z.1 ≠ 0)
    (h_no_1 : ∀ z ∈ s, z.1 ≠ 1) :
    s ⊆ b4_cliqueNum_pairBlock n 2 3 := by
  intro y hy
  rw [b4_cliqueNum_mem_pairBlock_iff]
  have hy0 := h_no_0 y hy
  have hy1 := h_no_1 y hy
  omega

lemma b4_cliqueNum_card_le_of_isClique (n : Fin 4 → ℕ) (s : Finset (Σ i : Fin 4, Fin (n i)))
    (hc : (b4_graph n).IsClique (s : Set (Σ i : Fin 4, Fin (n i)))) :
    s.card ≤ max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) := by
  by_cases h0 : ∃ x ∈ s, (x : Σ i : Fin 4, Fin (n i)).1 = 0
  · rcases h0 with ⟨x, hx, hx0⟩
    have hsub := b4_cliqueNum_case_0 n s hc x hx hx0
    have hle := card_le_card hsub
    rw [b4_cliqueNum_card_pairBlock n 0 1 (by decide)] at hle
    exact le_trans hle (le_max_of_le_left (le_max_left _ _))
  · push Not at h0
    by_cases h1 : ∃ x ∈ s, (x : Σ i : Fin 4, Fin (n i)).1 = 1
    · rcases h1 with ⟨x, hx, hx1⟩
      have hsub := b4_cliqueNum_case_1 n s hc h0 x hx hx1
      have hle := card_le_card hsub
      rw [b4_cliqueNum_card_pairBlock n 1 3 (by decide)] at hle
      exact le_trans hle (le_max_of_le_left (le_max_right _ _))
    · push Not at h1
      have hsub := b4_cliqueNum_case_23 n s h0 h1
      have hle := card_le_card hsub
      rw [b4_cliqueNum_card_pairBlock n 2 3 (by decide)] at hle
      exact le_trans hle (le_max_right _ _)

/-- The clique number of B_4(n_0, n_1, n_2, n_3) is max(max(n_0 + n_1, n_1 + n_3), n_2 + n_3). -/
theorem b4_cliqueNum (n : Fin 4 → ℕ) :
    (b4_graph n).cliqueNum = max (max (n 0 + n 1) (n 1 + n 3)) (n 2 + n 3) := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (b4_graph n).exists_isNClique_cliqueNum
    rw [isNClique_iff] at hs
    rw [← hs.2]
    exact b4_cliqueNum_card_le_of_isClique n s hs.1
  · have h01 : n 0 + n 1 ≤ (b4_graph n).cliqueNum := by
      have := (b4_cliqueNum_isClique_01 n).card_le_cliqueNum
      rwa [b4_cliqueNum_card_pairBlock n 0 1 (by decide)] at this
    have h13 : n 1 + n 3 ≤ (b4_graph n).cliqueNum := by
      have := (b4_cliqueNum_isClique_13 n).card_le_cliqueNum
      rwa [b4_cliqueNum_card_pairBlock n 1 3 (by decide)] at this
    have h23 : n 2 + n 3 ≤ (b4_graph n).cliqueNum := by
      have := (b4_cliqueNum_isClique_23 n).card_le_cliqueNum
      rwa [b4_cliqueNum_card_pairBlock n 2 3 (by decide)] at this
    exact max_le (max_le h01 h13) h23
