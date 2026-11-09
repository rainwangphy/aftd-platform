import AFTD.Prelude
import AFTD.Kb.Tcs.CycleLinkCrossesCutIffTlRect
import AFTD.Kb.Tcs.CardCandidateLinksLeSq

/-!
# online_cycle_augmentation_reduction_to_tl_hitting_set

Topic: online_algorithms   Node: e58095eaabc5

Provenance: formalization of a published result. Source: arXiv:2611.08570 Theorem 1.10

Let n be a natural number, L a finite set of pairs (i, j) of integers satisfying 0 ≤ i < j < n, w a real cost function on pairs, and α a real number. If an online algorithm Alg maintaining subsets of L irrevocably (Alg reqs ⊆ L and Alg reqs ⊆ Alg (reqs ++ [r])) is feasible and α-competitive for hitting arriving TL-rectangles ((p.1 ≤ c.1 - 1 ∧ c.1 ≤ p.2 ∧ p.2 ≤ c.2) ∨ (c.1 ≤ p.1 ∧ p.1 ≤ c.2 ∧ c.2 + 1 ≤ p.2)) for all valid cut sequences (1 ≤ c.1 ≤ c.2 < n), then Alg is also feasible and α-competitive for covering all arriving cuts ((c.1 ≤ p.1 ∧ p.1 ≤ c.2) ↔ ¬(c.1 ≤ p.2 ∧ p.2 ≤ c.2)) in Online Cycle Augmentation.
-/

open Finset BigOperators in
/-- Theorem 1.10: An α-competitive online algorithm for TL-rectangle hitting set yields an α-competitive online algorithm for Online Cycle Augmentation. -/
theorem online_cycle_augmentation_reduction_to_tl_hitting_set (n : ℕ) (L : Finset (ℤ × ℤ))
    (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < (n : ℤ))
    (w : (ℤ × ℤ) → ℝ) (α : ℝ)
    (Alg : List (ℤ × ℤ) → Finset (ℤ × ℤ))
    (h_online : (∀ reqs, Alg reqs ⊆ L) ∧ (∀ reqs r, Alg reqs ⊆ Alg (reqs ++ [r])))
    (h_tl_hit : ∀ reqs, (∀ c ∈ reqs, 1 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2 < (n : ℤ)) →
      ∀ c ∈ reqs, ∃ p ∈ Alg reqs,
        (p.1 ≤ c.1 - 1 ∧ c.1 ≤ p.2 ∧ p.2 ≤ c.2) ∨ (c.1 ≤ p.1 ∧ p.1 ≤ c.2 ∧ c.2 + 1 ≤ p.2))
    (h_tl_comp : ∀ reqs, (∀ c ∈ reqs, 1 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2 < (n : ℤ)) →
      ∀ F ⊆ L, (∀ c ∈ reqs, ∃ p ∈ F,
        (p.1 ≤ c.1 - 1 ∧ c.1 ≤ p.2 ∧ p.2 ≤ c.2) ∨ (c.1 ≤ p.1 ∧ p.1 ≤ c.2 ∧ c.2 + 1 ≤ p.2)) →
        ∑ p ∈ Alg reqs, w p ≤ α * ∑ p ∈ F, w p) :
    ((∀ cuts, (∀ c ∈ cuts, 1 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2 < (n : ℤ)) →
      ∀ c ∈ cuts, ∃ p ∈ Alg cuts,
        ((c.1 ≤ p.1 ∧ p.1 ≤ c.2) ↔ ¬(c.1 ≤ p.2 ∧ p.2 ≤ c.2))) ∧
    ∀ cuts, (∀ c ∈ cuts, 1 ≤ c.1 ∧ c.1 ≤ c.2 ∧ c.2 < (n : ℤ)) →
      ∀ F ⊆ L, (∀ c ∈ cuts, ∃ p ∈ F,
        ((c.1 ≤ p.1 ∧ p.1 ≤ c.2) ↔ ¬(c.1 ≤ p.2 ∧ p.2 ≤ c.2))) →
        ∑ p ∈ Alg cuts, w p ≤ α * ∑ p ∈ F, w p) := by
  constructor
  · intro cuts hcuts c hc
    obtain ⟨p, hp, h_rect⟩ := h_tl_hit cuts hcuts c hc
    have hpL : p ∈ L := h_online.1 cuts hp
    have hp_valid := hL p hpL
    have hc_valid := hcuts c hc
    have h_equiv := cycle_link_crosses_cut_iff_tl_rect p.1 p.2 c.1 c.2 (n : ℤ) hp_valid hc_valid
    refine ⟨p, hp, ?_⟩
    exact h_equiv.mpr h_rect
  · intro cuts hcuts F hFL hF_cross
    have hF_tl : ∀ c ∈ cuts, ∃ p ∈ F,
        (p.1 ≤ c.1 - 1 ∧ c.1 ≤ p.2 ∧ p.2 ≤ c.2) ∨ (c.1 ≤ p.1 ∧ p.1 ≤ c.2 ∧ c.2 + 1 ≤ p.2) := by
      intro c hc
      obtain ⟨p, hp, h_cross⟩ := hF_cross c hc
      have hpL : p ∈ L := hFL hp
      have hp_valid := hL p hpL
      have hc_valid := hcuts c hc
      have h_equiv := cycle_link_crosses_cut_iff_tl_rect p.1 p.2 c.1 c.2 (n : ℤ) hp_valid hc_valid
      refine ⟨p, hp, ?_⟩
      exact h_equiv.mp h_cross
    exact h_tl_comp cuts hcuts F hFL hF_tl
