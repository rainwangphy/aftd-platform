import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.WitnessFamilyRamseyProperty

/-!
# shadow_ramsey_property

Topic: combinatorics   Node: d262a88f8ac5

Provenance: helper lemma. arXiv:2611.15376 Proposition 3.1

For every simple graph G on a type V and natural numbers r, s, t, N, if the set-coloring Ramsey property set_coloring_ramsey_property G (r.choose t) (s.choose t) 1 N holds, then set_coloring_ramsey_property G r s t N holds.
-/

open scoped Classical in
/-- Shadow inequality for set-coloring Ramsey property. -/
theorem shadow_ramsey_property
    {V : Type*} (G : SimpleGraph V)
    (r s t N : ℕ)
    (h_prop : set_coloring_ramsey_property G (r.choose t) (s.choose t) 1 N) :
    set_coloring_ramsey_property G r s t N := by
  let W : Finset (Finset (Fin r)) := (Finset.univ : Finset (Fin r)).powersetCard t
  have hW_card : ∀ w ∈ W, w.card = t := by
    intro w hw
    rw [Finset.mem_powersetCard] at hw
    exact hw.2
  have hW_cov : ∀ (S : Finset (Fin r)), S.card = s → s.choose t ≤ (W.filter (· ⊆ S)).card := by
    intro S hS
    have h_eq : W.filter (· ⊆ S) = S.powersetCard t := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, W]
      tauto
    rw [h_eq, Finset.card_powersetCard, hS]
  have hW_card_eq : W.card = r.choose t := by
    dsimp [W]
    rw [Finset.card_powersetCard, Finset.card_fin]
  have h_prop' : set_coloring_ramsey_property G W.card (s.choose t) 1 N := by
    rw [hW_card_eq]
    exact h_prop
  exact witness_family_ramsey_property G r s t (s.choose t) N W hW_card hW_cov h_prop'
