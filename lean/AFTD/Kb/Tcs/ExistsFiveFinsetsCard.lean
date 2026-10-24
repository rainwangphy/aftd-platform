import AFTD.Prelude

/-!
# exists_five_finsets_card

Topic: combinatorics   Node: 768ab28e5de3

Provenance: helper lemma. step towards five_diamond_ramsey_property_step

If the binomial coefficient C(m,r) is at least 5, there are five pairwise distinct r-element subsets of Fin m.
-/

/-- Five distinct r-subsets of Fin m exist as soon as C(m,r) ≥ 5. -/
theorem exists_five_finsets_card {m r : ℕ} (h5 : 5 ≤ Nat.choose m r) :
    ∃ S : Fin 5 → Finset (Fin m), (∀ k, (S k).card = r) ∧ ∀ k k', k ≠ k' → S k ≠ S k' := by
  have hcard : ((Finset.univ : Finset (Fin m)).powersetCard r).card = Nat.choose m r := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hle : 5 ≤ ((Finset.univ : Finset (Fin m)).powersetCard r).card := by
    rwa [hcard]
  obtain ⟨G, hG_sub, hGc⟩ := Finset.exists_subset_card_eq hle
  let e : Fin 5 ≃ ↥G := (Fin.castOrderIso hGc.symm).toEquiv.trans G.equivFin.symm
  let S : Fin 5 → Finset (Fin m) := fun k => (e k).1
  use S
  constructor
  · intro k
    have hk : (e k).1 ∈ (Finset.univ : Finset (Fin m)).powersetCard r := hG_sub (e k).2
    rw [Finset.mem_powersetCard] at hk
    exact hk.2
  · intro k k' hne heq
    apply hne
    have : e k = e k' := Subtype.ext heq
    exact e.injective this
