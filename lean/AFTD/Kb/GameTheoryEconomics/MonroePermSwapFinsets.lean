import AFTD.Prelude

/-!
# monroe_perm_swap_finsets

Topic: social_choice   Node: 896cbe52ea01

Provenance: helper lemma. step towards hare_monroe_satisfies_droop_jr (Monroe and Droop-JR, open case of Justified Representation: From Hare to Droop, arXiv:2508.00811)

For disjoint finite sets P, Q of equal size there is a permutation sending P into Q, Q into P, and fixing everything else.
-/

/-- For disjoint finite sets P, Q of equal size there is a permutation sending P into Q, Q into P, and fixing everything else. -/
theorem monroe_perm_swap_finsets {α : Type*} [DecidableEq α] (P Q : Finset α)
    (hd : Disjoint P Q) (hc : P.card = Q.card) :
    ∃ σ : Equiv.Perm α, (∀ v ∈ P, σ v ∈ Q) ∧ (∀ v ∈ Q, σ v ∈ P) ∧
      ∀ v, v ∉ P → v ∉ Q → σ v = v := by
  induction P using Finset.induction_on generalizing Q with
  | empty =>
    have : Q = ∅ := by
      rw [← Finset.card_eq_zero]; simpa using hc.symm
    subst this
    exact ⟨1, by simp, by simp, by simp⟩
  | @insert a P ha ih =>
    have hQ : 0 < Q.card := by rw [← hc, Finset.card_insert_of_notMem ha]; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hQ
    have haQ : a ∉ Q := Finset.disjoint_left.1 hd (Finset.mem_insert_self a P)
    have hbP : b ∉ P := fun h => Finset.disjoint_left.1 hd (Finset.mem_insert_of_mem h) hb
    have hd' : Disjoint P (Q.erase b) :=
      Finset.disjoint_of_subset_right (Finset.erase_subset b Q)
        (Finset.disjoint_of_subset_left (Finset.subset_insert a P) hd)
    have hc' : P.card = (Q.erase b).card := by
      rw [Finset.card_erase_of_mem hb, ← hc, Finset.card_insert_of_notMem ha]; simp
    obtain ⟨σ, h1, h2, h3⟩ := ih (Q.erase b) hd' hc'
    have hab : a ≠ b := fun h => haQ (h ▸ hb)
    have σa : σ a = a := h3 a ha (fun h => haQ (Finset.mem_of_mem_erase h))
    have σb : σ b = b := h3 b hbP (by simp)
    refine ⟨σ.trans (Equiv.swap a b), ?_, ?_, ?_⟩
    · intro v hv
      simp only [Equiv.trans_apply]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [σa, Equiv.swap_apply_left]; exact hb
      · have hσ := h1 v hv
        have h1' : σ v ≠ a := fun h => haQ (h ▸ Finset.mem_of_mem_erase hσ)
        have h2' : σ v ≠ b := Finset.ne_of_mem_erase hσ
        rw [Equiv.swap_apply_of_ne_of_ne h1' h2']
        exact Finset.mem_of_mem_erase hσ
    · intro v hv
      simp only [Equiv.trans_apply]
      by_cases hvb : v = b
      · subst hvb; rw [σb, Equiv.swap_apply_right]; exact Finset.mem_insert_self _ _
      · have hσ := h2 v (Finset.mem_erase.2 ⟨hvb, hv⟩)
        have h1' : σ v ≠ a := fun h => ha (h ▸ hσ)
        have h2' : σ v ≠ b := fun h => hbP (h ▸ hσ)
        rw [Equiv.swap_apply_of_ne_of_ne h1' h2']
        exact Finset.mem_insert_of_mem hσ
    · intro v hvP hvQ
      simp only [Equiv.trans_apply]
      have hva : v ≠ a := fun h => hvP (h ▸ Finset.mem_insert_self a P)
      have hvb : v ≠ b := fun h => hvQ (h ▸ hb)
      rw [h3 v (fun h => hvP (Finset.mem_insert_of_mem h))
        (fun h => hvQ (Finset.mem_of_mem_erase h)), Equiv.swap_apply_of_ne_of_ne hva hvb]
