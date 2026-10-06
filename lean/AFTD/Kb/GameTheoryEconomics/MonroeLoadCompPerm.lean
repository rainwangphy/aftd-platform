import AFTD.Prelude

/-!
# monroe_load_comp_perm

Topic: social_choice   Node: 3f66ef62458b

Provenance: helper lemma. step towards hare_monroe_satisfies_droop_jr (Monroe and Droop-JR, open case of Justified Representation: From Hare to Droop, arXiv:2508.00811)

Precomposing an assignment with a permutation of the voters does not change how many voters each candidate receives.
-/

/-- Precomposing an assignment with a permutation of the voters does not change how many voters each candidate receives. -/
theorem monroe_load_comp_perm {n : ℕ} {β : Type*} [DecidableEq β] (π : Fin n → β)
    (σ : Equiv.Perm (Fin n)) (x : β) :
    (Finset.univ.filter fun v => π (σ v) = x).card = (Finset.univ.filter fun v => π v = x).card := by
  refine Finset.card_bij' (fun v _ => σ v) (fun v _ => σ.symm v) ?_ ?_ ?_ ?_ <;> simp
