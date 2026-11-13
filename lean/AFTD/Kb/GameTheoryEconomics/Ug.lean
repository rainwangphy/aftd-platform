import AFTD.Prelude

/-!
# Ug

Topic: general_equilibrium   Node: 18644aa6fbc1

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

Good-ordering event for group g: in the ordering e, player 2g appears immediately before player 2g+1, and every member of every earlier group h < g appears before 2g.
-/

/-- Event that group g is a contiguous block 2g,2g+1 placed after all earlier groups; each such ordering yields a non-core marginal vector. -/
noncomputable def Ug {n : ℕ} (e : Fin (Fintype.card (Fin n)) ≃ Fin n) (g : ℕ) : Prop := ∃ (ha : 2 * g < n) (hb : 2 * g + 1 < n),
    (e.symm ⟨2 * g, ha⟩).val + 1 = (e.symm ⟨2 * g + 1, hb⟩).val ∧
    (∀ i : Fin n, i.val / 2 < g → (e.symm i).val < (e.symm ⟨2 * g, ha⟩).val)
