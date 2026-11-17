import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.TreeZeroForcingFixedColorNotUltraLogConcave

/-!
# tree_fixed_color_ulc_strict_failure

Topic: graphs   Node: 4a38ec66d8bc

Provenance: helper lemma.

A fixed-color restriction of a 14-vertex tree fails the binomial-normalized log-concavity inequality at rank two.
-/

theorem tree_fixed_color_ulc_strict_failure : ∃ (T : SimpleGraph (Fin 14)) (A : Finset (Fin 14)) (f : Fin 5 → Fin 14), T.IsTree ∧ Function.Injective f ∧ Disjoint A (Finset.univ.image f) ∧ (let c := fun k : ℕ => {S : Finset (Fin 5) | S.card = k ∧ is_zero_forcing_set T ((Finset.univ \ (A ∪ S.image f) : Finset (Fin 14)) : Set (Fin 14))}.ncard; c 2 ^ 2 * Nat.choose 5 1 * Nat.choose 5 3 < c 1 * c 3 * Nat.choose 5 2 ^ 2) := by
  obtain ⟨T, A, f, hT, hf, hd, hc⟩ := tree_zero_forcing_fixed_color_not_ultra_log_concave
  refine ⟨T, A, f, hT, hf, hd, ?_⟩
  rcases hc with ⟨h1, h2, h3⟩
  dsimp only at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  norm_num [Nat.choose]
