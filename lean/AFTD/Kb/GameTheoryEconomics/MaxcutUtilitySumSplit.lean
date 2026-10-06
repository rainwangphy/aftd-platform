import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityEqSum
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_utility_sum_split

Topic: equilibria   Node: 487c65467529

Provenance: helper lemma. step towards maxcut_optimal_strong_of_degree_le (arXiv:2610.04948, Corollary 9)

For any set S, the total utility of the members of S is A + B, with A the bichromatic adjacent ordered pairs inside S and B those from S to its complement.
-/

theorem maxcut_utility_sum_split {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) (S : Finset V) :
    ∑ v ∈ S, maxcut_utility G ρ v =
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) +
      ∑ v ∈ S, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) := by
  simp only [maxcut_utility_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => (Finset.sum_add_sum_compl S _).symm
