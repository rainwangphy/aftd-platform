import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityEqSum
import AFTD.Kb.GameTheoryEconomics.MaxcutPairSumComm

/-!
# maxcut_welfare_split

Topic: equilibria   Node: 618063902dae

Provenance: helper lemma. step towards maxcut_optimal_strong_of_degree_le (arXiv:2610.04948, Corollary 9)

For any set S of players, the welfare of a coloring is A + 2B + C, where A counts bichromatic adjacent ordered pairs inside S, B those from S to its complement, and C those inside the complement.
-/

theorem maxcut_welfare_split {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) (S : Finset V) :
    maxcut_welfare G ρ =
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) +
      2 * ∑ v ∈ S, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) +
      ∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) := by
  have hs : ∀ v, ∑ w, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) =
      ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) +
        ∑ w ∈ Sᶜ, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) :=
    fun v => (Finset.sum_add_sum_compl S _).symm
  unfold maxcut_welfare
  simp only [maxcut_utility_eq_sum]
  rw [← Finset.sum_add_sum_compl S]
  simp only [hs, Finset.sum_add_distrib]
  rw [maxcut_pair_sum_comm G ρ Sᶜ S]
  ring
