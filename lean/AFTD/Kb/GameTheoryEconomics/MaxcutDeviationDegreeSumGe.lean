import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDeviationMonoInsideDrop
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal

/-!
# maxcut_deviation_degree_sum_ge

Topic: equilibria   Node: b2c3aa6be8de

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

Let σ be an optimal colouring of the unweighted Max-k-Cut game on a finite simple graph G and let (S,τ) be a strong deviation from σ. Then the members of the coalition have total degree at least 2k|S|, so in particular some player of every deviating coalition has degree at least 2k.
-/

/-- Any coalition that deviates strongly from an optimal k-colouring has total degree at least 2k|S|, i.e. average degree at least 2k. -/
theorem maxcut_deviation_degree_sum_ge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ τ : V → Fin k) (S : Finset V)
    (hopt : is_maxcut_optimal G σ) (hdev : is_maxcut_strong_deviation G σ S τ) :
    2 * k * S.card ≤ ∑ v ∈ S, G.degree v := by
  have hmono : ∀ v, k * (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ G.degree v := by
    intro v
    have hsum : (Finset.univ.filter fun w => G.Adj v w).card =
        ∑ c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := Finset.univ)
        (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
      simp only [Finset.filter_filter]
    have hdv : (Finset.univ.filter fun w => G.Adj v w).card = G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    have hlow : ∑ _c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤
        ∑ c : Fin k, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c).card :=
      Finset.sum_le_sum fun c _ => maxcut_optimal_same_color_le G σ hopt v c
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlow
    omega
  have hdrop := maxcut_deviation_mono_inside_drop G σ τ S hopt hdev
  have hdrop' : 2 * S.card ≤ ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) := by
    omega
  have hS_le : ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) ≤
      ∑ v ∈ S, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card := by
    refine Finset.sum_le_sum fun v _ => ?_
    calc ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)
        ≤ ∑ w ∈ Finset.univ, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card :=
          (Finset.card_filter _ _).symm
  calc 2 * k * S.card
      = k * (2 * S.card) := by ring
    _ ≤ k * (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)) :=
        Nat.mul_le_mul_left k hdrop'
    _ ≤ k * ∑ v ∈ S, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card :=
        Nat.mul_le_mul_left k hS_le
    _ = ∑ v ∈ S, k * (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card := by
        rw [Finset.mul_sum]
    _ ≤ ∑ v ∈ S, G.degree v :=
        Finset.sum_le_sum fun v _ => hmono v
