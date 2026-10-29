import AFTD.Prelude
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# srg_is_amply_regular

Topic: graphs   Node: 8f323d334615

Provenance: helper lemma. folklore; Brouwer, Cohen, Neumaier, Distance-Regular Graphs (1989)

Every strongly regular graph with parameters (n, k, ℓ, μ) on a finite vertex set is an amply regular graph with parameters (k, ℓ, μ).
-/

/-- Every strongly regular graph with parameters (n, k, ℓ, μ) is an amply regular graph with parameters (k, ℓ, μ). -/
theorem srg_is_amply_regular {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k ℓ μ : ℕ} (hG : G.IsSRGWith n k ℓ μ) :
    IsAmplyRegular G k ℓ μ := by
  refine ⟨hG.regular, fun {u v} hadj => hG.of_adj u v hadj, fun {u v} hdist => ?_⟩
  have hne : u ≠ v := by
    intro rfl
    simp at hdist
  have hnadj : ¬ G.Adj u v := by
    intro hadj
    rw [← SimpleGraph.dist_eq_one_iff_adj] at hadj
    omega
  exact hG.of_not_adj hne hnadj
