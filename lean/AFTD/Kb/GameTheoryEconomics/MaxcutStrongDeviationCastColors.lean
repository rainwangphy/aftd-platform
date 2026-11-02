import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_strong_deviation_cast_colors

Topic: equilibria   Node: 6f4ca10df6c4

Provenance: helper lemma. Lifting the 46-vertex unweighted deviation cycle from three colors to all k ≥ 3.

Injectively embedding the available colors into a larger color set preserves a given strong deviation and its coalition.
-/

theorem maxcut_strong_deviation_cast_colors
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k l : ℕ} (hkl : k ≤ l) (σ τ : V → Fin k) (S : Finset V)
    (h : is_maxcut_strong_deviation G σ S τ) :
    is_maxcut_strong_deviation G (fun v => Fin.castLE hkl (σ v)) S
      (fun v => Fin.castLE hkl (τ v)) := by
  have hu (ρ : V → Fin k) (v : V) :
      maxcut_utility G (fun u => Fin.castLE hkl (ρ u)) v = maxcut_utility G ρ v := by
    unfold maxcut_utility
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.castLE_inj]
  rcases h with ⟨hne, h_out, h_in⟩
  exact ⟨hne, fun v hv => congr_arg (Fin.castLE hkl) (h_out v hv), fun v hv => by
    rw [hu σ v, hu τ v]
    exact h_in v hv⟩
