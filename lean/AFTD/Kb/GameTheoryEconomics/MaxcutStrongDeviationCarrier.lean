import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_strong_deviation_carrier

Topic: equilibria   Node: dab88ee28d70

Provenance: helper lemma. step towards maxcut_game_strong_equilibrium_exists

Every strong deviation contains a carrier deviation: the subset of players who actually change color forms a valid strong deviation.
-/

/-- Every strong deviation contains a carrier deviation: the subset of players who actually change color forms a valid strong deviation. -/
theorem maxcut_strong_deviation_carrier {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ τ : V → Fin k) (S : Finset V)
    (hdev : is_maxcut_strong_deviation G σ S τ) :
    is_maxcut_strong_deviation G σ (Finset.univ.filter fun v => τ v ≠ σ v) τ := by
  classical
  obtain ⟨hne, hout, hgain⟩ := hdev
  have hsub : ∀ v, τ v ≠ σ v → v ∈ S := by
    intro v hv
    by_contra hn
    exact hv (hout v hn)
  have hdiff : ∃ v, τ v ≠ σ v := by
    by_contra h
    have heq : τ = σ := funext fun v => by simpa using not_exists.mp h v
    obtain ⟨v, hv⟩ := hne
    have := hgain v hv
    simpa [heq] using this
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hdiff
    exact ⟨v, by simp [hv]⟩
  · intro v hv
    simpa using hv
  · intro v hv
    exact hgain v (hsub v (Finset.mem_filter.mp hv).2)
