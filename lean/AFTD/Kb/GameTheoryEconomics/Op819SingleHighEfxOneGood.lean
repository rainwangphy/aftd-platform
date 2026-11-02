import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineSingleHighAlphaEfx
import AFTD.Kb.GameTheoryEconomics.IsAlphaEfxGoods
import AFTD.Kb.GameTheoryEconomics.IsSingleHighProfile
import AFTD.Kb.GameTheoryEconomics.IsSingleHighValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsOnlineAllocator

/-!
# op819_single_high_efx_one_good

Topic: fair_division   Node: 3eafe2b691d6

Provenance: helper lemma. arXiv:2610.34625

For any number of agents $n \ge 1$, $m = 1$ good, and parameter $R \ge 0$, there exists a deterministic online algorithm that achieves a $1$-EFX allocation for all single-high valuation profiles with parameter $R$.
-/

/-- For a single good, 1-EFX is trivially achievable online for any number of agents and any ratio R >= 0. -/
theorem op819_single_high_efx_one_good (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    has_online_single_high_alpha_efx (n + 1) 1 R 1 := by
  use fun _ _ => 0
  constructor
  · intros v v' t ht
    rfl
  · intros v hv i j hij g hg
    have herase : (bundle_of (fun _ => (0 : Fin (n + 1))) j).erase g = ∅ := by
      ext x
      simp only [Finset.mem_erase, Finset.notMem_empty, iff_false]
      intro ⟨hne, _⟩
      exact hne (Subsingleton.elim x g)
    rw [herase]
    dsimp [additive_valuation]
    rw [mul_zero]
    apply Finset.sum_nonneg
    intro x _
    rcases hv i with ⟨g0, hg0, hrest⟩
    by_cases hx : x = g0
    · rw [hx, hg0]; exact hR
    · rw [hrest x hx]; linarith
