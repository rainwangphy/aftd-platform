import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Forces
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258HasMonoClique

/-!
# op_258_forces_mono_clique

Topic: combinatorics   Node: 62498d7ab2ae

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

If a forces a monochromatic K_k, then a forces a monochromatic K_j for every j ≤ k.
-/

/-- The forcing hierarchy is downward closed in the clique size: a monochromatic `K_k` contains a monochromatic `K_j` for `j ≤ k`. -/
theorem op_258_forces_mono_clique (a : ℕ+ → ℝ) {j k : ℕ} (hjk : j ≤ k) (hk : op_258_forces a k) :
    op_258_forces a j := by
  obtain ⟨n₀, hn⟩ := hk
  refine ⟨n₀, ?_⟩
  intro n hn' c hc
  obtain ⟨s, i, hcard, hmono⟩ := hn n hn' c hc
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (by omega : j ≤ s.card)
  refine ⟨t, i, htcard, ?_⟩
  intro u v hu hv huv
  have hu' : u ∈ s := hts hu
  have hv' : v ∈ s := hts hv
  have := hmono hu' hv' huv
  convert this
