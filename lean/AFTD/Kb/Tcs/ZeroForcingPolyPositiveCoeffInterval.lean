import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.ZeroForcingPolyCoeff
import AFTD.Kb.Tcs.IsZeroForcingSetMono
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# zero_forcing_poly_positive_coeff_interval

Topic: graphs   Node: fbb07b21d332

Provenance: helper lemma. Helper for tree_zero_forcing_poly_unimodal, via log-concavity of its coefficient sequence.

For any finite graph the positive coefficients of its zero forcing polynomial form an interval.
-/

theorem zero_forcing_poly_positive_coeff_interval {V : Type*} [Fintype V] (G : SimpleGraph V) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (hi : 0 < (zero_forcing_poly G).coeff i) (hk : 0 < (zero_forcing_poly G).coeff k) : 0 < (zero_forcing_poly G).coeff j := by
  classical
  rw [zero_forcing_poly_coeff] at hi hk ⊢
  have h_fin (m : ℕ) : ({S : Finset V | is_zero_forcing_set G (S : Set V) ∧ S.card = m} : Set (Finset V)).Finite :=
    Set.toFinite _
  rw [Set.ncard_pos (h_fin i)] at hi
  rw [Set.ncard_pos (h_fin k)] at hk
  rw [Set.ncard_pos (h_fin j)]
  obtain ⟨Si, hSi_zf, hSi_card⟩ := hi
  obtain ⟨Sk, -, hSk_card⟩ := hk
  have hjV : j ≤ Fintype.card V := by
    have : Sk.card ≤ Fintype.card V := Finset.card_le_univ Sk
    omega
  have h_compl : j - Si.card ≤ (Siᶜ).card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨u, hu_sub, hu_card⟩ := Finset.exists_subset_card_eq h_compl
  refine ⟨Si ∪ u, is_zero_forcing_set_mono G (by simp) hSi_zf, ?_⟩
  rw [Finset.card_union_of_disjoint (disjoint_compl_right.mono_right hu_sub), hu_card]
  omega
