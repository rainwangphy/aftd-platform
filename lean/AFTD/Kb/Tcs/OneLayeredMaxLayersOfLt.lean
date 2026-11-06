import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredMaxLayers
import AFTD.Kb.Tcs.OneLayeredFamily

/-!
# one_layered_max_layers_of_lt

Topic: combinatorics   Node: c5ad5b2b10c6

Provenance: helper lemma. arXiv:2611.08071 Section 2

If m < r, then F(m, r) = 0, as no 1-layered family of r-subsets can be formed on at most m vertices.
-/

/-- A 1-layered family of `r`-subsets on `Fin n` forces `r ≤ n`, since some layer is nonempty. -/
private theorem one_layered_max_layers_of_lt_aux (n r : ℕ) (F : OneLayeredFamily (Fin n) r) :
    r ≤ n := by
  obtain ⟨A, hA⟩ := F.layers_nonempty ⟨0, F.k_pos⟩
  have hcard : A.card = r := F.layers_card _ A hA
  have hle : A.card ≤ n := by
    simpa using Finset.card_le_univ A
  omega

/-- The maximum number of layers F(m, r) is 0 when m < r. -/
theorem one_layered_max_layers_of_lt (m r : ℕ) (h : m < r) : one_layered_max_layers m r = 0 := by
  unfold one_layered_max_layers
  have hempty : {k : ℕ | ∃ n ≤ m, ∃ F : OneLayeredFamily (Fin n) r, F.k = k} = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨k, n, hn, F, hFk⟩ := hne
    have := one_layered_max_layers_of_lt_aux n r F
    omega
  rw [hempty, csSup_empty]
  rfl
