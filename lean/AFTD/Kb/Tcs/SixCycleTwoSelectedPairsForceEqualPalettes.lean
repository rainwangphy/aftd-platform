import AFTD.Prelude

/-!
# six_cycle_two_selected_pairs_force_equal_palettes

Topic: combinatorics   Node: 94524f51ffb1

Provenance: helper lemma. Palette obstruction reduction for the OP-874 campaign.

If four consecutive factor colors exhaust the palette, two complementary colors at a selected six-cycle pair have the same two-color set as the middle pair.
-/

theorem six_cycle_two_selected_pairs_force_equal_palettes
    {Ω : Type*} [DecidableEq Ω] (a b c d e f : Ω)
    (hcover : ∀ z : Ω, z ∈ ({f,a,b,c} : Finset Ω))
    (hcd : c ≠ d) (hdf : d ≠ f) (hef : e ≠ f) (hce : c ≠ e)
    (hde : d ≠ e) : ({a,b} : Finset Ω) = {d,e} := by
  have hd : d = a ∨ d = b := by
    have h := hcover d
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    aesop
  have he : e = a ∨ e = b := by
    have h := hcover e
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    aesop
  rcases hd with hda | hdb <;> rcases he with hea | heb
  · exact False.elim (hde (hda.trans hea.symm))
  · rw [hda, heb]
  · rw [hdb, hea, Finset.pair_comm]
  · exact False.elim (hde (hdb.trans heb.symm))
