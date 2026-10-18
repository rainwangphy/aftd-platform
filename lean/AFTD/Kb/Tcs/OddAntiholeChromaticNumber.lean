import AFTD.Prelude
import AFTD.Kb.Tcs.OddAntiholeNotColorableOfIdenticalLists

/-!
# odd_antihole_chromaticNumber

Topic: graphs   Node: 6b4ed58e856c

Provenance: helper lemma. arXiv:2610.14241 (Restricting odd antiholes in critical graphs via list coloring), Sec. 2 (the ℓ-chromatic odd antihole); the first conjunct of strong ℓ-chromatic-choosability in OP-216

For ℓ ≥ 3 the odd antihole complement(C_{2ℓ-1}) has chromatic number ℓ.
-/

theorem odd_antihole_chromaticNumber_aux_adj {N : ℕ} (hN : 3 ≤ N) (u v : Fin N) (h : u.val + 1 = v.val) :
    (SimpleGraph.cycleGraph N).Adj u v := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj]
  right
  rw [Fin.sub_def]
  ext
  simp only [Fin.val_mk, Fin.val_one]
  have hv := v.isLt
  rw [show M + 2 - u.val + v.val = (M + 2) + 1 by omega]
  rw [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem odd_antihole_chromaticNumber (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    (SimpleGraph.cycleGraph (2 * ℓ - 1))ᶜ.chromaticNumber = ℓ := by
  have hcol : (SimpleGraph.cycleGraph (2 * ℓ - 1))ᶜ.Colorable ℓ := by
    refine ⟨SimpleGraph.Coloring.mk (fun u => (⟨u.val / 2, by have := u.isLt; omega⟩ : Fin ℓ)) ?_⟩
    intro u v huv heq
    rw [SimpleGraph.compl_adj] at huv
    obtain ⟨hne, hnadj⟩ := huv
    have h2 : u.val / 2 = v.val / 2 := by simpa using congrArg Fin.val heq
    have hne' : u.val ≠ v.val := fun h => hne (Fin.ext h)
    rcases (show u.val + 1 = v.val ∨ v.val + 1 = u.val by omega) with h | h
    · exact hnadj (odd_antihole_chromaticNumber_aux_adj (by omega) u v h)
    · exact hnadj (odd_antihole_chromaticNumber_aux_adj (by omega) v u h).symm
  have hnot : ¬ (SimpleGraph.cycleGraph (2 * ℓ - 1))ᶜ.Colorable (ℓ - 1) := by
    rintro ⟨f⟩
    apply odd_antihole_not_colorable_of_identical_lists ℓ hℓ (Finset.range (ℓ - 1)) (by simp)
    refine ⟨fun v => (f v).val, fun v => by simp, ?_⟩
    intro u v huv h
    exact f.valid huv (Fin.ext h)
  have := (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable (n := ℓ - 1)).mpr
    ⟨by rw [Nat.sub_add_cancel (by omega)]; exact hcol, hnot⟩
  rw [this]
  norm_cast
  omega
