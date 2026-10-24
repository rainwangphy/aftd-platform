import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerFifteenTightClassAncestors

/-!
# cycle_power_fifteen_tight_class_spanning

Topic: combinatorics   Node: e73194559697

Provenance: helper lemma. Counting step for the k = 15 case of OP-205, arXiv:2610.15635. Experiment 3978 identifies the weights; the proof assigns one weighted edge to each vertex in a rooted forest.

Every nonempty subset attaining equality in the sixteen-position weighted-pair bound contains both positions 0 and 15.
-/

theorem cycle_power_fifteen_tight_class_spanning(b : Fin 16 → Bool)
    (hw :
    2 * (b 0 && b 15).toNat +
      (∑ i : Fin 2, (b ⟨i.val, by omega⟩ && b ⟨i.val + 14, by omega⟩).toNat) +
      (∑ i : Fin 4, (b ⟨i.val, by omega⟩ && b ⟨i.val + 12, by omega⟩).toNat) +
      (∑ i : Fin 8, (b ⟨i.val, by omega⟩ && b ⟨i.val + 8, by omega⟩).toNat) =
      ∑ i : Fin 16, (b i).toNat) (i : Fin 16) (hi : b i = true) :
    b 0 = true ∧ b 15 = true := by
  obtain ⟨hroot, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := cycle_power_fifteen_tight_class_ancestors b hw
  have htop : b 0 = true := by
    fin_cases i
    · exact hi
    · exact hroot.symm ▸ (h1 (hi))
    · exact h14 (h2 (hi))
    · exact hroot.symm ▸ (h3 (hi))
    · exact h12 (h4 (hi))
    · exact hroot.symm ▸ (h1 (h13 (h5 (hi))))
    · exact h14 (h6 (hi))
    · exact hroot.symm ▸ (h7 (hi))
    · exact h8 (hi)
    · exact hroot.symm ▸ (h1 (h9 (hi)))
    · exact h14 (h2 (h10 (hi)))
    · exact hroot.symm ▸ (h3 (h11 (hi)))
    · exact h12 (hi)
    · exact hroot.symm ▸ (h1 (h13 (hi)))
    · exact h14 (hi)
    · exact hroot.symm ▸ (hi)
  exact ⟨htop, hroot ▸ htop⟩
