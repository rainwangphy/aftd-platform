import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_2130_path_interval_crossing_closed

Topic: online_algorithms   Node: 4ebb2822cddb

Provenance: helper lemma. OP-2130: interval specialization of the backward-witness construction of arXiv:2611.00388, Lemma 4.2

If a unit edge has one endpoint in a finite integer interval and one outside, adding the outside endpoint and deleting the inside endpoint each produce another integer interval, possibly empty.
-/

theorem op_2130_path_interval_crossing_closed (l r a b : ℤ) (ha : a ∈ Finset.Icc l r) (hb : b ∉ Finset.Icc l r) (hab : a + 1 = b ∨ b + 1 = a) : (∃ L R : ℤ, insert b (Finset.Icc l r) = Finset.Icc L R) ∧ (∃ L R : ℤ, (Finset.Icc l r).erase a = Finset.Icc L R) := by
  have ha' := Finset.mem_Icc.mp ha
  have hb' : ¬ (l ≤ b ∧ b ≤ r) := by simpa using hb
  have h : (a = l ∧ b = l - 1) ∨ (a = r ∧ b = r + 1) := by rcases hab with hab | hab <;> omega
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor
    · refine ⟨l - 1, r, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    · refine ⟨l + 1, r, ?_⟩
      ext x
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
  · constructor
    · refine ⟨l, r + 1, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    · refine ⟨l, r - 1, ?_⟩
      ext x
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
