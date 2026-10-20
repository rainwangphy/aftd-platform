import AFTD.Prelude
import AFTD.Kb.Tcs.WeightedSetPackingInstance
import AFTD.Kb.Tcs.IsPacking

/-!
# op_98_conflict_degree_bound

Topic: approximation   Node: f5c7d463afd1

Provenance: helper lemma. step towards op_98_objective_switching_weighted_four_set_packing

A set a conflicts with at most a.card sets of any packing O: the intersections o ∩ a (o ∈ O, o not disjoint from a) are nonempty, pairwise disjoint subsets of a.
-/

/-- Degree bound: a single set intersects at most |a| members of a packing. -/
theorem op_98_conflict_degree_bound {α : Type*} [DecidableEq α] {k : ℕ}
    (inst : WeightedSetPackingInstance α k) (O : Finset (Finset α)) (a : Finset α)
    (hO : is_packing inst O) :
    (O.filter (fun o => ¬ Disjoint a o)).card ≤ a.card := by
  set F := O.filter (fun o => ¬ Disjoint a o) with hF
  have hmem : ∀ o, o ∈ F ↔ o ∈ O ∧ ¬ Disjoint a o := by
    intro o; rw [hF, Finset.mem_filter]
  have hpd : (F : Set (Finset α)).PairwiseDisjoint (fun o => o ∩ a) := by
    intro o ho o' ho' hne
    have hoO : o ∈ O := (hmem o).mp ho |>.1
    have ho'O : o' ∈ O := (hmem o').mp ho' |>.1
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (hO.2 hoO ho'O hne)
  have hcard : (F.biUnion (fun o => o ∩ a)).card = ∑ o ∈ F, (o ∩ a).card :=
    Finset.card_biUnion hpd
  have hsub : F.biUnion (fun o => o ∩ a) ⊆ a := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨o, ho, hxo⟩ := hx
    exact (Finset.mem_inter.mp hxo).2
  have hle : (F.biUnion (fun o => o ∩ a)).card ≤ a.card := Finset.card_le_card hsub
  have hnonempty : ∀ o ∈ F, 1 ≤ (o ∩ a).card := by
    intro o ho
    have hnd : ¬ Disjoint a o := (hmem o).mp ho |>.2
    obtain ⟨x, hxa, hxo⟩ := Finset.not_disjoint_iff.mp hnd
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxo, hxa⟩⟩
  calc F.card = ∑ o ∈ F, 1 := Finset.card_eq_sum_ones F
    _ ≤ ∑ o ∈ F, (o ∩ a).card := Finset.sum_le_sum hnonempty
    _ = (F.biUnion (fun o => o ∩ a)).card := hcard.symm
    _ ≤ a.card := hle
