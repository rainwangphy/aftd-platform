import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# condorcet_voter_bad_outsiders_eq_min_rank

Topic: social_choice   Node: 687b55b4d6a3

Provenance: helper lemma. step towards condorcet_dimension_le_three_balanced

For a permutation `perm` of `Fin m` and a nonempty subset S, the number of candidates outside S ranked strictly above every element of S by `perm` equals the minimum rank of S under `perm`.
-/

/-- For a single voter, the number of outside candidates ranked above all members of S equals the minimum rank of S under that voter's preference permutation. -/
theorem condorcet_voter_bad_outsiders_eq_min_rank {m : ℕ} (perm : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) (hS : S.Nonempty) :
    ((Finset.univ \ S).filter (fun a => ∀ s ∈ S, perm a < perm s)).card =
      (S.image (fun s => (perm s).val)).min' (hS.image _) := by
  set r := (S.image (fun s => (perm s).val)).min' (hS.image _) with hr
  have h_filter_sdiff : (Finset.univ \ S).filter (fun a => ∀ s ∈ S, perm a < perm s) =
      Finset.univ.filter (fun a => ∀ s ∈ S, perm a < perm s) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun ha => lt_irrefl _ (h a ha), h⟩⟩
  rw [h_filter_sdiff]
  have h_pred (a : Fin m) : (∀ s ∈ S, perm a < perm s) ↔ (perm a).val < r := by
    rw [hr, Finset.lt_min'_iff]
    simp
  have h_filter_eq : Finset.univ.filter (fun a => ∀ s ∈ S, perm a < perm s) =
      Finset.univ.filter (fun a => (perm a).val < r) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h_pred]
  rw [h_filter_eq]
  have h_card_perm : (Finset.univ.filter (fun a => (perm a).val < r)).card =
      (Finset.univ.filter (fun b : Fin m => b.val < r)).card := by
    have h_map : Finset.univ.filter (fun a => (perm a).val < r) =
        (Finset.univ.filter (fun b : Fin m => b.val < r)).map perm.symm.toEmbedding := by
      ext a
      simp
    rw [h_map, Finset.card_map]
  rw [h_card_perm]
  rw [Fin.card_filter_val_lt]
  have hr_lt : r < m := by
    rw [hr]
    have hr_mem := Finset.min'_mem (S.image (fun s => (perm s).val)) (hS.image _)
    simp only [Finset.mem_image] at hr_mem
    rcases hr_mem with ⟨s, _, hs⟩
    rw [← hs]
    exact (perm s).isLt
  exact min_eq_right (le_of_lt hr_lt)
