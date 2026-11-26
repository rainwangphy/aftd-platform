import AFTD.Prelude
import AFTD.Kb.Tcs.IsGeneratingConnectionSet

/-!
# is_generating_connection_set_univ_erase_one

Topic: combinatorics   Node: e26d0f14cf18

Provenance: helper lemma. sanity lemma for connected_intersection_density (arXiv:2611.26732, Definition 1.4: the maximum exists because G \ {e} is admissible)

In every finite group $G$, the set $G \setminus \{1\}$ of all non-identity elements is an inverse-closed generating connection set.
-/

theorem is_generating_connection_set_univ_erase_one (G : Type*) [Group G] [Fintype G] [DecidableEq G] : is_generating_connection_set G (Finset.univ.erase 1) := by
  refine ⟨by simp, fun s hs => ?_, ?_⟩
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hs ⊢
    exact inv_ne_one.mpr hs
  · rw [eq_top_iff]
    intro g _
    by_cases hg : g = 1
    · rw [hg]; exact one_mem _
    · exact Subgroup.subset_closure (by simp [hg])
