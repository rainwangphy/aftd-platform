import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable
import AFTD.Kb.Tcs.BipartiteSubsetGraph
import AFTD.Kb.Tcs.BipartiteSubsetMinUncolorableR
import AFTD.Kb.Tcs.BipartiteSubsetUncolorableOfGe

/-!
# bipartite_subset_colorable_iff_below_threshold

Topic: graphs   Node: 33b8901669cc

Provenance: helper lemma. arXiv:2610.42094, Definition 1.2; monotonicity and least-threshold semantics for OP-861.

For positive k, the standard lists are colorable at threshold r exactly when r is less than the least uncolorable threshold.
-/

theorem op861_colorable_threshold_mono (k r s : ℕ) (hrs : r ≤ s)
    (h : bipartite_subset_standard_list_colorable k s) :
    bipartite_subset_standard_list_colorable k r := by
  obtain ⟨C, hC⟩ := h
  have hvalid : ∀ {v w}, (bipartite_subset_graph k r).Adj v w → C v ≠ C w := by
    intro v w hadj
    apply C.valid
    cases v <;> cases w <;> dsimp [bipartite_subset_graph] at hadj ⊢ <;> omega
  let D : (bipartite_subset_graph k r).Coloring (Fin (2*k-1)) :=
    SimpleGraph.Coloring.mk (fun v => C v) hvalid
  exact ⟨D, hC⟩

theorem bipartite_subset_colorable_iff_below_threshold (k r : ℕ) (hk : 1 ≤ k) : bipartite_subset_standard_list_colorable k r ↔ r < bipartite_subset_min_uncolorable_r k := by
  classical
  let A : Set ℕ := {s | ¬ bipartite_subset_standard_list_colorable k s}
  have hn : A.Nonempty := ⟨k, bipartite_subset_uncolorable_of_ge k k hk le_rfl⟩
  have hbad : ¬ bipartite_subset_standard_list_colorable k (bipartite_subset_min_uncolorable_r k) := by
    change sInf A ∈ A
    exact csInf_mem hn
  constructor
  · intro hc
    by_contra hnot
    have hle : bipartite_subset_min_uncolorable_r k ≤ r := by omega
    exact hbad (op861_colorable_threshold_mono k _ r hle hc)
  · intro hlt
    by_contra hbad'
    have hm : r ∈ A := hbad'
    have hle : bipartite_subset_min_uncolorable_r k ≤ r := by
      change sInf A ≤ r
      exact Nat.sInf_le hm
    omega
