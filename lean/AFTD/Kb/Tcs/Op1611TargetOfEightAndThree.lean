import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationDiamGtMatching

/-!
# op_1611_target_of_eight_and_three

Topic: graphs   Node: 4cb45b1a5343

Provenance: helper lemma. step towards op_1611_min_max_degree_superlinear_matching_recoloring_diameter

If 8 satisfies the witness predicate and no Δ ≤ 3 does, then there is a unique Δ with 4 ≤ Δ ≤ 8 that is least in the set of witnesses.
-/

/-- The uniqueness/existence target follows from P(8) together with the failure of P on all Δ ≤ 3. -/
theorem op_1611_target_of_eight_and_three (h8 : simple_graph_reconfiguration_diam_gt_matching 8) (h4 : ∀ Δ : ℕ, Δ ≤ 3 → ¬ simple_graph_reconfiguration_diam_gt_matching Δ) : ∃! Δ : ℕ, 4 ≤ Δ ∧ Δ ≤ 8 ∧ IsLeast {d : ℕ | simple_graph_reconfiguration_diam_gt_matching d} Δ := by
  classical
  have hne : ∃ d, simple_graph_reconfiguration_diam_gt_matching d := ⟨8, h8⟩
  have hL : IsLeast {d : ℕ | simple_graph_reconfiguration_diam_gt_matching d} (Nat.find hne) :=
    ⟨Nat.find_spec hne, fun d hd => Nat.find_min' hne hd⟩
  refine ⟨Nat.find hne, ⟨?_, Nat.find_min' hne h8, hL⟩, fun y hy => hy.2.2.unique hL⟩
  by_contra h
  exact h4 _ (by omega) (Nat.find_spec hne)
