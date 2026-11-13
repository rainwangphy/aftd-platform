import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingRootExposureCount
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.Tcs.IsZeroForcingSetMono
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.F

/-!
# tree_exposure_plain_partial_sync_counterexample

Topic: graphs   Node: 91c6290506e3

Provenance: helper lemma. An elementary obstruction to a proposed ordinary log-concavity route for OP-1399.

For a rooted three-vertex path the unexposed counts at ranks zero and one are one and three, while the exposed counts at ranks zero, one and two are zero, zero and one; thus the two sequences fail ordinary partial synchronization.
-/

open SimpleGraph

lemma tree_exposure_plain_partial_sync_counterexample_not_adj_0_0 : ¬ (pathGraph 3).Adj 0 0 := by rw [pathGraph_adj]; decide
lemma tree_exposure_plain_partial_sync_counterexample_not_adj_0_2 : ¬ (pathGraph 3).Adj 0 2 := by rw [pathGraph_adj]; decide
lemma tree_exposure_plain_partial_sync_counterexample_not_adj_2_0 : ¬ (pathGraph 3).Adj 2 0 := by rw [pathGraph_adj]; decide
lemma tree_exposure_plain_partial_sync_counterexample_not_adj_2_2 : ¬ (pathGraph 3).Adj 2 2 := by rw [pathGraph_adj]; decide

lemma tree_exposure_plain_partial_sync_counterexample_zf_zero : is_zero_forcing_set (pathGraph 3) ({0} : Set (Fin 3)) := by
  intro v
  have h0 : ZeroForced (pathGraph 3) {0} 0 := ZeroForced.init 0 (by simp)
  have hadj01 : (pathGraph 3).Adj 0 1 := by rw [pathGraph_adj]; decide
  have h1 : ZeroForced (pathGraph 3) {0} 1 := by
    apply ZeroForced.step 0 1 h0 hadj01
    intro x hx hne
    fin_cases x
    · exact False.elim (tree_exposure_plain_partial_sync_counterexample_not_adj_0_0 hx)
    · contradiction
    · exact False.elim (tree_exposure_plain_partial_sync_counterexample_not_adj_0_2 hx)
  have hadj12 : (pathGraph 3).Adj 1 2 := by rw [pathGraph_adj]; decide
  have h2 : ZeroForced (pathGraph 3) {0} 2 := by
    apply ZeroForced.step 1 2 h1 hadj12
    intro x hx hne
    fin_cases x
    · exact h0
    · exfalso; revert hx; rw [pathGraph_adj]; decide
    · contradiction
  fin_cases v
  · exact h0
  · exact h1
  · exact h2

lemma tree_exposure_plain_partial_sync_counterexample_zf_two : is_zero_forcing_set (pathGraph 3) ({2} : Set (Fin 3)) := by
  intro v
  have h2 : ZeroForced (pathGraph 3) {2} 2 := ZeroForced.init 2 (by simp)
  have hadj21 : (pathGraph 3).Adj 2 1 := by rw [pathGraph_adj]; decide
  have h1 : ZeroForced (pathGraph 3) {2} 1 := by
    apply ZeroForced.step 2 1 h2 hadj21
    intro x hx hne
    fin_cases x
    · exact False.elim (tree_exposure_plain_partial_sync_counterexample_not_adj_2_0 hx)
    · contradiction
    · exact False.elim (tree_exposure_plain_partial_sync_counterexample_not_adj_2_2 hx)
  have hadj10 : (pathGraph 3).Adj 1 0 := by rw [pathGraph_adj]; decide
  have h0 : ZeroForced (pathGraph 3) {2} 0 := by
    apply ZeroForced.step 1 0 h1 hadj10
    intro x hx hne
    fin_cases x
    · contradiction
    · exfalso; revert hx; rw [pathGraph_adj]; decide
    · exact h2
  fin_cases v
  · exact h0
  · exact h1
  · exact h2

lemma tree_exposure_plain_partial_sync_counterexample_zf_of_not_mem (W : Finset (Fin 3)) (h : 0 ∉ W ∨ 2 ∉ W) :
    is_zero_forcing_set (pathGraph 3) (((Finset.univ \ W : Finset (Fin 3)) : Set (Fin 3))) := by
  cases h with
  | inl h0 =>
    apply is_zero_forcing_set_mono (pathGraph 3) (S := {0})
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [h0]
    · exact tree_exposure_plain_partial_sync_counterexample_zf_zero
  | inr h2 =>
    apply is_zero_forcing_set_mono (pathGraph 3) (S := {2})
    · intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [h2]
    · exact tree_exposure_plain_partial_sync_counterexample_zf_two

lemma tree_exposure_plain_partial_sync_counterexample_exposed_12 : zero_forcing_root_exposed_fort (pathGraph 3) 0 {1, 2} := by
  refine ⟨{1, 2}, subset_rfl, by decide, ⟨1, by decide, by rw [pathGraph_adj]; decide⟩, ?_⟩
  intro u hu_ne hu_not w hw hadj
  fin_cases u
  · contradiction
  · exfalso; apply hu_not; decide
  · exfalso; apply hu_not; decide

lemma tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset (W : Finset (Fin 3)) (h : ¬ ({1, 2} : Finset (Fin 3)) ⊆ W) :
    ¬ zero_forcing_root_exposed_fort (pathGraph 3) 0 W := by
  intro ⟨F, hFW, hrF, ⟨w, hwF, hadj0w⟩, hfort⟩
  have h12 : 1 ∉ W ∨ 2 ∉ W := by
    by_contra hc
    push Not at hc
    apply h
    intro x hx
    fin_cases x
    · exfalso; revert hx; decide
    · exact hc.1
    · exact hc.2
  cases h12 with
  | inl h1W =>
    have h1F : 1 ∉ F := fun h => h1W (hFW h)
    have : w = 1 := by
      rw [pathGraph_adj] at hadj0w
      fin_cases w
      · revert hadj0w; decide
      · rfl
      · revert hadj0w; decide
    subst this
    exact h1F hwF
  | inr h2W =>
    have h2F : 2 ∉ F := fun h => h2W (hFW h)
    have hw1 : w = 1 := by
      rw [pathGraph_adj] at hadj0w
      fin_cases w
      · revert hadj0w; decide
      · rfl
      · revert hadj0w; decide
    have h2ne0 : (2 : Fin 3) ≠ 0 := by decide
    have h2adj1 : (pathGraph 3).Adj 2 1 := by rw [pathGraph_adj]; decide
    obtain ⟨x, hxF, hadj2x, hxnew⟩ := hfort 2 h2ne0 h2F w hwF (hw1 ▸ h2adj1)
    have : x = 1 := by
      have : x ≠ 0 := by
        intro hx0
        subst hx0
        revert hadj2x
        rw [pathGraph_adj]; decide
      have : x ≠ 2 := fun hx2 => h2F (hx2 ▸ hxF)
      fin_cases x
      · contradiction
      · rfl
      · contradiction
    apply hxnew
    rw [hw1, this]

lemma tree_exposure_plain_partial_sync_counterexample_finset_card_one (W : Finset (Fin 3)) (h : W.card = 1) :
    W = {0} ∨ W = {1} ∨ W = {2} := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
  fin_cases x <;> simp

lemma tree_exposure_plain_partial_sync_counterexample_finset_card_two (W : Finset (Fin 3)) (h : W.card = 2) :
    W = {0, 1} ∨ W = {0, 2} ∨ W = {1, 2} := by
  have h1 : (Finset.univ \ W).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ, Fintype.card_fin, h]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
  have hw : W = Finset.univ \ {x} := by
    have := Finset.sdiff_sdiff_eq_self (Finset.subset_univ W)
    rw [hx] at this
    exact this.symm
  fin_cases x
  · right; right; rw [hw]; decide
  · right; left; rw [hw]; decide
  · left; rw [hw]; decide

lemma tree_exposure_plain_partial_sync_counterexample_isTree : (pathGraph 3).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨SimpleGraph.pathGraph_connected 2, ?_⟩
  rw [Nat.card_fin, Nat.card_eq_fintype_card, <- SimpleGraph.edgeFinset_card]
  decide

lemma tree_exposure_plain_partial_sync_counterexample_c_0_false : zero_forcing_root_exposure_count (pathGraph 3) 0 0 false = 1 := by
  unfold zero_forcing_root_exposure_count
  have : {W : Finset (Fin 3) | W.card = 0 ∧ is_zero_forcing_set (pathGraph 3) ((Finset.univ \ W : Finset (Fin 3)) : Set (Fin 3)) ∧ ((false = true) ↔ zero_forcing_root_exposed_fort (pathGraph 3) 0 W)} = {∅} := by
    ext W
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hcard, -⟩
      exact Finset.card_eq_zero.mp hcard
    · rintro rfl
      refine ⟨rfl, tree_exposure_plain_partial_sync_counterexample_zf_of_not_mem ∅ (Or.inl (by decide)), ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      apply tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset
      decide
  rw [this]
  exact Set.ncard_singleton ∅

lemma tree_exposure_plain_partial_sync_counterexample_c_0_true : zero_forcing_root_exposure_count (pathGraph 3) 0 0 true = 0 := by
  unfold zero_forcing_root_exposure_count
  have : {W : Finset (Fin 3) | W.card = 0 ∧ is_zero_forcing_set (pathGraph 3) ((Finset.univ \ W : Finset (Fin 3)) : Set (Fin 3)) ∧ ((true = true) ↔ zero_forcing_root_exposed_fort (pathGraph 3) 0 W)} = ∅ := by
    ext W
    constructor
    · rintro ⟨hcard, _, he⟩
      have : W = ∅ := Finset.card_eq_zero.mp hcard
      subst this
      have hexp : zero_forcing_root_exposed_fort (pathGraph 3) 0 ∅ := he.mp rfl
      have hnot := tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset ∅ (by decide)
      exact hnot hexp
    · intro h
      exact False.elim h
  rw [this, Set.ncard_empty]

lemma tree_exposure_plain_partial_sync_counterexample_c_1_true : zero_forcing_root_exposure_count (pathGraph 3) 0 1 true = 0 := by
  unfold zero_forcing_root_exposure_count
  have : {W : Finset (Fin 3) | W.card = 1 ∧ is_zero_forcing_set (pathGraph 3) ((Finset.univ \ W : Finset (Fin 3)) : Set (Fin 3)) ∧ ((true = true) ↔ zero_forcing_root_exposed_fort (pathGraph 3) 0 W)} = ∅ := by
    ext W
    constructor
    · rintro ⟨hcard, _, he⟩
      have hexp : zero_forcing_root_exposed_fort (pathGraph 3) 0 W := he.mp rfl
      have hnot : ¬ zero_forcing_root_exposed_fort (pathGraph 3) 0 W := by
        apply tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset
        intro hsub
        have hc : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
        have : ({1, 2} : Finset (Fin 3)).card ≤ W.card := Finset.card_le_card hsub
        omega
      exact hnot hexp
    · intro h
      exact False.elim h
  rw [this, Set.ncard_empty]

lemma tree_exposure_plain_partial_sync_counterexample_c_2_true : zero_forcing_root_exposure_count (pathGraph 3) 0 2 true = 1 := by
  unfold zero_forcing_root_exposure_count
  have : {W : Finset (Fin 3) | W.card = 2 ∧ is_zero_forcing_set (pathGraph 3) ((Finset.univ \ W : Finset (Fin 3)) : Set (Fin 3)) ∧ ((true = true) ↔ zero_forcing_root_exposed_fort (pathGraph 3) 0 W)} = {{1, 2}} := by
    ext W
    constructor
    · rintro ⟨hcard, _, he⟩
      have hexp : zero_forcing_root_exposed_fort (pathGraph 3) 0 W := he.mp rfl
      obtain (h | h | h) := tree_exposure_plain_partial_sync_counterexample_finset_card_two W hcard
      · exfalso
        subst h
        exact tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset {0, 1} (by decide) hexp
      · exfalso
        subst h
        exact tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset {0, 2} (by decide) hexp
      · exact Set.mem_singleton_iff.mpr h
    · rintro rfl
      refine ⟨by decide, tree_exposure_plain_partial_sync_counterexample_zf_of_not_mem {1, 2} (Or.inl (by decide)), ?_⟩
      simp [tree_exposure_plain_partial_sync_counterexample_exposed_12]
  rw [this, Set.ncard_singleton]

lemma tree_exposure_plain_partial_sync_counterexample_c_1_false : zero_forcing_root_exposure_count (pathGraph 3) 0 1 false = 3 := by
  unfold zero_forcing_root_exposure_count
  have : {W : Finset (Fin 3) | W.card = 1 ∧ is_zero_forcing_set (pathGraph 3) ((Finset.univ \ W : Finset (Fin 3)) : Set (Fin 3)) ∧ ((false = true) ↔ zero_forcing_root_exposed_fort (pathGraph 3) 0 W)} = ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) := by
    ext W
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hcard, _, _⟩
      exact tree_exposure_plain_partial_sync_counterexample_finset_card_one W hcard
    · rintro (rfl | rfl | rfl)
      · refine ⟨by decide, tree_exposure_plain_partial_sync_counterexample_zf_of_not_mem {0} (Or.inr (by decide)), ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        apply tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset; decide
      · refine ⟨by decide, tree_exposure_plain_partial_sync_counterexample_zf_of_not_mem {1} (Or.inl (by decide)), ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        apply tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset; decide
      · refine ⟨by decide, tree_exposure_plain_partial_sync_counterexample_zf_of_not_mem {2} (Or.inl (by decide)), ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        apply tree_exposure_plain_partial_sync_counterexample_not_exposed_of_not_subset; decide
  rw [this, Set.ncard_coe_finset]
  decide

theorem tree_exposure_plain_partial_sync_counterexample : ∃ (T : SimpleGraph (Fin 3)) (r : Fin 3), T.IsTree ∧ zero_forcing_root_exposure_count T r 0 false = 1 ∧ zero_forcing_root_exposure_count T r 1 false = 3 ∧ zero_forcing_root_exposure_count T r 0 true = 0 ∧ zero_forcing_root_exposure_count T r 1 true = 0 ∧ zero_forcing_root_exposure_count T r 2 true = 1 := by
  refine ⟨pathGraph 3, 0, tree_exposure_plain_partial_sync_counterexample_isTree,
    tree_exposure_plain_partial_sync_counterexample_c_0_false,
    tree_exposure_plain_partial_sync_counterexample_c_1_false,
    tree_exposure_plain_partial_sync_counterexample_c_0_true,
    tree_exposure_plain_partial_sync_counterexample_c_1_true,
    tree_exposure_plain_partial_sync_counterexample_c_2_true⟩
