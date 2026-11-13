import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingRootExposedFort
import AFTD.Kb.Tcs.ZeroForcingAttachLeaf
import AFTD.Kb.Tcs.ZfsComplIffNoStuck
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# root_exposed_fort_iff_new_white_leaf_breaks_forcing

Topic: graphs   Node: 2d2f18c56fe2

Provenance: helper lemma. The operational meaning of the rooted boundary state in OP-1399; a related leaf inequality is in arXiv:2605.10836, Section 3, Lemma 4.

If the complement of W is a zero forcing set of G, then W contains a root-exposed fort exactly when the same originally blue vertices fail to force the graph obtained by adjoining an initially white leaf at r.
-/

open Finset

def root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf
    {V : Type*} [DecidableEq V] (W : Finset V) : Finset (Option V) :=
  insert none (W.map ⟨Option.some, Option.some_injective V⟩)

lemma root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_t_leaf_some
    {V : Type*} [DecidableEq V] {v : V} {W : Finset V} :
    some v ∈ root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf W ↔ v ∈ W := by
  simp [root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf]

def root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v
    {V : Type*} [Fintype V] [DecidableEq V] (W1 : Finset (Option V)) : Finset V :=
  Finset.univ.filter (fun v => some v ∈ W1)

lemma root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v
    {V : Type*} [Fintype V] [DecidableEq V] {W1 : Finset (Option V)} {v : V} :
    v ∈ root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v W1 ↔ some v ∈ W1 := by
  simp [root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v]

lemma root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v_sub
    {V : Type*} [Fintype V] [DecidableEq V] {W1 : Finset (Option V)} {W : Finset V}
    (h : W1 ⊆ root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf W) :
    root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v W1 ⊆ W := by
  intro v hv
  rw [root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v] at hv
  have := h hv
  rwa [root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_t_leaf_some] at this

lemma root_exposed_fort_iff_new_white_leaf_breaks_forcing_compl_t_leaf_eq
    {V : Type*} [Fintype V] [DecidableEq V] (W : Finset V) :
    (Option.some '' (((Finset.univ \ W : Finset V) : Set V))) =
    ((Finset.univ \ root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf W : Finset (Option V)) : Set (Option V)) := by
  ext (x | x)
  · simp [root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf]
  · simp [root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf]

theorem root_exposed_fort_iff_new_white_leaf_breaks_forcing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V) (W : Finset V) (hW : is_zero_forcing_set G ((Finset.univ \ W : Finset V) : Set V)) : zero_forcing_root_exposed_fort G r W ↔ ¬ is_zero_forcing_set (zero_forcing_attach_leaf G r) (Option.some '' (((Finset.univ \ W : Finset V) : Set V))) := by
  constructor
  · intro hF
    rw [root_exposed_fort_iff_new_white_leaf_breaks_forcing_compl_t_leaf_eq, zfs_compl_iff_no_stuck]
    intro h
    rcases hF with ⟨F, hFW, hrF, ⟨w0, hw0F, hrw0⟩, hfort⟩
    apply h
    refine ⟨insert none (F.map ⟨Option.some, Option.some_injective V⟩), ?_, ?_, ?_⟩
    · exact Finset.insert_nonempty none _
    · intro x hx
      simp only [root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf,
        mem_insert, mem_map, Function.Embedding.coeFn_mk] at hx ⊢
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · left; rfl
      · right; exact ⟨y, hFW hy, rfl⟩
    · intro u hu w hw hadj
      rcases u with _ | u
      · exfalso
        apply hu
        simp only [mem_insert, true_or]
      · simp only [mem_insert, mem_map, Function.Embedding.coeFn_mk] at hw
        rcases hw with rfl | ⟨w', hw', rfl⟩
        · have hu_eq_r : u = r := hadj
          rw [hu_eq_r]
          refine ⟨some w0, ?_, ?_, ?_⟩
          · simp only [mem_insert, mem_map, Function.Embedding.coeFn_mk]
            right; exact ⟨w0, hw0F, rfl⟩
          · exact hrw0
          · intro h; cases h
        · have hadj_G : G.Adj u w' := hadj
          have huF : u ∉ F := by
            intro huF
            apply hu
            simp only [mem_insert, mem_map, Function.Embedding.coeFn_mk]
            right; exact ⟨u, huF, rfl⟩
          by_cases hur : u = r
          · rw [hur]
            refine ⟨none, ?_, ?_, ?_⟩
            · simp only [mem_insert, true_or]
            · show r = r; rfl
            · intro h; cases h
          · rcases hfort u hur huF w' hw' hadj_G with ⟨x', hx'F, hadjx', hne⟩
            refine ⟨some x', ?_, ?_, ?_⟩
            · simp only [mem_insert, mem_map, Function.Embedding.coeFn_mk]
              right; exact ⟨x', hx'F, rfl⟩
            · exact hadjx'
            · intro h
              injection h with h'
              exact hne h'
  · intro h_not
    rw [root_exposed_fort_iff_new_white_leaf_breaks_forcing_compl_t_leaf_eq, zfs_compl_iff_no_stuck] at h_not
    have h_ex : ∃ W1 : Finset (Option V), W1.Nonempty ∧
        W1 ⊆ root_exposed_fort_iff_new_white_leaf_breaks_forcing_t_leaf W ∧
        ∀ u ∉ W1, ∀ w ∈ W1, (zero_forcing_attach_leaf G r).Adj u w →
          ∃ x ∈ W1, (zero_forcing_attach_leaf G r).Adj u x ∧ x ≠ w := by
      by_contra hc
      exact h_not hc
    rcases h_ex with ⟨W1, hW1_ne, hW1_sub, hW1_fort⟩
    rw [zfs_compl_iff_no_stuck] at hW
    have h_none_in : none ∈ W1 := by
      by_contra h_none_notin
      apply hW
      refine ⟨root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v W1, ?_,
        root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v_sub hW1_sub, ?_⟩
      · rcases hW1_ne with ⟨x, hx⟩
        cases x with
        | none => contradiction
        | some v =>
          exact ⟨v, root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr hx⟩
      · intro u hu w hw hadj
        rw [root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v] at hw
        have hu_not_in : some u ∉ W1 := fun h => hu
          (root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr h)
        have hadj' : (zero_forcing_attach_leaf G r).Adj (some u) (some w) := hadj
        rcases hW1_fort (some u) hu_not_in (some w) hw hadj' with ⟨x, hx, hadjx, hxne⟩
        cases x with
        | none => contradiction
        | some x_v =>
          refine ⟨x_v, root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr hx, hadjx, ?_⟩
          intro heq
          subst heq
          exact hxne rfl
    have hr_notin : r ∉ root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v W1 := by
      intro hr_in
      apply hW
      refine ⟨root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v W1,
        ⟨r, hr_in⟩, root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v_sub hW1_sub, ?_⟩
      intro u hu w hw hadj
      rw [root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v] at hw
      have hu_not_in : some u ∉ W1 := fun h => hu
        (root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr h)
      have hadj' : (zero_forcing_attach_leaf G r).Adj (some u) (some w) := hadj
      rcases hW1_fort (some u) hu_not_in (some w) hw hadj' with ⟨x, hx, hadjx, hxne⟩
      cases x with
      | none =>
        have hu_eq_r : u = r := hadjx
        subst hu_eq_r
        exact (hu hr_in).elim
      | some x_v =>
        refine ⟨x_v, root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr hx, hadjx, ?_⟩
        intro heq
        subst heq
        exact hxne rfl
    refine ⟨root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v W1,
      root_exposed_fort_iff_new_white_leaf_breaks_forcing_to_v_sub hW1_sub, hr_notin, ?_, ?_⟩
    · have hr_notin' : some r ∉ W1 := fun h => hr_notin
        (root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr h)
      have hadj_leaf : (zero_forcing_attach_leaf G r).Adj (some r) none := rfl
      rcases hW1_fort (some r) hr_notin' none h_none_in hadj_leaf with ⟨x, hx, hadjx, hxne⟩
      cases x with
      | none => exact (hxne rfl).elim
      | some w =>
        refine ⟨w, root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr hx, hadjx⟩
    · intro u hur hu w hw hadj
      have hu_not_in : some u ∉ W1 := fun h => hu
        (root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr h)
      rw [root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v] at hw
      have hadj' : (zero_forcing_attach_leaf G r).Adj (some u) (some w) := hadj
      rcases hW1_fort (some u) hu_not_in (some w) hw hadj' with ⟨x, hx, hadjx, hxne⟩
      cases x with
      | none =>
        have hu_eq_r : u = r := hadjx
        exact (hur hu_eq_r).elim
      | some x_v =>
        refine ⟨x_v, root_exposed_fort_iff_new_white_leaf_breaks_forcing_mem_to_v.mpr hx, hadjx, ?_⟩
        intro heq
        subst heq
        exact hxne rfl
