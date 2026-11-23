import AFTD.Prelude
import AFTD.Kb.Tcs.HigherBruhatPacketConsistent
import AFTD.Kb.Tcs.PosetDimension
import AFTD.Kb.Tcs.HigherBruhatIncLe
import AFTD.Kb.Tcs.HigherBruhatInc
import AFTD.Kb.Tcs.BipartiteSubgraphPosetDimensionPowLowerBound
import AFTD.Kb.Tcs.IsPosetRealizer

/-!
# higher_bruhat_inc_poset_dimension_ge_card_of_boolean_subposet

Topic: combinatorics   Node: 659272bc31d3

Provenance: helper lemma. arXiv:2611.17465, Section 2.1

If X and S are disjoint families of (k+1)-element subsets of {0, ..., n-1} such that X ∪ E is packet-consistent for every subcollection E ⊆ S, then the Dushnik–Miller dimension of the inclusion higher Bruhat order B_inc(n, k) is at least the cardinality of S.
-/

def higher_bruhat_inc_poset_dimension_ge_card_of_boolean_subposet_mk
    (n k : ℕ) (X S : Finset (Finset (Fin n)))
    (hX : ∀ A ∈ X, A.card = k + 1) (hS : ∀ A ∈ S, A.card = k + 1)
    (hcons : ∀ E ⊆ S, higher_bruhat_packet_consistent n k (X ∪ E))
    (E : Finset (Finset (Fin n))) (hE : E ⊆ S) : higher_bruhat_inc n k :=
  ⟨X ∪ E, ⟨by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact hX A hA
    · exact hS A (hE hA),
    hcons E hE⟩⟩

/-- A Boolean interval of size |S| in the inclusion higher Bruhat order forces poset dimension at least |S|. -/
lemma higher_bruhat_inc_poset_dimension_ge_card_of_boolean_subposet
    (n k : ℕ) (X S : Finset (Finset (Fin n)))
    (hX : ∀ A ∈ X, A.card = k + 1)
    (hS : ∀ A ∈ S, A.card = k + 1)
    (hdisj : Disjoint X S)
    (hcons : ∀ E ⊆ S, higher_bruhat_packet_consistent n k (X ∪ E)) :
    S.card ≤ poset_dimension (higher_bruhat_inc_le n k) := by
  classical
  by_cases hS_empty : S = ∅
  · rw [hS_empty, Finset.card_empty]
    exact Nat.zero_le _
  have : Fintype (higher_bruhat_inc n k) := Subtype.fintype _
  have hpo : IsPartialOrder (higher_bruhat_inc n k) (higher_bruhat_inc_le n k) :=
    { refl := fun _ => Finset.Subset.refl _
      trans := fun _ _ _ => Finset.Subset.trans
      antisymm := fun _ _ hxy hyx => Subtype.ext (Finset.Subset.antisymm hxy hyx) }
  obtain ⟨R, hR⟩ := @bspd_hexists_realizer_of_poset_dimension
    (higher_bruhat_inc n k) this inferInstance
    (Fintype.card (higher_bruhat_inc n k)) rfl (higher_bruhat_inc_le n k) hpo
  let v (s : {s // s ∈ S}) : higher_bruhat_inc n k :=
    higher_bruhat_inc_poset_dimension_ge_card_of_boolean_subposet_mk
      n k X S hX hS hcons {s.1} (Finset.singleton_subset_iff.mpr s.2)
  let u (s : {s // s ∈ S}) : higher_bruhat_inc n k :=
    higher_bruhat_inc_poset_dimension_ge_card_of_boolean_subposet_mk
      n k X S hX hS hcons (S.erase s.1) (Finset.erase_subset s.1 S)
  have hnot_le : ∀ s : {s // s ∈ S}, ¬ higher_bruhat_inc_le n k (v s) (u s) := by
    intro s h
    change X ∪ {s.1} ⊆ X ∪ (S.erase s.1) at h
    have hs_in : s.1 ∈ X ∪ {s.1} := Finset.mem_union_right X (Finset.mem_singleton_self s.1)
    have hs_in2 : s.1 ∈ X ∪ (S.erase s.1) := h hs_in
    rcases Finset.mem_union.mp hs_in2 with h1 | h2
    · exact Finset.disjoint_right.mp hdisj s.2 h1
    · exact Finset.notMem_erase s.1 S h2
  have hle_of_ne : ∀ s t : {s // s ∈ S}, s ≠ t → higher_bruhat_inc_le n k (v s) (u t) := by
    intro s t hst
    change X ∪ {s.1} ⊆ X ∪ (S.erase t.1)
    have hne : s.1 ≠ t.1 := by
      intro h
      apply hst
      exact Subtype.ext h
    have hs_mem : s.1 ∈ S.erase t.1 := Finset.mem_erase.mpr ⟨hne, s.2⟩
    have hsub : {s.1} ⊆ S.erase t.1 := Finset.singleton_subset_iff.mpr hs_mem
    exact Finset.union_subset_union_right hsub
  have h_ex_i : ∀ s : {s // s ∈ S}, ∃ i : Fin (poset_dimension (higher_bruhat_inc_le n k)),
      ¬ (R i).le (v s) (u s) := by
    intro s
    by_contra hcon
    have hall : ∀ i, (R i).le (v s) (u s) := by
      intro i
      by_contra hi
      exact hcon ⟨i, hi⟩
    have : higher_bruhat_inc_le n k (v s) (u s) := (hR (v s) (u s)).mpr hall
    exact hnot_le s this
  choose f hf using h_ex_i
  have hf_inj : Function.Injective f := by
    intro s t hst
    by_contra h_ne
    have h1 := hf s
    have h2 := hf t
    rw [hst] at h1
    set lo := R (f t)
    have h_le1 : higher_bruhat_inc_le n k (v s) (u t) := hle_of_ne s t h_ne
    have h_le2 : higher_bruhat_inc_le n k (v t) (u s) := hle_of_ne t s (Ne.symm h_ne)
    have h_R_le1 : lo.le (v s) (u t) := (hR (v s) (u t)).mp h_le1 (f t)
    have h_R_le2 : lo.le (v t) (u s) := (hR (v t) (u s)).mp h_le2 (f t)
    have h_u_v : lo.le (u s) (v s) := by
      rcases lo.le_total (u s) (v s) with h | h
      · exact h
      · exact False.elim (h1 h)
    have h_ut_vt : lo.le (u t) (v t) := by
      rcases lo.le_total (u t) (v t) with h | h
      · exact h
      · exact False.elim (h2 h)
    have h_u_ut : lo.le (u s) (u t) := lo.le_trans (u s) (v s) (u t) h_u_v h_R_le1
    have h_ut_u : lo.le (u t) (u s) := lo.le_trans (u t) (v t) (u s) h_ut_vt h_R_le2
    have h_eq : u s = u t := lo.le_antisymm (u s) (u t) h_u_ut h_ut_u
    rw [h_eq] at h1
    exact h1 h_R_le1
  have hcard := Fintype.card_le_of_injective f hf_inj
  rw [Fintype.card_coe, Fintype.card_fin] at hcard
  exact hcard
