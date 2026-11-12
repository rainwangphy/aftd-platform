import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingBoundary
import AFTD.Kb.Tcs.ZeroForcingCl
import AFTD.Kb.Tcs.ZeroForcingBoundaryMono
import AFTD.Kb.Tcs.ZeroForcingSeq

/-!
# zero_forcing_boundary_cl_le

Topic: graphs   Node: d42dded34867

Provenance: formalization of a published result. Source: arXiv:2611.13244, Proposition 2.9 -- Stabilization of the zero forcing number of generalized Petersen graphs

Let G be a simple graph and S a finite subset of vertices. Then the extended cardinality of the boundary of the closure cl(S) is at most the extended cardinality of S.
-/

lemma zero_forcing_boundary_cl_le_encard_le_coe_of_forall_finset {α : Type*} (s : Set α) (k : ℕ)
    (h : ∀ (t : Finset α), (t : Set α) ⊆ s → t.card ≤ k) : s.encard ≤ k := by
  by_cases hfin : s.Finite
  · rw [Set.encard_le_coe_iff_finite_ncard_le]
    refine ⟨hfin, ?_⟩
    have ht : (hfin.toFinset : Set α) ⊆ s := by rw [hfin.coe_toFinset]
    have := h hfin.toFinset ht
    rwa [← Set.ncard_eq_toFinset_card s hfin] at this
  · obtain ⟨t, ht_sub, ht_card⟩ := Set.Infinite.exists_subset_card_eq hfin (k + 1)
    have := h t ht_sub
    omega

lemma zero_forcing_boundary_cl_le_seq_mono {V : Type*} (G : SimpleGraph V) (S : Set V) :
    Monotone (zero_forcing_seq G S) := by
  apply monotone_nat_of_le_succ
  intro n
  change zero_forcing_seq G S n ⊆ zero_forcing_seq G S (n + 1)
  rw [zero_forcing_seq]
  exact Set.subset_union_left

lemma zero_forcing_boundary_cl_le_exists_seq_subset_of_finset {V : Type*} (G : SimpleGraph V) (S : Set V)
    (t : Finset V) (ht : (t : Set V) ⊆ zero_forcing_cl G S) :
    ∃ N : ℕ, (t : Set V) ⊆ zero_forcing_seq G S N := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.insert_subset_iff] at ht
    obtain ⟨N', hN'⟩ := ih ht.2
    have ha_cl := ht.1
    rw [zero_forcing_cl, Set.mem_iUnion] at ha_cl
    obtain ⟨na, hna⟩ := ha_cl
    refine ⟨max na N', ?_⟩
    rw [Finset.coe_insert, Set.insert_subset_iff]
    refine ⟨zero_forcing_boundary_cl_le_seq_mono G S (le_max_left na N') hna, ?_⟩
    exact hN'.trans (zero_forcing_boundary_cl_le_seq_mono G S (le_max_right na N'))

lemma zero_forcing_boundary_cl_le_subset_boundary_seq_of_subset_cl {V : Type*} (G : SimpleGraph V) (S : Set V)
    (N : ℕ) {t : Set V} (ht : t ⊆ zero_forcing_boundary G (zero_forcing_cl G S))
    (htN : t ⊆ zero_forcing_seq G S N) :
    t ⊆ zero_forcing_boundary G (zero_forcing_seq G S N) := by
  intro x hx
  have hxb := ht hx
  rw [zero_forcing_boundary] at hxb ⊢
  rcases hxb with ⟨-, y, hy_adj, hy_not⟩
  refine ⟨htN hx, y, hy_adj, ?_⟩
  intro hy_in
  apply hy_not
  rw [zero_forcing_cl]
  exact Set.mem_iUnion.mpr ⟨N, hy_in⟩

lemma zero_forcing_boundary_cl_le_seq_le {V : Type*} (G : SimpleGraph V) {S : Set V}
    (hS : S.Finite) (N : ℕ) :
    (zero_forcing_boundary G (zero_forcing_seq G S N)).encard ≤ S.encard := by
  induction N with
  | zero =>
    change (zero_forcing_boundary G S).encard ≤ S.encard
    apply Set.encard_le_encard
    intro x hx
    rw [zero_forcing_boundary] at hx
    exact hx.1
  | succ n ih =>
    exact (zero_forcing_boundary_mono G hS n).trans ih

/-- The boundary of the zero forcing closure of a finite set S has cardinality at most |S|. -/
theorem zero_forcing_boundary_cl_le {V : Type*} (G : SimpleGraph V) {S : Set V} (hS : S.Finite) : (zero_forcing_boundary G (zero_forcing_cl G S)).encard ≤ S.encard := by
  obtain ⟨k, hk⟩ := hS.exists_encard_eq_coe
  rw [hk]
  apply zero_forcing_boundary_cl_le_encard_le_coe_of_forall_finset
  intro t ht
  have ht_cl : (t : Set V) ⊆ zero_forcing_cl G S := by
    intro x hx
    have := ht hx
    rw [zero_forcing_boundary] at this
    exact this.1
  obtain ⟨N, hN⟩ := zero_forcing_boundary_cl_le_exists_seq_subset_of_finset G S t ht_cl
  have ht_seq := zero_forcing_boundary_cl_le_subset_boundary_seq_of_subset_cl G S N ht hN
  have hle := Set.encard_le_encard ht_seq
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  have h_bound := hle.trans (zero_forcing_boundary_cl_le_seq_le G hS N)
  rw [hk, Nat.cast_le] at h_bound
  exact h_bound
