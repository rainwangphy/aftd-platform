import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphKIndependenceNumber
import AFTD.Kb.Tcs.SimpleGraphUpperKStarFormingNumber
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent
import AFTD.Kb.Tcs.SimpleGraphIsKIndependentIff
import AFTD.Kb.Tcs.SimpleGraphIsMinimalKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming
import AFTD.Kb.Tcs.SimpleGraphIsKIndependentEmpty
import AFTD.Kb.Tcs.SimpleGraphIsKStarFormingIff

/-!
# simple_graph_k_independence_number_le_upper_k_star_forming_number

Topic: graphs   Node: 93c877a48d45

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Theorem 2.3 (a theorem the paper cites from earlier work on k-star-forming sets).

For every finite graph G and every k, β_k(G) ≤ SF_k(G).
-/

open scoped Classical
open Finset

lemma simple_graph_k_independence_number_le_upper_k_star_forming_number_exists_maximal
    {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (I : Finset V) (hI : simple_graph_is_k_independent G k I) :
    ∃ J : Finset V, I ⊆ J ∧ simple_graph_is_k_independent G k J ∧
      ∀ v ∉ J, ¬ simple_graph_is_k_independent G k (insert v J) := by
  let S := (univ.filter (fun J => I ⊆ J ∧ simple_graph_is_k_independent G k J))
  have hI_in_S : I ∈ S := mem_filter.mpr ⟨mem_univ _, subset_rfl, hI⟩
  have hSne : S.Nonempty := ⟨I, hI_in_S⟩
  obtain ⟨J, hJ_mem, hJ_max⟩ := S.exists_max_image Finset.card hSne
  rw [mem_filter] at hJ_mem
  refine ⟨J, hJ_mem.2.1, hJ_mem.2.2, ?_⟩
  intro v hv h_ind
  have h_sub : I ⊆ insert v J := hJ_mem.2.1.trans (subset_insert v J)
  have h_ins_mem : insert v J ∈ S := mem_filter.mpr ⟨mem_univ _, h_sub, h_ind⟩
  have h_le := hJ_max (insert v J) h_ins_mem
  rw [card_insert_of_notMem hv] at h_le
  omega

lemma simple_graph_k_independence_number_le_upper_k_star_forming_number_k_star_forming
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (hk : 1 ≤ k) (J : Finset V) (hJ_ind : simple_graph_is_k_independent G k J)
    (hJ_max : ∀ v ∉ J, ¬ simple_graph_is_k_independent G k (insert v J)) :
    simple_graph_is_k_star_forming G k J := by
  rw [simple_graph_is_k_star_forming_iff G k hk J]
  intro v hv
  have h_not_ind := hJ_max v hv
  rw [simple_graph_is_k_independent_iff] at h_not_ind
  simp only [not_forall, not_lt] at h_not_ind
  obtain ⟨w, hw, hwk⟩ := h_not_ind
  rcases mem_insert.mp hw with hw_eq | hwJ
  · left
    rw [hw_eq] at hwk
    have : (insert v J).filter (G.Adj v) = J.filter (G.Adj v) := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hadj⟩
        · exact (G.irrefl hadj).elim
        · exact ⟨hx, hadj⟩
      · rintro ⟨hx, hadj⟩
        exact ⟨Or.inr hx, hadj⟩
    rwa [this] at hwk
  · right
    rw [simple_graph_is_k_independent_iff] at hJ_ind
    have hJw := hJ_ind w hwJ
    by_cases hadj : G.Adj w v
    · refine ⟨w, hwJ, hadj.symm, ?_⟩
      have : (insert v J).filter (G.Adj w) = insert v (J.filter (G.Adj w)) := by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxadj⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hx, hxadj⟩
        · rintro (rfl | ⟨hx, hxadj⟩)
          · exact ⟨Or.inl rfl, hadj⟩
          · exact ⟨Or.inr hx, hxadj⟩
      rw [this, card_insert_of_notMem] at hwk
      · omega
      · intro h
        exact hv (mem_filter.mp h).1
    · have : (insert v J).filter (G.Adj w) = J.filter (G.Adj w) := by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hx, hxadj⟩
          · exact (hadj hxadj).elim
          · exact ⟨hx, hxadj⟩
        · rintro ⟨hx, hxadj⟩
          exact ⟨Or.inr hx, hxadj⟩
      rw [this] at hwk
      omega

lemma simple_graph_k_independence_number_le_upper_k_star_forming_number_not_k_star_forming_of_ssubset
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (J : Finset V) (hJ : simple_graph_is_k_independent G k J) :
    ∀ T ⊂ J, ¬ simple_graph_is_k_star_forming G k T := by
  intro T hT hTsf
  obtain ⟨s, hsJ, hsT⟩ := exists_of_ssubset hT
  obtain ⟨c, L, hc, hL, hcard, hadj, -⟩ := hTsf s hsT
  have hcJ : c ∈ J := by
    rcases hc with rfl | hcT
    · exact hsJ
    · exact hT.1 hcT
  have h_sub : (L : Set V) ⊆ {u | u ∈ J ∧ G.Adj c u} := by
    intro x hx
    have hx_fin : x ∈ L := mem_coe.mp hx
    refine ⟨?_, hadj x hx_fin⟩
    rcases hL x hx_fin with rfl | hxT
    · exact hsJ
    · exact hT.1 hxT
  have h_le : (L : Set V).ncard ≤ ({u | u ∈ J ∧ G.Adj c u} : Set V).ncard :=
    Set.ncard_le_ncard h_sub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at h_le
  have h_lt := hJ c hcJ
  omega

theorem simple_graph_k_independence_number_le_upper_k_star_forming_number {V : Type*}
    [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    simple_graph_k_independence_number G k ≤ simple_graph_upper_k_star_forming_number G k := open Finset in by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : simple_graph_k_independence_number G 0 = 0 := by
      dsimp [simple_graph_k_independence_number]
      have h_empty : {n | ∃ I : Finset V, simple_graph_is_k_independent G 0 I ∧ I.card = n} = {0} := by
        ext n
        simp only [Set.mem_singleton_iff]
        constructor
        · rintro ⟨I, hI, rfl⟩
          rw [simple_graph_is_k_independent_iff] at hI
          have : I = ∅ := by
            rw [eq_empty_iff_forall_notMem]
            intro v hv
            have := hI v hv
            omega
          simp [this]
        · rintro rfl
          refine ⟨∅, ?_, card_empty⟩
          rw [simple_graph_is_k_independent_iff]
          intro v hv
          cases hv
      rw [h_empty]
      exact csSup_singleton 0
    rw [h0]
    omega
  · have hbdd_sf : BddAbove {n | ∃ S : Finset V,
        simple_graph_is_minimal_k_star_forming G k S ∧ S.card = n} := by
      refine ⟨Fintype.card V, ?_⟩
      rintro n ⟨S, -, rfl⟩
      exact card_le_univ S
    have hne_ind : {n | ∃ I : Finset V, simple_graph_is_k_independent G k I ∧ I.card = n}.Nonempty := by
      refine ⟨0, ∅, simple_graph_is_k_independent_empty G k, card_empty⟩
    dsimp [simple_graph_k_independence_number, simple_graph_upper_k_star_forming_number]
    apply csSup_le hne_ind
    rintro n ⟨I, hI, rfl⟩
    obtain ⟨J, hIJ, hJ_ind, hJ_max⟩ :=
      simple_graph_k_independence_number_le_upper_k_star_forming_number_exists_maximal G k I hI
    have hJ_sf :=
      simple_graph_k_independence_number_le_upper_k_star_forming_number_k_star_forming G k hk J hJ_ind hJ_max
    have hJ_min_sf : simple_graph_is_minimal_k_star_forming G k J :=
      ⟨hJ_sf, simple_graph_k_independence_number_le_upper_k_star_forming_number_not_k_star_forming_of_ssubset G k J hJ_ind⟩
    have hJ_mem : J.card ∈ {n | ∃ S : Finset V,
        simple_graph_is_minimal_k_star_forming G k S ∧ S.card = n} := ⟨J, hJ_min_sf, rfl⟩
    have h_le := le_csSup hbdd_sf hJ_mem
    exact (card_le_card hIJ).trans h_le
