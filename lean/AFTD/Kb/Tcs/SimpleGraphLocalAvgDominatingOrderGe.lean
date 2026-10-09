import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLocalAvgDominatingOrder
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining
import AFTD.Kb.Tcs.FinsetDownClosedFamilyAvgCardLe

/-!
# simple_graph_local_avg_dominating_order_ge

Topic: graphs   Node: 4f9cc772d2c2

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Theorem 2.2.

For every finite graph G of order n and every vertex v, the dominating sets containing v have average size at least (n+1)/2, with equality if and only if v is adjacent to all other vertices (deg v = n − 1).
-/

theorem simple_graph_local_avg_dominating_order_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ((Fintype.card V : ℚ) + 1) / 2 ≤ simple_graph_local_avg_dominating_order G v ∧
      (simple_graph_local_avg_dominating_order G v = ((Fintype.card V : ℚ) + 1) / 2 ↔
        G.degree v = Fintype.card V - 1) := by
  classical
  set D := simple_graph_dominating_sets_containing G v with hD
  set n := Fintype.card V with hn
  set X : Finset V := Finset.univ.erase v with hX
  set I := D.image (fun S => Sᶜ) with hI
  have memD : ∀ S, S ∈ D ↔ v ∈ S ∧ ∀ w, w ∈ S ∨ ∃ u ∈ S, G.Adj u w := by
    intro S; rw [hD]; unfold simple_graph_dominating_sets_containing; simp
  have hcompl_inj : Set.InjOn (fun S : Finset V => Sᶜ) ↑D := fun S _ T _ h => compl_injective h
  have hDne : D.Nonempty := ⟨Finset.univ, (memD _).2 ⟨Finset.mem_univ v, fun w => Or.inl (Finset.mem_univ w)⟩⟩
  have hIne : I.Nonempty := hDne.image _
  have hIsub : ∀ T ∈ I, T ⊆ X := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
    intro w hw
    rw [hX, Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ w⟩
    rintro rfl
    exact (Finset.mem_compl.1 hw) ((memD S).1 hS).1
  have hIdown : ∀ T ∈ I, ∀ U ⊆ T, U ∈ I := by
    intro T hT U hU
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
    have hSU : S ⊆ Uᶜ := by
      intro w hw
      rw [Finset.mem_compl]
      intro hwU
      exact (Finset.mem_compl.1 (hU hwU)) hw
    refine Finset.mem_image.2 ⟨Uᶜ, (memD _).2 ⟨hSU ((memD S).1 hS).1, fun w => ?_⟩, compl_compl U⟩
    rcases ((memD S).1 hS).2 w with h | ⟨u, hu, hadj⟩
    · exact Or.inl (hSU h)
    · exact Or.inr ⟨u, hSU hu, hadj⟩
  have hcardI : I.card = D.card := Finset.card_image_of_injOn hcompl_inj
  have hsumI : ∑ T ∈ I, (T.card : ℚ) = ∑ S ∈ D, ((n : ℚ) - S.card) := by
    rw [hI, Finset.sum_image hcompl_inj]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ S)]
  have hXcard : X.card = n - 1 := by rw [hX, Finset.card_erase_of_mem (Finset.mem_univ v)]; rfl
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨v⟩
  have hDpos : (0 : ℚ) < D.card := by exact_mod_cast hDne.card_pos
  have key := finset_down_closed_family_avg_card_le X I hIne hIsub hIdown
  rw [hsumI, hcardI, hXcard, Nat.cast_sub hn1, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul] at key
  have havd : simple_graph_local_avg_dominating_order G v = (∑ S ∈ D, (S.card : ℚ)) / D.card := rfl
  have hsplit : ((D.card : ℚ) * n - ∑ S ∈ D, (S.card : ℚ)) / D.card =
      n - (∑ S ∈ D, (S.card : ℚ)) / D.card := by
    field_simp
  rw [hsplit, Nat.cast_one] at key
  obtain ⟨k1, k2⟩ := key
  refine ⟨?_, ?_⟩
  · rw [havd]; push_cast at k1 ⊢; linarith
  · rw [havd]
    have e1 : (∑ S ∈ D, (S.card : ℚ)) / D.card = ((n : ℚ) + 1) / 2 ↔
        (n : ℚ) - (∑ S ∈ D, (S.card : ℚ)) / D.card = ((n : ℚ) - 1) / 2 := by
      constructor <;> intro h <;> linarith
    rw [e1, k2]
    -- the complements fill the power set iff `v` is adjacent to every other vertex
    have hdeg : G.degree v = n - 1 ↔ ∀ w, w ≠ v → G.Adj v w := by
      rw [← G.card_neighborFinset_eq_degree]
      have hsubN : G.neighborFinset v ⊆ X := by
        intro w hw
        rw [hX, Finset.mem_erase]
        exact ⟨(G.ne_of_adj ((G.mem_neighborFinset v w).1 hw)).symm, Finset.mem_univ w⟩
      constructor
      · intro h w hw
        have heq : G.neighborFinset v = X :=
          Finset.eq_of_subset_of_card_le hsubN (by rw [hXcard, h])
        have : w ∈ X := by rw [hX, Finset.mem_erase]; exact ⟨hw, Finset.mem_univ w⟩
        rw [← heq, G.mem_neighborFinset] at this
        exact this
      · intro h
        have heq : G.neighborFinset v = X := by
          refine Finset.Subset.antisymm hsubN fun w hw => ?_
          rw [hX, Finset.mem_erase] at hw
          rw [G.mem_neighborFinset]; exact h w hw.1
        rw [heq, hXcard]
    rw [hdeg]
    constructor
    · intro hIX w hw
      have hXI : X ∈ I := by rw [hIX]; exact Finset.mem_powerset_self X
      obtain ⟨S, hS, hSX⟩ := Finset.mem_image.1 hXI
      have hSv : S = {v} := by
        rw [← compl_compl S, hSX, hX]
        ext u; simp
      rcases ((memD S).1 hS).2 w with h | ⟨u, hu, hadj⟩
      · rw [hSv, Finset.mem_singleton] at h; exact absurd h hw
      · rw [hSv, Finset.mem_singleton] at hu; rw [← hu]; exact hadj
    · intro hall
      refine Finset.Subset.antisymm (fun T hT => Finset.mem_powerset.2 (hIsub T hT)) fun T hT => ?_
      rw [Finset.mem_powerset] at hT
      have hvT : v ∈ Tᶜ := by
        rw [Finset.mem_compl]; intro h
        have := hT h
        rw [hX, Finset.mem_erase] at this
        exact this.1 rfl
      refine Finset.mem_image.2 ⟨Tᶜ, (memD _).2 ⟨hvT, fun w => ?_⟩, compl_compl T⟩
      by_cases hw : w = v
      · exact Or.inl (hw ▸ hvT)
      · exact Or.inr ⟨v, hvT, hall w hw⟩
