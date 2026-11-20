import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.FactorcriticalInduceOneAfterVertexRestriction
import AFTD.Kb.Tcs.NontrivialFactorcriticalGraphConnected

/-!
# factorcritical_separator_lower_bound

Topic: graphs   Node: b4ec8894c1f4

Provenance: helper lemma. OP-1957 factor-critical crossing-cut link; scratch Lean axiom audit completed.

A separator between two nonempty parts in a 2k-factor-critical graph of the displayed order has at least 2k vertices.
-/

theorem factorcritical_separator_lower_bound
    (k d : ℕ) (G : SimpleGraph (Fin (2*k+d+3)))
    (hcrit : is_k_factor_critical G (2*k))
    (C A B : Finset (Fin (2*k+d+3)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hCA : Disjoint C A) (hCB : Disjoint C B)
    (hAB : Disjoint A B) (hpart : C ∪ A ∪ B = Finset.univ)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : 2*k ≤ C.card := by
  classical
  by_contra hn
  have hCsmall : C.card < 2*k := by omega
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  have hab : a ≠ b := by
    intro heq
    subst b
    exact (Finset.disjoint_left.mp hAB) ha hb
  have haC : a ∉ C := fun h => (Finset.disjoint_left.mp hCA) h ha
  have hbC : b ∉ C := fun h => (Finset.disjoint_left.mp hCB) h hb
  let P : Finset (Fin (2*k+d+3)) := ((Finset.univ \ C).erase a).erase b
  have hPcard : d+2 ≤ P.card := by
    have hC := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    simp only [Finset.card_univ,Fintype.card_fin] at hC
    have haU : a ∈ Finset.univ \ C := by simp [haC]
    have hbU : b ∈ (Finset.univ \ C).erase a := by simp [hbC,hab.symm]
    dsimp [P]
    rw [Finset.card_erase_of_mem hbU,Finset.card_erase_of_mem haU]
    omega
  obtain ⟨T,hTP,hTcard⟩ := Finset.exists_subset_card_eq hPcard
  let S := insert a (insert b T)
  have haT : a ∉ T := by
    intro h
    have := hTP h
    simp [P] at this
  have hbT : b ∉ T := by
    intro h
    have := hTP h
    simp [P] at this
  have hSsize : S.card + 2*k = Fintype.card (Fin (2*k+d+3)) + 1 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem (by simp [hab,haT]),Finset.card_insert_of_notMem hbT,hTcard]
    simp only [Fintype.card_fin]
    omega
  have hSA : a ∈ S := by simp [S]
  have hSB : b ∈ S := by simp [S]
  have hSnotC : ∀ v ∈ S, v ∉ C := by
    intro v hv
    dsimp [S] at hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact haC
    · exact hbC
    · have hvP := hTP hv
      dsimp [P] at hvP
      exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hvP))).2
  have hSAB : ∀ v ∈ S, v ∈ A ∨ v ∈ B := by
    intro v hv
    have hp : v ∈ C ∪ A ∪ B := by rw [hpart]; exact Finset.mem_univ v
    rcases Finset.mem_union.mp hp with hp | hb'
    · rcases Finset.mem_union.mp hp with hc | ha'
      · exact ((hSnotC v hv) hc).elim
      · exact Or.inl ha'
    · exact Or.inr hb'
  let D := G.induce {v | v ∈ S}
  have hDcrit : is_k_factor_critical D 1 := factorcritical_induce_one_after_vertex_restriction G (2*k) hcrit S hSsize
  let av : {v // v ∈ S} := ⟨a,hSA⟩
  let bv : {v // v ∈ S} := ⟨b,hSB⟩
  have hne : av ≠ bv := fun he => hab (congrArg Subtype.val he)
  have hconn := nontrivial_factorcritical_graph_connected D hDcrit av bv hne
  have hreach : D.Reachable av bv := hconn.preconnected av bv
  have hprop : ∀ u v : {v // v ∈ S}, D.Reachable u v → u.val ∈ A → v.val ∈ A := by
    intro u v hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => intro hu; exact hu
    | @cons u v w huv p ih =>
      intro hu
      apply ih
      rcases hSAB v.val v.property with hvA | hvB
      · exact hvA
      · exact (hcross u.val hu v.val hvB huv).elim
  have hbA := hprop av bv hreach ha
  exact (Finset.disjoint_left.mp hAB) hbA hb
