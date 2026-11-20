import AFTD.Prelude
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.PerfectMatchingTransportGraphIso

/-!
# factorcritical_induce_one_after_vertex_restriction

Topic: graphs   Node: 948ef0129504

Provenance: helper lemma. OP-1957 factor-critical residual bridge reduction.

An induced graph obtained from a k-factor-critical graph by retaining n−k+1 vertices is 1-factor-critical.
-/

theorem factorcritical_induce_one_after_vertex_restriction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (hcrit : is_k_factor_critical G k)
    (S : Finset V) (hS : S.card + k = Fintype.card V + 1) :
    is_k_factor_critical (G.induce {v | v ∈ S}) 1 := by
  classical
  intro W hW
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hW
  let T := (Finset.univ : Finset V) \ S.erase b.val
  have hbS : b.val ∈ S := b.property
  have hsc : (S.erase b.val).card + k = Fintype.card V := by
    rw [Finset.card_erase_of_mem hbS]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨b.val,hbS⟩
    omega
  have hT : T.card = k := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S.erase b.val))
    simp only [Finset.card_univ] at h
    dsimp [T]
    omega
  have hm := hcrit T hT
  have hs : (↑({b} : Finset {v : V // v ∈ S}) : Set {v : V // v ∈ S})ᶜ =
      {v | v ≠ b} := by
    ext v
    simp
  rw [hs]
  let e : (G.induce (T : Set V)ᶜ) ≃g ((G.induce {v | v ∈ S}).induce {v | v ≠ b}) := {
    toFun := fun v => by
      have hv : v.val ∈ S.erase b.val := by simpa [T, and_comm] using v.property
      refine ⟨⟨v.val, Finset.mem_of_mem_erase hv⟩, ?_⟩
      intro h
      exact (Finset.ne_of_mem_erase hv) (congrArg Subtype.val h)
    invFun := fun v => by
      have hvne : v.val.val ≠ b.val := by
        intro h
        exact v.property (Subtype.ext h)
      have hv : v.val.val ∈ S.erase b.val := Finset.mem_erase.mpr ⟨hvne, v.val.property⟩
      exact ⟨v.val.val, by simpa [T] using hv⟩
    left_inv := by intro v; apply Subtype.ext; rfl
    right_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl
    map_rel_iff' := by intro a c; rfl }
  exact perfect_matching_transport_graph_iso _ _ e hm
