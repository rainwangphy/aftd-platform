import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphFortTransversalNumber
import AFTD.Kb.Tcs.IsCompatibleCollection
import AFTD.Kb.Tcs.FinsetTransversalNumber
import AFTD.Kb.Tcs.SimpleGraphIsFort

/-!
# op_979_fort_transversal_number_empty_graph

Topic: graphs   Node: 3176163a72b5

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 6, Example 6.2

For the edgeless graph (the empty graph bot) on a finite vertex set V with decidable equality, the fort transversal number equals the number of vertices Fintype.card V.
-/

private lemma op_979_fort_transversal_number_empty_graph_singletons_fort {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ F ∈ Finset.univ.image (fun v : V => ({v} : Finset V)),
      simple_graph_is_fort (⊥ : SimpleGraph V) (F : Set V) := by
  intro F hF
  rw [Finset.mem_image] at hF
  obtain ⟨v, _, rfl⟩ := hF
  rw [Finset.coe_singleton]
  constructor
  · exact ⟨v, rfl⟩
  · intro u _
    simp

private lemma op_979_fort_transversal_number_empty_graph_singletons_compatible {V : Type*} [Fintype V] [DecidableEq V] :
    is_compatible_collection (Finset.univ.image (fun v : V => ({v} : Finset V))) := by
  unfold is_compatible_collection
  intro C1 h1 C2 h2 hne x hx
  rw [Finset.mem_image] at h1 h2
  obtain ⟨v, _, rfl⟩ := h1
  obtain ⟨w, _, rfl⟩ := h2
  rw [Finset.mem_inter, Finset.mem_singleton, Finset.mem_singleton] at hx
  exact absurd (by rw [show v = w from hx.1.symm.trans hx.2]) hne

private lemma op_979_fort_transversal_number_empty_graph_singletons_transversal {V : Type*} [Fintype V] [DecidableEq V] :
    finset_transversal_number (Finset.univ.image (fun v : V => ({v} : Finset V))) = Fintype.card V := by
  classical
  unfold finset_transversal_number
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨Finset.univ, ?_, Finset.card_univ⟩
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨v, _, rfl⟩ := hS
    rw [Finset.univ_inter]
    exact ⟨v, Finset.mem_singleton.mpr rfl⟩
  · apply le_csInf
    · refine ⟨Fintype.card V, Finset.univ, ?_, Finset.card_univ⟩
      intro S hS
      rw [Finset.mem_image] at hS
      obtain ⟨v, _, rfl⟩ := hS
      rw [Finset.univ_inter]
      exact ⟨v, Finset.mem_singleton.mpr rfl⟩
    · intro k hk
      obtain ⟨T, hT, rfl⟩ := hk
      have hTeq : T = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro v
        have hmem : ({v} : Finset V) ∈ Finset.univ.image (fun v : V => ({v} : Finset V)) :=
          Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
        have := hT _ hmem
        rw [Finset.Nonempty] at this
        obtain ⟨x, hx⟩ := this
        rw [Finset.mem_inter, Finset.mem_singleton] at hx
        rw [← hx.2]
        exact hx.1
      rw [hTeq, Finset.card_univ]

/-- For the edgeless graph on a finite vertex set V, T(⊥) = |V|. -/
theorem op_979_fort_transversal_number_empty_graph
    {V : Type*} [Fintype V] [DecidableEq V] :
    simple_graph_fort_transversal_number (⊥ : SimpleGraph V) = Fintype.card V := by
  classical
  unfold simple_graph_fort_transversal_number
  set C0 : Finset (Finset V) := Finset.univ.image (fun v : V => ({v} : Finset V)) with hC0
  have hC0_fort : ∀ F ∈ C0, simple_graph_is_fort (⊥ : SimpleGraph V) (F : Set V) := by
    rw [hC0]; exact op_979_fort_transversal_number_empty_graph_singletons_fort
  have hC0_compat : is_compatible_collection C0 := by
    rw [hC0]; exact op_979_fort_transversal_number_empty_graph_singletons_compatible
  have hC0_trans : finset_transversal_number C0 = Fintype.card V := by
    rw [hC0]; exact op_979_fort_transversal_number_empty_graph_singletons_transversal
  set S : Set ℕ := { k : ℕ | ∃ C : Finset (Finset V),
      (∀ F ∈ C, simple_graph_is_fort (⊥ : SimpleGraph V) (F : Set V)) ∧
      is_compatible_collection C ∧ finset_transversal_number C = k } with hS
  have hmem : Fintype.card V ∈ S := ⟨C0, hC0_fort, hC0_compat, hC0_trans⟩
  have hbdd : ∀ k ∈ S, k ≤ Fintype.card V := by
    intro k hk
    obtain ⟨C, hCf, hCc, hCt⟩ := hk
    rw [← hCt]
    apply Nat.sInf_le
    refine ⟨Finset.univ, ?_, Finset.card_univ⟩
    intro T hT
    rw [Finset.univ_inter]
    exact (hCf T hT).1
  apply le_antisymm
  · apply csSup_le
    · exact ⟨Fintype.card V, hmem⟩
    · exact hbdd
  · exact le_csSup ⟨Fintype.card V, hbdd⟩ hmem
