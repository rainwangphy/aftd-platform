import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.SupportGraph

/-!
# witness_family_ramsey_property

Topic: combinatorics   Node: b1d46964e022

Provenance: helper lemma. arXiv:2611.15376 Proposition 3.1

For every simple graph G on a type V, natural numbers r, s, t, b, N, and family W of subsets of Fin r such that every member of W has cardinality t and every s-subset of Fin r contains at least b members of W, if the set-coloring Ramsey property set_coloring_ramsey_property G W.card b 1 N holds, then set_coloring_ramsey_property G r s t N holds.
-/

open scoped Classical in
/-- Reduction of set-coloring Ramsey property via witness families. -/
theorem witness_family_ramsey_property
    {V : Type*} (G : SimpleGraph V)
    (r s t b N : ℕ)
    (W : Finset (Finset (Fin r)))
    (hW_card : ∀ w ∈ W, w.card = t)
    (hW_cov : ∀ S : Finset (Fin r), S.card = s → b ≤ (W.filter (· ⊆ S)).card)
    (h_prop : set_coloring_ramsey_property G W.card b 1 N) :
    set_coloring_ramsey_property G r s t N := by
  intro ϕ hϕ
  let w : Fin W.card → Finset (Fin r) := fun i => (W.equivFin.symm i).1
  have hw_mem : ∀ i, w i ∈ W := fun i => (W.equivFin.symm i).2
  have hw_card : ∀ i, (w i).card = t := fun i => hW_card _ (hw_mem i)
  have hgood_card : ∀ e : (⊤ : SimpleGraph (Fin N)).edgeSet,
      b ≤ (Finset.univ.filter (fun i : Fin W.card => w i ⊆ ϕ e)).card := by
    intro e
    have h := hW_cov (ϕ e) (hϕ e)
    have hcardEq : (Finset.univ.filter (fun i : Fin W.card => w i ⊆ ϕ e)).card
        = (W.filter (· ⊆ ϕ e)).card := by
      symm
      apply Finset.card_bij (fun a ha => W.equivFin ⟨a, (Finset.mem_filter.mp ha).1⟩)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hh := (Finset.mem_filter.mp ha).2
        have h2 := congrArg Subtype.val (Equiv.symm_apply_apply W.equivFin ⟨a, (Finset.mem_filter.mp ha).1⟩)
        simp only at h2
        dsimp only [w]
        rw [h2]; exact hh
      · intro a1 ha1 a2 ha2 heq
        exact congrArg Subtype.val (W.equivFin.injective heq)
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        refine ⟨(W.equivFin.symm c).1, ?_, ?_⟩
        · simp only [Finset.mem_filter]
          exact ⟨(W.equivFin.symm c).2, hc⟩
        · show W.equivFin ⟨(W.equivFin.symm c).1, _⟩ = c
          have key : W.equivFin (W.equivFin.symm c) = c := Equiv.apply_symm_apply W.equivFin c
          convert key using 1
    rw [hcardEq]; exact h
  choose ψ hψsub hψcard using fun e => Finset.exists_subset_card_eq (hgood_card e)
  obtain ⟨T', hT'card, hT'cont⟩ := h_prop ψ hψcard
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hT'card
  refine ⟨w x, hw_card x, ?_⟩
  have hle : support_graph ψ {x} ≤ support_graph ϕ (w x) := by
    unfold support_graph
    apply SimpleGraph.fromEdgeSet_mono
    intro e he
    simp only [Set.mem_ofPred_eq] at he ⊢
    obtain ⟨h, hsub⟩ := he
    refine ⟨h, ?_⟩
    have hx : x ∈ ψ ⟨e, h⟩ := Finset.mem_of_subset hsub (Finset.mem_singleton_self x)
    have hx' : x ∈ Finset.univ.filter (fun i : Fin W.card => w i ⊆ ϕ ⟨e, h⟩) := hψsub ⟨e,h⟩ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    exact hx'
  obtain ⟨f⟩ := hT'cont
  exact ⟨⟨⟨f.toHom, fun hadj => hle (f.toHom.map_rel hadj)⟩, f.injective'⟩⟩
