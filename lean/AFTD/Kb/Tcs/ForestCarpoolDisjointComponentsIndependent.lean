import AFTD.Prelude
import AFTD.Kb.Tcs.ForestCarpoolFinalDiscrepancy
import AFTD.Kb.Tcs.CarpoolForestEdgeSequence
import AFTD.Kb.Tcs.ForestCarpoolAppendEdgeDisconnected
import AFTD.Kb.Tcs.ForestCarpoolComponentCoinLocality
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# forest_carpool_disjoint_components_independent

Topic: online_algorithms   Node: 483977498b20

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

If appending the edge u-v to the given prefix yields a forest, then under uniformly random prefix coins the two endpoint final discrepancies are independent, expressed as exact joint and marginal counts.
-/

theorem forest_carpool_disjoint_components_independent (n : ℕ)
    (edges : List (Fin n × Fin n)) (u v : Fin n)
    (hf : CarpoolForestEdgeSequence n (edges ++ [(u, v)])) (a b : ℤ) :
  (Finset.univ.filter (fun r : Fin edges.length → Bool =>
    forest_carpool_final_discrepancy n edges r u = a ∧
    forest_carpool_final_discrepancy n edges r v = b)).card * 2 ^ edges.length =
  (Finset.univ.filter (fun r : Fin edges.length → Bool =>
    forest_carpool_final_discrepancy n edges r u = a)).card *
  (Finset.univ.filter (fun r : Fin edges.length → Bool =>
    forest_carpool_final_discrepancy n edges r v = b)).card := by
  classical
  have huv := forest_carpool_append_edge_disconnected n edges u v hf
  set Γ := SimpleGraph.fromEdgeSet {s(e.1, e.2) | e ∈ edges}
  set P : (Fin edges.length → Bool) → Prop := fun r => forest_carpool_final_discrepancy n edges r u = a
  set Q : (Fin edges.length → Bool) → Prop := fun r => forest_carpool_final_discrepancy n edges r v = b
  let mix : (Fin edges.length → Bool) → (Fin edges.length → Bool) → (Fin edges.length → Bool) :=
    fun r s i => if Γ.Reachable u (edges.get i).1 then r i else s i
  have hP : ∀ r s, P (mix r s) ↔ P r := by
    intro r s
    simp only [P]
    rw [forest_carpool_component_coin_locality n edges u (mix r s) r]
    intro i hi
    have hi' : Γ.Reachable u (edges.get i).1 := hi
    simp only [mix, if_pos hi']
  have hQ : ∀ r s, Q (mix r s) ↔ Q s := by
    intro r s
    simp only [Q]
    rw [forest_carpool_component_coin_locality n edges v (mix r s) s]
    intro i hi
    have : ¬ Γ.Reachable u (edges.get i).1 := fun h => huv (h.trans hi.symm)
    simp only [mix, if_neg this]
  have hmix : ∀ r s, mix (mix r s) (mix s r) = r := by
    intro r s; funext i; simp only [mix]; split_ifs <;> rfl
  let φ : (Fin edges.length → Bool) × (Fin edges.length → Bool) →
      (Fin edges.length → Bool) × (Fin edges.length → Bool) := fun p => (mix p.1 p.2, mix p.2 p.1)
  have hφ : ∀ p, φ (φ p) = p := by
    rintro ⟨r, s⟩; simp only [φ, hmix]
  have h1 : ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : (Fin edges.length → Bool) × (Fin edges.length → Bool) => P p.1 ∧ Q p.2)).card =
      ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : (Fin edges.length → Bool) × (Fin edges.length → Bool) => P p.1 ∧ Q p.1)).card := by
    refine Finset.card_nbij' φ φ ?_ ?_ (fun p _ => hφ p) (fun p _ => hφ p)
    · rintro ⟨r, s⟩ hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hp ⊢
      exact ⟨(hP r s).mpr hp.1, (hQ r s).mpr hp.2⟩
    · rintro ⟨r, s⟩ hp
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hp ⊢
      exact ⟨(hP r s).mpr hp.1, (hQ s r).mpr hp.2⟩
  have h2 : ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : (Fin edges.length → Bool) × (Fin edges.length → Bool) => P p.1 ∧ Q p.2)) =
      (Finset.univ.filter P) ×ˢ (Finset.univ.filter Q) := by
    ext ⟨r, s⟩; simp
  have h3 : ((Finset.univ ×ˢ Finset.univ).filter
      (fun p : (Fin edges.length → Bool) × (Fin edges.length → Bool) => P p.1 ∧ Q p.1)) =
      (Finset.univ.filter (fun r => P r ∧ Q r)) ×ˢ Finset.univ := by
    ext ⟨r, s⟩; simp
  have h4 := h1
  rw [h2, h3, Finset.card_product, Finset.card_product, Finset.card_univ] at h4
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h4
  exact h4.symm
