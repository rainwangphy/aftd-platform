import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasiblePacking
import AFTD.Kb.Tcs.IncidentEdgeMultiset

/-!
# op_1627_realizable_parameters_seven_five_three_two

Topic: combinatorics   Node: 7bc9252aa772

Provenance: original. Related work: arXiv:2611.15376 Sec. 7, after Question 7.2

There exists an edge-coloring ϕ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 7) assigning a 5-element subset of Fin 7 to each edge of the complete graph on Fin 5 such that for every vertex v : Fin 5, the multiset of incident edge labels incident_edge_multiset ϕ v is a feasible packing for parameters (7, 5, 3, 2).
-/

instance op_1627_realizable_parameters_seven_five_three_two_decidable_feasible_packing
    (r s t h : ℕ) (M : Multiset (Finset (Fin r))) : Decidable (is_feasible_packing r s t h M) := by
  unfold is_feasible_packing
  infer_instance

def op_1627_realizable_parameters_seven_five_three_two_color_pair (u v : ℕ) : Finset (Fin 7) :=
  match min u v, max u v with
  | 0, 1 => {0, 2, 3, 5, 6}
  | 0, 2 => {0, 1, 2, 5, 6}
  | 0, 3 => {1, 3, 4, 5, 6}
  | 0, 4 => {0, 1, 3, 4, 5}
  | 1, 2 => {0, 1, 2, 3, 4}
  | 1, 3 => {0, 1, 4, 5, 6}
  | 1, 4 => {1, 2, 3, 5, 6}
  | 2, 3 => {0, 2, 3, 4, 5}
  | 2, 4 => {0, 1, 4, 5, 6}
  | 3, 4 => {0, 2, 3, 4, 6}
  | _, _ => {0, 1, 2, 3, 4}

lemma op_1627_realizable_parameters_seven_five_three_two_color_pair_symm (u v : Fin 5) :
    op_1627_realizable_parameters_seven_five_three_two_color_pair u.val v.val =
    op_1627_realizable_parameters_seven_five_three_two_color_pair v.val u.val := by
  dsimp [op_1627_realizable_parameters_seven_five_three_two_color_pair]
  rw [min_comm, max_comm]

def op_1627_realizable_parameters_seven_five_three_two_phi :
    (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 7) :=
  fun e => Sym2.lift
    ⟨fun u v => op_1627_realizable_parameters_seven_five_three_two_color_pair u.val v.val,
     op_1627_realizable_parameters_seven_five_three_two_color_pair_symm⟩ e.val

/-- For parameters (r, s, t, h) = (7, 5, 3, 2) where n = 3 and D = 4, there exists a (7, 5)-set-coloring of K_5 such that at every vertex v, the multiset of incident edge labels is a feasible packing. -/
theorem op_1627_realizable_parameters_seven_five_three_two :
    ∃ ϕ : (⊤ : SimpleGraph (Fin 5)).edgeSet → Finset (Fin 7),
      (∀ e, (ϕ e).card = 5) ∧
      ∀ v : Fin 5, is_feasible_packing 7 5 3 2 (incident_edge_multiset ϕ v) := ⟨op_1627_realizable_parameters_seven_five_three_two_phi, by decide⟩
