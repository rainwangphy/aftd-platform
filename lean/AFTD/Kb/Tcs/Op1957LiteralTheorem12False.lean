import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Order

/-!
# op1957_literal_theorem_1_2_false

Topic: graphs   Node: 0797ef4c05f9

Provenance: erratum. Corrects: arXiv:2611.22690, Section 2 and Theorem 1.2, specialized to six vertices; the counterexample applies to the definition as written, without connectedness.

Under the definition in Section 2 of arXiv:2611.22690, which does not require connectedness, the assertion that every minimally 2-extendable graph on six vertices has minimum degree 3, 4, or 5 is false. Three disjoint edges give a counterexample of minimum degree 1 to this six-vertex case of Theorem 1.2. The standard formulation with connectedness is not refuted.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def op1957_erratum_three_pairs : SimpleGraph (Fin 6) where
  Adj u v := ((u.val, v.val) ∈ ([(0,1), (2,3), (4,5)] : List (ℕ × ℕ))) ∨
    ((v.val, u.val) ∈ ([(0,1), (2,3), (4,5)] : List (ℕ × ℕ)))
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩

instance : DecidableRel op1957_erratum_three_pairs.Adj := fun u v =>
  inferInstanceAs (Decidable
    (((u.val, v.val) ∈ ([(0,1), (2,3), (4,5)] : List (ℕ × ℕ))) ∨
     ((v.val, u.val) ∈ ([(0,1), (2,3), (4,5)] : List (ℕ × ℕ)))))

def op1957_erratum_two_pairs : op1957_erratum_three_pairs.Subgraph where
  verts := {v | v.val < 4}
  Adj u v := op1957_erratum_three_pairs.Adj u v ∧ u.val < 4 ∧ v.val < 4
  adj_sub := fun h => h.1
  edge_vert := fun h => h.2.1
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩

theorem op1957_erratum_all_perfect : (⊤ : op1957_erratum_three_pairs.Subgraph).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  simp only [SimpleGraph.Subgraph.top_adj]
  unfold ExistsUnique
  fin_cases v <;> decide

theorem op1957_erratum_two_matching : op1957_erratum_two_pairs.IsMatching := by
  intro v hv
  fin_cases v <;> simp_all [op1957_erratum_two_pairs, op1957_erratum_three_pairs] <;> unfold ExistsUnique <;> decide

theorem op1957_erratum_two_card : op1957_erratum_two_pairs.edgeSet.ncard = 2 := by
  classical
  have hs : op1957_erratum_two_pairs.edgeSet = ({s((0 : Fin 6), 1), s(2, 3)} : Set (Sym2 (Fin 6))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change op1957_erratum_two_pairs.Adj u v ↔ s(u, v) ∈ ({s((0 : Fin 6), 1), s(2, 3)} : Set (Sym2 (Fin 6)))
      fin_cases u <;> fin_cases v <;> simp [op1957_erratum_two_pairs, op1957_erratum_three_pairs, Sym2.eq, Sym2.rel_iff']
  rw [hs]
  simp

theorem op1957_erratum_min_degree : op1957_erratum_three_pairs.minDegree = 1 := by decide

theorem op1957_erratum_unique_neighbors : ∀ u v w : Fin 6, op1957_erratum_three_pairs.Adj u v → op1957_erratum_three_pairs.Adj u w → v = w := by
  decide

theorem op1957_erratum_no_perfect_after_deletion (e : Sym2 (Fin 6)) (he : e ∈ op1957_erratum_three_pairs.edgeSet) :
    ¬ ∃ P : (op1957_erratum_three_pairs.deleteEdges {e}).Subgraph, P.IsPerfectMatching := by
  induction e using Sym2.ind with
  | _ u v =>
    intro h
    obtain ⟨P,hP⟩ := h
    have huv : op1957_erratum_three_pairs.Adj u v := he
    obtain ⟨w, hw, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) u
    have hdel := P.adj_sub hw
    rw [SimpleGraph.deleteEdges_adj] at hdel
    have hwv : w = v := op1957_erratum_unique_neighbors u w v hdel.1 huv
    subst w
    exact hdel.2 (Set.mem_singleton _)

theorem op1957_erratum_three_pairs_minimal : is_minimally_k_extendable op1957_erratum_three_pairs 2 := by
  constructor
  · refine ⟨by decide, ⟨op1957_erratum_two_pairs, op1957_erratum_two_matching, op1957_erratum_two_card⟩, ?_⟩
    intro M hM hMsize
    exact ⟨⊤, op1957_erratum_all_perfect, le_top⟩
  · intro e he h
    obtain ⟨M, hM, hMsize⟩ := h.2.1
    obtain ⟨P,hP,_⟩ := h.2.2 M hM hMsize
    exact op1957_erratum_no_perfect_after_deletion e he ⟨P,hP⟩

theorem op1957_literal_theorem_1_2_false :
    ¬ (∀ G : SimpleGraph (Fin 6), ∀ [DecidableRel G.Adj],
      is_minimally_k_extendable G 2 →
      G.minDegree = 3 ∨ G.minDegree = 4 ∨ G.minDegree = 5) := by
  intro h
  have bad := h op1957_erratum_three_pairs op1957_erratum_three_pairs_minimal
  rw [op1957_erratum_min_degree] at bad
  omega
