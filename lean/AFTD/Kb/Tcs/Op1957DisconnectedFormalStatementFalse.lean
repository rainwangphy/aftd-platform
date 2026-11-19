import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Order

/-!
# op1957_disconnected_formal_statement_false

Topic: graphs   Node: bd076a256431

Provenance: helper lemma. OP-1957: refutation of the incomplete disconnected formalization; the standard connected formulation is a distinct open statement.

The formal minimum-degree statement that omits connectedness is false: for k = 4, the graph consisting of five disjoint edges is minimally k-extendable under the repository definition and has minimum degree one. This concerns the disconnected formalization, while the connected conjecture remains open.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def op1957_1050_five_pairs : SimpleGraph (Fin 10) where
  Adj u v := ((u.val, v.val) ∈ ([(0,1), (2,3), (4,5), (6,7), (8,9)] : List (ℕ × ℕ))) ∨
    ((v.val, u.val) ∈ ([(0,1), (2,3), (4,5), (6,7), (8,9)] : List (ℕ × ℕ)))
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨by intro u; fin_cases u <;> decide⟩

instance : DecidableRel op1957_1050_five_pairs.Adj := fun u v =>
  inferInstanceAs (Decidable
    (((u.val, v.val) ∈ ([(0,1), (2,3), (4,5), (6,7), (8,9)] : List (ℕ × ℕ))) ∨
     ((v.val, u.val) ∈ ([(0,1), (2,3), (4,5), (6,7), (8,9)] : List (ℕ × ℕ)))))

def op1957_1050_four_pairs : op1957_1050_five_pairs.Subgraph where
  verts := {v | v.val < 8}
  Adj u v := op1957_1050_five_pairs.Adj u v ∧ u.val < 8 ∧ v.val < 8
  adj_sub := fun h => h.1
  edge_vert := fun h => h.2.1
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩

theorem op1957_1050_all_perfect : (⊤ : op1957_1050_five_pairs.Subgraph).IsPerfectMatching := by
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  simp only [SimpleGraph.Subgraph.top_adj]
  unfold ExistsUnique
  fin_cases v <;> decide

theorem op1957_1050_four_matching : op1957_1050_four_pairs.IsMatching := by
  intro v hv
  fin_cases v <;> simp_all [op1957_1050_four_pairs, op1957_1050_five_pairs] <;> unfold ExistsUnique <;> decide

theorem op1957_1050_four_card : op1957_1050_four_pairs.edgeSet.ncard = 4 := by
  classical
  have hs : op1957_1050_four_pairs.edgeSet = ({s((0 : Fin 10), 1), s(2, 3), s(4, 5), s(6, 7)} : Set (Sym2 (Fin 10))) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change op1957_1050_four_pairs.Adj u v ↔ s(u, v) ∈ ({s((0 : Fin 10), 1), s(2, 3), s(4, 5), s(6, 7)} : Set (Sym2 (Fin 10)))
      fin_cases u <;> fin_cases v <;> simp [op1957_1050_four_pairs, op1957_1050_five_pairs, Sym2.eq, Sym2.rel_iff']
  rw [hs]
  simp

theorem op1957_1050_min_degree : op1957_1050_five_pairs.minDegree = 1 := by decide

theorem op1957_1050_unique_neighbors : ∀ u v w : Fin 10, op1957_1050_five_pairs.Adj u v → op1957_1050_five_pairs.Adj u w → v = w := by
  decide

theorem op1957_1050_no_perfect_after_deletion (e : Sym2 (Fin 10)) (he : e ∈ op1957_1050_five_pairs.edgeSet) :
    ¬ ∃ P : (op1957_1050_five_pairs.deleteEdges {e}).Subgraph, P.IsPerfectMatching := by
  induction e using Sym2.ind with
  | _ u v =>
    intro h
    obtain ⟨P,hP⟩ := h
    have huv : op1957_1050_five_pairs.Adj u v := he
    obtain ⟨w, hw, _⟩ := (SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP) u
    have hdel := P.adj_sub hw
    rw [SimpleGraph.deleteEdges_adj] at hdel
    have hwv : w = v := op1957_1050_unique_neighbors u w v hdel.1 huv
    subst w
    exact hdel.2 (Set.mem_singleton _)

theorem op1957_1050_five_pairs_minimal : is_minimally_k_extendable op1957_1050_five_pairs 4 := by
  constructor
  · refine ⟨by decide, ⟨op1957_1050_four_pairs, op1957_1050_four_matching, op1957_1050_four_card⟩, ?_⟩
    intro M hM hMsize
    exact ⟨⊤, op1957_1050_all_perfect, le_top⟩
  · intro e he h
    obtain ⟨M, hM, hMsize⟩ := h.2.1
    obtain ⟨P,hP,_⟩ := h.2.2 M hM hMsize
    exact op1957_1050_no_perfect_after_deletion e he ⟨P,hP⟩

theorem op1957_disconnected_formal_statement_false :
    ¬ (∀ k : ℕ, 4 ≤ k → ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      is_minimally_k_extendable G k → n ≤ 4 * k →
      G.minDegree = k + 1 ∨ G.minDegree = 2 * k ∨ G.minDegree = 2 * k + 1) := by
  intro h
  have bad := h 4 (by decide) 10 op1957_1050_five_pairs op1957_1050_five_pairs_minimal (by decide)
  rw [op1957_1050_min_degree] at bad
  omega
