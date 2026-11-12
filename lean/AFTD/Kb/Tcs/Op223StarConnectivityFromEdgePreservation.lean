import AFTD.Prelude
import AFTD.Kb.Tcs.Op223StarConnectivityOfNonleafRankStep
import AFTD.Kb.Tcs.Op223NonsustainableHasBadEdge
import AFTD.Kb.Tcs.Op223TreeAdjacentShiftNonleafCount
import AFTD.Kb.Tcs.Op223ShiftBadEdgeYieldsStep
import AFTD.Kb.Tcs.NonsustainableGtsStep
import AFTD.Kb.Tcs.IsSustainableEdge
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.IsGeneralizedTreeShift
import AFTD.Kb.Tcs.GtsGraph
import AFTD.Kb.Tcs.IsSustainableTree

/-!
# op223_star_connectivity_from_edge_preservation

Topic: graphs   Node: f222d6b8d729

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1

Assume shifting along a nonsustainable edge preserves it, shifting a branch toward the center of a nonsustainable pendant edge preserves that edge, and every vertex of a non-star tree has a non-leaf neighbor. Then every nonsustainable finite tree with at least two vertices reaches a star through nonsustainable generalized tree shifts.
-/

open SimpleGraph

theorem op223_star_connectivity_from_edge_preservation
    (halong : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (u v : Fin n),
      T.IsTree → T.Adj u v → ¬ is_sustainable_edge T s(u,v) →
        ¬ is_sustainable_edge (gts_graph T u v u) s(u,v))
    (hpend : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (u v w : Fin n),
      T.IsTree → T.Adj u w → Nat.card (T.neighborSet w) = 1 →
      ¬ is_sustainable_edge T s(u,w) → T.Adj u v →
        ¬ is_sustainable_edge (gts_graph T u v u) s(u,w))
    (hcenter : ∀ (n : ℕ), 2 ≤ n → ∀ (T : SimpleGraph (Fin n)), T.IsTree →
      ¬ Nonempty (T ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) →
      ∀ u : Fin n, ∃ v, T.Adj u v ∧ 2 ≤ Nat.card (T.neighborSet v)) :
    ∀ (n : ℕ), 2 ≤ n → ∀ (X : SimpleGraph (Fin n)), is_nonsustainable_tree X →
      ∃ K : SimpleGraph (Fin n), Nonempty (K ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) ∧
        Relation.ReflTransGen nonsustainable_gts_step X K := by
  classical
  apply op223_star_connectivity_of_nonleaf_rank_step
  intro n hn T hT hstar
  obtain ⟨a, b, hab, hbad⟩ := op223_nonsustainable_has_bad_edge T hT
  have hpos (u v : Fin n) (huv : T.Adj u v) : 0 < Nat.card (T.neighborSet u) := by
    letI : Nonempty (T.neighborSet u) := ⟨⟨v, huv⟩⟩
    exact Nat.card_pos
  have hmake (u v w : Fin n) (huv : T.Adj u v) (huw : T.Adj u w)
      (hu2 : 2 ≤ Nat.card (T.neighborSet u)) (hv2 : 2 ≤ Nat.card (T.neighborSet v))
      (hbad' : ¬ is_sustainable_edge (gts_graph T u v u) s(u,w)) :
      ∃ Y : SimpleGraph (Fin n), is_nonsustainable_tree Y ∧ nonsustainable_gts_step T Y ∧
        (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (Y.neighborSet x))).card <
          (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (T.neighborSet x))).card := by
    have hs := op223_shift_bad_edge_yields_step T hT u v w huv huw hbad'
    refine ⟨gts_graph T u v u, hs.2.1, hs, ?_⟩
    have hc := op223_tree_adjacent_shift_nonleaf_count T u v hT.1 huv hu2 hv2
    omega
  have hpendstep (u w : Fin n) (huw : T.Adj u w)
      (hw1 : Nat.card (T.neighborSet w) = 1)
      (hbadw : ¬ is_sustainable_edge T s(u,w)) :
      ∃ Y : SimpleGraph (Fin n), is_nonsustainable_tree Y ∧ nonsustainable_gts_step T Y ∧
        (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (Y.neighborSet x))).card <
          (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (T.neighborSet x))).card := by
    obtain ⟨v, huv, hv2⟩ := hcenter n hn T hT.1 hstar u
    have hwv : w ≠ v := by
      intro h
      subst v
      omega
    have hu2 : 2 ≤ Nat.card (T.neighborSet u) := by
      have hp : 1 < Fintype.card (T.neighborSet u) := by
        apply Fintype.one_lt_card_iff.mpr
        refine ⟨⟨w, huw⟩, ⟨v, huv⟩, ?_⟩
        intro hh
        exact hwv (congrArg Subtype.val hh)
      have hp' : 1 < Nat.card (T.neighborSet u) := by rw [Nat.card_eq_fintype_card]; exact hp
      omega
    exact hmake u v w huv huw hu2 hv2 (hpend n T u v w hT.1 huw hw1 hbadw huv)
  by_cases ha : 2 ≤ Nat.card (T.neighborSet a)
  · by_cases hb : 2 ≤ Nat.card (T.neighborSet b)
    · exact hmake a b b hab hab ha hb (halong n T a b hT.1 hab hbad)
    · have hb1 : Nat.card (T.neighborSet b) = 1 := by have := hpos b a hab.symm; omega
      exact hpendstep a b hab hb1 hbad
  · have ha1 : Nat.card (T.neighborSet a) = 1 := by have := hpos a b hab; omega
    have hbad' : ¬ is_sustainable_edge T s(b,a) := by
      rw [Sym2.eq_swap]
      exact hbad
    exact hpendstep b a hab.symm ha1 hbad'
