import AFTD.Prelude
import AFTD.Kb.Tcs.IsSustainableTree
import AFTD.Kb.Tcs.SustainableGtsStep

/-!
# op223_path_connectivity_of_leaf_rank_step

Topic: graphs   Node: 026a94de4cd0

Provenance: helper lemma. step towards op223_gts_poset_connectivity

If every sustainable tree X on Fin n (n ≥ 1) that is not a path has a sustainable generalized-tree-shift predecessor Y with strictly fewer leaves, then every sustainable tree on Fin n is reachable from a path by a sequence of sustainable generalized tree shifts.
-/

open SimpleGraph

/-- Reduction of the sustainable half to a one-step leaf-count drop. -/
theorem op223_path_connectivity_of_leaf_rank_step
    (hstep : ∀ (n : ℕ) (_hn : 1 ≤ n) (X : SimpleGraph (Fin n)), is_sustainable_tree X →
      ¬ Nonempty (X ≃g SimpleGraph.pathGraph n) →
      ∃ Y : SimpleGraph (Fin n), is_sustainable_tree Y ∧ sustainable_gts_step Y X ∧
        (Finset.univ.filter (fun x : Fin n => Nat.card (Y.neighborSet x) = 1)).card <
          (Finset.univ.filter (fun x : Fin n => Nat.card (X.neighborSet x) = 1)).card) :
    ∀ (n : ℕ) (_hn : 1 ≤ n) (X : SimpleGraph (Fin n)), is_sustainable_tree X →
      ∃ P : SimpleGraph (Fin n), Nonempty (P ≃g SimpleGraph.pathGraph n) ∧
        Relation.ReflTransGen sustainable_gts_step P X := by
  classical
  intro n hn
  let rank (X : SimpleGraph (Fin n)) :=
    (Finset.univ.filter (fun x : Fin n => Nat.card (X.neighborSet x) = 1)).card
  have go : ∀ k : ℕ, ∀ X : SimpleGraph (Fin n), is_sustainable_tree X → rank X = k →
      ∃ K : SimpleGraph (Fin n), Nonempty (K ≃g SimpleGraph.pathGraph n) ∧
        Relation.ReflTransGen sustainable_gts_step K X := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro X hX hRank
      by_cases hstar : Nonempty (X ≃g SimpleGraph.pathGraph n)
      · exact ⟨X, hstar, Relation.ReflTransGen.refl⟩
      · obtain ⟨Y, hY, hXY, hlt⟩ := hstep n hn X hX hstar
        have hsmall : rank Y < k := by simpa [rank, ← hRank] using hlt
        obtain ⟨K, hK, hYK⟩ := ih (rank Y) hsmall Y hY rfl
        exact ⟨K, hK, Relation.ReflTransGen.tail hYK hXY⟩
  intro X hX
  exact go (rank X) X hX rfl
