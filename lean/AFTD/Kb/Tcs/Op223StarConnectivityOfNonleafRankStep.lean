import AFTD.Prelude
import AFTD.Kb.Tcs.IsNonsustainableTree
import AFTD.Kb.Tcs.NonsustainableGtsStep

/-!
# op223_star_connectivity_of_nonleaf_rank_step

Topic: graphs   Node: a3adad81fce1

Provenance: helper lemma. step towards op223_gts_poset_connectivity

If every non-sustainable tree X on Fin n (n ≥ 2) that is not a star has a non-sustainable generalized-tree-shift successor Y with strictly fewer non-leaf vertices, then every non-sustainable tree on Fin n reaches a star by a sequence of non-sustainable generalized tree shifts.
-/

open SimpleGraph

/-- Reduction of the non-sustainable half to a one-step non-leaf-count drop. -/
theorem op223_star_connectivity_of_nonleaf_rank_step
    (hstep : ∀ (n : ℕ) (_hn : 2 ≤ n) (X : SimpleGraph (Fin n)), is_nonsustainable_tree X →
      ¬ Nonempty (X ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) →
      ∃ Y : SimpleGraph (Fin n), is_nonsustainable_tree Y ∧ nonsustainable_gts_step X Y ∧
        (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (Y.neighborSet x))).card <
          (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (X.neighborSet x))).card) :
    ∀ (n : ℕ) (_hn : 2 ≤ n) (X : SimpleGraph (Fin n)), is_nonsustainable_tree X →
      ∃ K : SimpleGraph (Fin n), Nonempty (K ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) ∧
        Relation.ReflTransGen nonsustainable_gts_step X K := by
  classical
  intro n hn
  let rank (X : SimpleGraph (Fin n)) :=
    (Finset.univ.filter (fun x : Fin n => 1 < Nat.card (X.neighborSet x))).card
  have go : ∀ k : ℕ, ∀ X : SimpleGraph (Fin n), is_nonsustainable_tree X → rank X = k →
      ∃ K : SimpleGraph (Fin n), Nonempty (K ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1))) ∧
        Relation.ReflTransGen nonsustainable_gts_step X K := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro X hX hRank
      by_cases hstar : Nonempty (X ≃g completeBipartiteGraph (Fin 1) (Fin (n - 1)))
      · exact ⟨X, hstar, Relation.ReflTransGen.refl⟩
      · obtain ⟨Y, hY, hXY, hlt⟩ := hstep n hn X hX hstar
        have hsmall : rank Y < k := by simpa [rank, ← hRank] using hlt
        obtain ⟨K, hK, hYK⟩ := ih (rank Y) hsmall Y hY rfl
        exact ⟨K, hK, Relation.ReflTransGen.head hXY hYK⟩
  intro X hX
  exact go (rank X) X hX rfl
