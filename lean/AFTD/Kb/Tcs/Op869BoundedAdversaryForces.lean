import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869PredecessorPostdegree

/-!
# op869_bounded_adversary_forces

Topic: online_algorithms   Node: f6fa68e74113

Provenance: helper lemma. arXiv:2610.41516, Section 2.2, post-degree controlled adaptive t-fold coloring simulation.

The bounded t-fold adversary game is the t-fold game where, after each move, every vertex has post-degree at most D.
-/

def op869_bounded_adversary_forces {n : ℕ} (k t K D : ℕ) :
    ℕ → ℕ → (Fin n → Finset (Fin n)) → (Fin n → Finset ℕ) → Prop
  | 0, _, _, _ => False
  | fuel + 1, i, P, C =>
    if hi : i < n then
      ∃ S : Finset (Fin n), (∀ a ∈ S, a.val < i) ∧
        let v : Fin n := ⟨i, hi⟩
        let P' := Function.update P v S
        (op869_graph_from_predecessors P').Colorable k ∧
        (∀ a, op869_predecessor_postdegree P' a ≤ D) ∧
        ∀ c : Finset ℕ, c.card = t → (∀ a ∈ S, Disjoint (C a) c) →
          let C' := Function.update C v c
          K ≤ ((Finset.univ.filter (fun a : Fin n => a.val ≤ i)).biUnion C').card ∨
            op869_bounded_adversary_forces k t K D fuel (i + 1) P' C'
    else False
