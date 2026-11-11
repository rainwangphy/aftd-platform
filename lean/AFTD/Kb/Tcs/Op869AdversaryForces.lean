import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GraphFromPredecessors

/-!
# op869_adversary_forces

Topic: online_algorithms   Node: f190792ed609

Provenance: helper lemma. arXiv:2610.41516, Sections 1 and 2; formal infrastructure for the adaptive online-coloring construction.

A bounded t-fold online-coloring adversary position is winning if, before the move budget or vertex indices run out, the adversary can choose earlier neighbors while maintaining a k-colorable graph and force at least K distinct colors against every legal t-element response; the recursive state also records previously assigned color sets.
-/

def op869_adversary_forces {n : ℕ} (k t K : ℕ) :
    ℕ → ℕ → (Fin n → Finset (Fin n)) → (Fin n → Finset ℕ) → Prop
  | 0, _, _, _ => False
  | fuel + 1, i, P, C =>
    if hi : i < n then
      ∃ S : Finset (Fin n), (∀ a ∈ S, a.val < i) ∧
        let v : Fin n := ⟨i, hi⟩
        let P' := Function.update P v S
        (op869_graph_from_predecessors P').Colorable k ∧
        ∀ c : Finset ℕ, c.card = t → (∀ a ∈ S, Disjoint (C a) c) →
          let C' := Function.update C v c
          K ≤ ((Finset.univ.filter (fun a : Fin n => a.val ≤ i)).biUnion C').card ∨
            op869_adversary_forces k t K fuel (i + 1) P' C'
    else False
