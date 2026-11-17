import AFTD.Prelude
import AFTD.Kb.Tcs.Op869EqualFoldSimulation
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces

/-!
# op869_strict_fold_suffices

Topic: online_algorithms   Node: dbc81e1357e1

Provenance: helper lemma. Boundary-case reduction for the fold simulation of arXiv:2610.41516 Lemma 2.5.

For a fixed positive simulation constant C, the strict fold-decrease case implies the full fold simulation including equality.
-/

/-- Reduce fold simulation to strictly decreasing folds. -/
theorem op869_strict_fold_suffices (C : ℕ) (hC : 1 ≤ C)
    (hstrict : ∀ n q t K D : ℕ, 1 ≤ t → t < q → q ≤ K → 1 ≤ D →
      op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) →
      ∀ n' D' : ℕ, C*K^2*q*n*D*2^(C*((q+t-1)/t)) ≤ n' →
        C*K^2*q*D*2^(C*((q+t-1)/t)) ≤ D' →
        op869_bounded_adversary_forces 3 t K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅)) :
    ∀ n q t K D : ℕ, 1 ≤ t → t ≤ q → q ≤ K → 1 ≤ D →
      op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) →
      ∀ n' D' : ℕ, C*K^2*q*n*D*2^(C*((q+t-1)/t)) ≤ n' →
        C*K^2*q*D*2^(C*((q+t-1)/t)) ≤ D' →
        op869_bounded_adversary_forces 3 t K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅) := by
  intro n q t K D ht htq hqK hD hgame n' D' hn hD'
  rcases lt_or_eq_of_le htq with hlt | heq
  · exact hstrict n q t K D ht hlt hqK hD hgame n' D' hn hD'
  · subst t
    exact op869_equal_fold_simulation C n q K D n' D' hC ht hqK hD hgame hn hD'
