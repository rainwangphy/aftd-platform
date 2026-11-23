import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# higher_bruhat_right_coord

Topic: combinatorics   Node: 744800373895

Provenance: formalization of a published result. Source: arXiv:2611.17465 Definition 4

For a subset Q ⊆ {0, ..., n-1} and a family X, the right coordinate rho_Q(X) is the list of boolean values 1_{Q ∪ {x} ∈ X} for elements x ∉ Q satisfying x > min Q, ordered in increasing order, or the empty list if Q is empty.
-/

/-- The long right coordinate binary word rho_Q(X) for Q in (Fin n choose k). -/
def higher_bruhat_right_coord (n : ℕ) (Q : Finset (Fin n)) (X : Finset (Finset (Fin n))) : List Bool :=
  if hQ : Q.Nonempty then
    let D := (Finset.univ.filter (fun x : Fin n => x ∉ Q ∧ Q.min' hQ < x)).sort (· ≤ ·)
    D.map (fun x => decide (insert x Q ∈ X))
  else []
