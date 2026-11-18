import AFTD.Prelude

/-!
# op861_five_tail_strong_pair_counterexample

Topic: graphs   Node: a14dbc4d238a

Provenance: helper lemma. Finite counterexample computed in experiment 30755.

A five-vertex complete three-uniform single-tail hypergraph strongly dominates every pair, disproving a proposed counting obstruction for single-tail systems.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def op861_five_tail (X : Finset (Fin 5)) : Fin 5 :=
  if X = {0,1,2} then 1
  else if X = {0,1,3} then 3
  else if X = {0,1,4} then 0
  else if X = {0,2,3} then 2
  else if X = {0,2,4} then 2
  else if X = {0,3,4} then 0
  else if X = {1,2,3} then 3
  else if X = {1,2,4} then 1
  else 4

theorem op861_five_tail_strong_pair_counterexample :
    (∀ X, X.card = 3 → op861_five_tail X ∈ X) ∧
    (∀ R, R.card = 2 → ∃ v, v ∉ R ∧ op861_five_tail (insert v R) = v) ∧
    ¬ Nat.choose 4 2 ≤ 3 * Nat.choose 2 2 := by
  constructor
  · decide
  · constructor <;> decide
