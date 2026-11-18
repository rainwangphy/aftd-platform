import AFTD.Prelude

/-!
# op861_acyclic_five_tail_rule_counterexample

Topic: graphs   Node: 5781835577d3

Provenance: helper lemma. Counterexample found in experiment 30725 to a proposed extension of the four-vertex rule in https://korandi.org/docs/domination-3tournaments.pdf.

For an explicit acyclic five-vertex directed graph, the rule that chooses the least starting vertex of a longest directed path in each triple uses all five vertices as tails. Thus a natural five-vertex extension of the known four-vertex repeated-tail rule is false.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def op861_dag5_edge (v w : Fin 5) : Prop :=
  (v = 2 ∧ w = 4) ∨ (v = 3 ∧ w = 4) ∨ (v = 4 ∧ w = 1)

instance : DecidableRel op861_dag5_edge := fun v w => by
  unfold op861_dag5_edge
  infer_instance

def op861_dag5_rank : Fin 5 → ℕ := ![0, 3, 0, 0, 1]

def op861_dag5_score (X : Finset (Fin 5)) (v : Fin 5) : ℕ :=
  if ∃ u ∈ X, ∃ w ∈ X, op861_dag5_edge v u ∧ op861_dag5_edge u w then 2
  else if ∃ u ∈ X, op861_dag5_edge v u then 1 else 0

def op861_dag5_tail (X : Finset (Fin 5)) : Fin 5 :=
  if X = {0,1,4} then 4
  else if X = {0,2,4} then 2
  else if X = {0,3,4} then 3
  else if X = {1,2,3} then 1
  else if X = {1,2,4} then 2
  else if X = {1,3,4} then 3
  else if X = {2,3,4} then 2
  else 0

theorem op861_acyclic_five_tail_rule_counterexample :
    (∀ v w, op861_dag5_edge v w → op861_dag5_rank v < op861_dag5_rank w) ∧
    (∀ X : Finset (Fin 5), X.card = 3 →
      op861_dag5_tail X ∈ X ∧
      (∀ v ∈ X, op861_dag5_score X v ≤ op861_dag5_score X (op861_dag5_tail X)) ∧
      (∀ v ∈ X, op861_dag5_score X v = op861_dag5_score X (op861_dag5_tail X) →
        op861_dag5_tail X ≤ v)) ∧
    (∀ v : Fin 5, ∃ X : Finset (Fin 5), X.card = 3 ∧ op861_dag5_tail X = v) := by
  constructor
  · decide
  · constructor <;> decide
