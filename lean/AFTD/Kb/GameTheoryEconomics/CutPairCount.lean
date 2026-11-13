import AFTD.Prelude

/-!
# cutPairCount

Topic: general_equilibrium   Node: 23c33f9c5ab7

Provenance: helper lemma. step towards two_thirds_convex_random_marginal_core_logarithmic_lower_bound

The number of ordered cross-group pairs (a,b) cut by the ordered pair of coalitions (A,B): a lies in A\B and b in B\A, or vice versa.
-/

/-- Auxiliary cardinality of ordered cross-group pairs cut between A and B; it is the crossPairCount supermodularity defect. -/
noncomputable def cutPairCount {n : ℕ} (A B : Finset (Fin n)) : ℕ := (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1.val / 2 ≠ p.2.val / 2 ∧
    ((p.1 ∈ A \ B ∧ p.2 ∈ B \ A) ∨ (p.1 ∈ B \ A ∧ p.2 ∈ A \ B)))).card
