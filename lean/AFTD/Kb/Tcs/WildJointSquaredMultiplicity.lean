import AFTD.Prelude

/-!
# wild_joint_squared_multiplicity

Topic: graphs   Node: 961ed5592899

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Q: one quarter of the ordered equal-support count, i.e. the number of ordered pairs of witnesses (ordered vertex pairs x!=y) whose support sets coincide, divided by 4. Equals sum_T mu(T)^2 for symmetric A.
-/

/-- Q = (1/4) * ordered equal-support count = sum_T mu(T)^2. -/
noncomputable def wild_joint_squared_multiplicity (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) : ℝ := (1/4) * ((Finset.univ.filter (fun pq : (Fin (3*q) × Fin (3*q)) × (Fin (3*q) × Fin (3*q)) => pq.1.1 ≠ pq.1.2 ∧ pq.2.1 ≠ pq.2.2 ∧ ({pq.1.1, pq.1.2, A pq.1.1 pq.1.2} : Finset (Fin (3*q))) = {pq.2.1, pq.2.2, A pq.2.1 pq.2.2})).card : ℝ)
