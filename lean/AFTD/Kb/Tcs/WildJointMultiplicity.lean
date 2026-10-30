import AFTD.Prelude

/-!
# wild_joint_multiplicity

Topic: graphs   Node: 0b2d7e2be8ec

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

mu(T): the number of unordered vertex pairs {x,y} (x != y) whose witness support {x,y,A x y} equals T. Equals half the ordered count because A is symmetric; equals #{i in T : T contains a colour-i edge} when |T|=3.
-/

/-- Multiplicity mu(T) of the witness support T (unordered-pair count). -/
noncomputable def wild_joint_multiplicity (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (T : Finset (Fin (3*q))) : ℕ := (Finset.univ.filter (fun p : Fin (3*q) × Fin (3*q) => p.1 ≠ p.2 ∧ ({p.1, p.2, A p.1 p.2} : Finset (Fin (3*q))) = T)).card / 2
