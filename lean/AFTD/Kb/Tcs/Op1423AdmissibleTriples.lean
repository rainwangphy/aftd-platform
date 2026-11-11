import AFTD.Prelude

/-!
# op_1423_admissible_triples

Topic: combinatorics   Node: 22f65e5b17aa

Provenance: helper lemma. step towards op_1423_two_band_binomial_count

The finite set of admissible band triples (A,B,C) for the parameters F, m, g: A ranges over the subsets of [m,2m) containing m, B over the subsets of [2m,3m), C over the subsets of [3m,F), and the triple is admissible when F is in neither A+A nor A+B, every element of (A+A) ∩ [2m,3m) lies in B, every element of ((A+A) ∪ (A+B)) ∩ [3m,F) lies in C, and |A|+|B|+|C| = F-g.
-/

/-- Admissible band triples (A,B,C) for the two-band binomial count: A ⊆ [m,2m) contains m, B ⊆ [2m,3m), C ⊆ [3m,F), the closure constraints on A+A and A+B hold, and |A|+|B|+|C| = F-g. -/
noncomputable def op_1423_admissible_triples (F m g : ℕ) : Finset ((Finset ℕ × Finset ℕ) × Finset ℕ) := by
  classical
  exact ((((Finset.Ico m (2*m)).powerset.filter (fun A => m ∈ A)).product
      ((Finset.Ico (2*m) (3*m)).powerset)).product ((Finset.Ico (3*m) F).powerset)).filter
    (fun t =>
      let A : Finset ℕ := t.1.1
      let B : Finset ℕ := t.1.2
      let C : Finset ℕ := t.2
      let AA : Finset ℕ := Finset.image₂ (fun a b : ℕ => a+b) A A
      let AB : Finset ℕ := Finset.image₂ (fun a b : ℕ => a+b) A B
      let P : Finset ℕ := (AA ∪ AB).filter (fun x => 3*m ≤ x ∧ x < F)
      F ∉ AA ∧ F ∉ AB ∧ AA ∩ Finset.Ico (2*m) (3*m) ⊆ B ∧ P ⊆ C ∧
        A.card + B.card + C.card = F - g)
