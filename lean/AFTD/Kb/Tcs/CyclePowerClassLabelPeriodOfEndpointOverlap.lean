import AFTD.Prelude

/-!
# cycle_power_class_label_period_of_endpoint_overlap

Topic: combinatorics   Node: 78346c7d5c73

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

If a shifted class meets every other class through the old endpoint, complete palettes and label separation force the shifted class to retain its label.
-/

open Finset

theorem cycle_power_class_label_period_of_endpoint_overlap
    {α : Type*} (D : ℤ) (S : ℤ → ℤ → Prop) (σ : ℤ → α)
    (hslots : ∀ (v : ℤ) (a : α), ∃ p, S p v ∧ σ p = a)
    (hsep : ∀ (p q u : ℤ), S p u → S q u → σ p = σ q → p = q)
    (hbefore : ∀ p, ¬ S (p + D) (p + D - 1))
    (hoverlap : ∀ p q, q ≠ p → S q (p + D - 1) →
      ∃ u, S q u ∧ S (p + D) u) :
    ∀ p, σ (p + D) = σ p := by
  intro p
  obtain ⟨q, hq, hσ⟩ := hslots (p + D - 1) (σ (p + D))
  by_cases hqp : q = p
  · subst q
    exact hσ.symm
  obtain ⟨u, hqu, hnew⟩ := hoverlap p q hqp hq
  have heq := hsep q (p + D) u hqu hnew hσ
  rw [heq] at hq
  exact False.elim (hbefore p hq)
