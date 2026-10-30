import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleRemoveKValue

/-!
# bundle_remove_k_value_le

Topic: fair_division   Node: 62e193cbabb1

Provenance: helper lemma. arXiv:2610.34625, Lemma 3.2

Given a type of goods α with decidable equality, a valuation function v : Finset α → ℝ, a natural number k : ℕ, a bundle S : Finset α, and a sub-bundle X : Finset α satisfying X ⊆ S and X.card ≤ k, the value bundle_remove_k_value v k S is at most v (S \ X).
-/

/-- Removing any sub-bundle X of at most k goods from S leaves at least the value D^{(k)}(S). -/
theorem bundle_remove_k_value_le {α : Type*} [DecidableEq α] (v : Finset α → ℝ) (k : ℕ) (S : Finset α)
    (X : Finset α) (hX1 : X ⊆ S) (hX2 : X.card ≤ k) :
    bundle_remove_k_value v k S ≤ v (S \ X) := by
  have : Finite {X : Finset α // X ⊆ S ∧ X.card ≤ k} := by
    have h1 : {X : Finset α | X ⊆ S ∧ X.card ≤ k}.Finite := by
      have h2 : {X : Finset α | X ⊆ S}.Finite := by
        have : {X : Finset α | X ⊆ S} = (S.powerset : Set (Finset α)) := by
          ext; exact Finset.mem_powerset.symm
        rw [this]
        exact Finset.finite_toSet S.powerset
      exact h2.subset (fun Y hY => hY.1)
    exact h1.to_subtype
  have h_bdd : BddBelow (Set.range (fun (Y : {X : Finset α // X ⊆ S ∧ X.card ≤ k}) => v (S \ Y.val))) :=
    Finite.bddBelow_range _
  unfold bundle_remove_k_value
  exact ciInf_le h_bdd ⟨X, ⟨hX1, hX2⟩⟩
