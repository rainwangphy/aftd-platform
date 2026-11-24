import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidCircuitMonoOfFundCircuitMonoOfFiniteSdiff
import AFTD.Kb.Tcs.MatroidConnected

/-!
# not_matroid_connected_of_fund_circuit_separated_finite

Topic: algorithms   Node: 543691737d23

Provenance: helper lemma. step towards not_matroid_connected_of_fund_circuit_separated

If M is a matroid with finite ground set, B is a base, and A is a non-empty proper subset of B such that every e in E \ B whose fundamental circuit meets A has its fundamental circuit contained in insert e A, then M is not connected.
-/

/-- A non-empty proper subset A of a base B whose separated fundamental circuits stay inside insert e A certifies disconnection, on a finite ground set. -/
theorem not_matroid_connected_of_fund_circuit_separated_finite {α : Type*} (M : Matroid α) {B : Set α} (hE : M.E.Finite) (hB : M.IsBase B) {A : Set α} (hAne : A.Nonempty) (hAB : A ⊂ B) (hsep : ∀ e ∈ M.E \ B, (M.fundCircuit e B ∩ A).Nonempty → M.fundCircuit e B ⊆ insert e A) : ¬ matroid_connected M := by
  intro hconn
  set S : Set α := A ∪ {x : α | x ∈ M.E \ B ∧ (M.fundCircuit x B ∩ A).Nonempty} with hS
  have hmono : ∀ e ∈ M.E \ B, M.fundCircuit e B ⊆ S ∨ Disjoint (M.fundCircuit e B) S := by
    intro e he
    by_cases hne : (M.fundCircuit e B ∩ A).Nonempty
    · left
      intro x hx
      have hsub := hsep e he hne hx
      rw [hS]
      rcases hsub with rfl | hxA
      · exact Or.inr ⟨he, hne⟩
      · exact Or.inl hxA
    · right
      rw [Set.disjoint_left]
      intro x hx hxS
      rw [hS] at hxS
      have hsub := M.fundCircuit_subset_insert e B hx
      rcases hxS with hxA | ⟨hxEB, hne'⟩
      · exact hne ⟨x, hx, hxA⟩
      · rcases hsub with rfl | hxB
        · exact hne hne'
        · exact hxEB.2 hxB
  obtain ⟨a, haA⟩ := hAne
  obtain ⟨b, hbB, hbA⟩ := Set.exists_of_ssubset hAB
  have haE : a ∈ M.E := hB.subset_ground (hAB.subset haA)
  have hbE : b ∈ M.E := hB.subset_ground hbB
  have hne_ab : a ≠ b := by intro h; exact hbA (h ▸ haA)
  obtain h | ⟨C, hC, haC, hbC⟩ := hconn a haE b hbE
  · exact hne_ab h
  · have hfin : (C \ B).Finite := (hE.subset hC.subset_ground).sdiff
    have hCS := matroid_circuit_mono_of_fundCircuit_mono_of_finite_sdiff M hB hmono C hC hfin
    have haS : a ∈ S := by rw [hS]; exact Or.inl haA
    rcases hCS with hCS | hdisj
    · have hbS : b ∈ S := hCS hbC
      rw [hS] at hbS
      rcases hbS with hbA' | ⟨hbEB, _⟩
      · exact hbA hbA'
      · exact hbEB.2 hbB
    · rw [Set.disjoint_left] at hdisj
      exact hdisj haC haS
