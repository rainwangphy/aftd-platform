import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# maxcut_one_sum_indecomposable_delete_preconnected

Topic: equilibria   Node: c5aa409c9d5d

Provenance: helper lemma. Structural reduction for OP-85, the unweighted Max-k-Cut strong-equilibrium existence problem in arXiv:2610.04948, Section 4.

If a finite graph has no nontrivial separation into two induced pieces meeting at one vertex, then after deleting any vertex every two remaining vertices are connected by a walk. The empty and singleton deletions are included.
-/

open Finset

theorem maxcut_one_sum_indecomposable_delete_preconnected
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hind : ∀ (A B : Finset V) (o : V), A ∪ B = Finset.univ → A ∩ B = {o} →
        (∀ v ∈ A, v ∉ B → ∀ w ∈ B, w ∉ A → ¬ G.Adj v w) →
        A = Finset.univ ∨ B = Finset.univ) :
    ∀ o : V, (G.induce ({o}ᶜ : Set V)).Preconnected := by
  classical
  intro o
  by_contra hf
  change ¬ ∀ u v, (G.induce ({o}ᶜ : Set V)).Reachable u v at hf
  push Not at hf
  obtain ⟨u, v, huv⟩ := hf
  let D : Set V := {o}ᶜ
  let H := G.induce D
  let P : V → Prop := fun x => ∃ hx : x ∈ D, H.Reachable u ⟨x, hx⟩
  let C : Finset V := Finset.univ.filter P
  let A : Finset V := insert o C
  let B : Finset V := insert o (Finset.univ \ C)
  have hoC : o ∉ C := by simp [C, P, D]
  have huC : u.1 ∈ C := by
    simp only [C, mem_filter, mem_univ, true_and]
    exact ⟨u.2, SimpleGraph.Reachable.refl u⟩
  have hvC : v.1 ∉ C := by
    simp only [C, mem_filter, mem_univ, true_and]
    rintro ⟨hv, hr⟩
    exact huv hr
  have hvne : v.1 ≠ o := fun h => v.2 (by simp [h])
  have hcover : A ∪ B = Finset.univ := by
    ext x
    simp [A, B]
  have hinter : A ∩ B = {o} := by
    ext x
    by_cases hx : x = o <;> simp [A, B, hx, hoC]
  have hsep : ∀ x ∈ A, x ∉ B → ∀ y ∈ B, y ∉ A → ¬ G.Adj x y := by
    intro x hx hxB y hy hyA hxy
    have hxC : x ∈ C := by
      by_contra hh
      exact hxB (by simp [B, hh])
    have hyC : y ∉ C := by
      intro hh
      exact hyA (by simp [A, hh])
    have hyD : y ∈ D := by
      have : y ≠ o := by
        intro h; subst y; exact hyA (by simp [A])
      simpa [D] using this
    have ⟨hxD, hr⟩ : P x := (mem_filter.mp hxC).2
    apply hyC
    apply mem_filter.mpr
    refine ⟨mem_univ _, ⟨hyD, ?_⟩⟩
    exact hr.trans (SimpleGraph.Adj.reachable hxy)
  have hAn : A ≠ Finset.univ := by
    intro h
    have : v.1 ∈ A := by rw [h]; exact mem_univ _
    have : v.1 = o ∨ v.1 ∈ C := by simpa [A] using this
    exact this.elim hvne hvC
  have hBn : B ≠ Finset.univ := by
    intro h
    have : u.1 ∈ B := by rw [h]; exact mem_univ _
    have hune : u.1 ≠ o := fun h => u.2 (by simp [h])
    have : u.1 = o ∨ u.1 ∉ C := by simpa [B] using this
    exact this.elim hune (fun hh => hh huC)
  exact (hind A B o hcover hinter hsep).elim hAn hBn
