import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutSingleVertexSumStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityLeDegree
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_strong_equilibrium_of_saturated_vertex

Topic: equilibria   Node: e53e57b259bf

Provenance: helper lemma. Structural reduction for OP-85, the unweighted Max-k-Cut strong-equilibrium existence problem in arXiv:2610.04948, Section 4.

A coloring of a finite graph is a strong equilibrium if its restriction after deleting a vertex is a strong equilibrium and every edge incident to the deleted vertex is cut by the coloring.
-/

open Finset

theorem maxcut_strong_equilibrium_of_saturated_vertex
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {k : ℕ} (σ : V → Fin k)
    (hproper : ∀ w, G.Adj v w → σ w ≠ σ v)
    (hsub : is_maxcut_strong_equilibrium (G.induce (↑(Finset.univ.erase v) : Set V))
      (fun x => σ x.1)) :
    is_maxcut_strong_equilibrium G σ := by
  classical
  let A : Finset V := Finset.univ.erase v
  have hfull : maxcut_utility G σ v = G.degree v := by
    have hz : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w _ ⟨hw, heq⟩
      exact hproper w hw heq
    have h := maxcut_utility_add_monochromatic_card G σ v
    simpa [hz] using h
  have hsplit : ∀ (p : V → Fin k) (x : V) (hx : x ∈ A),
      maxcut_utility G p x =
        maxcut_utility (G.induce (↑A : Set V)) (fun y => p y.1) ⟨x,hx⟩ +
          if G.Adj x v ∧ p v ≠ p x then 1 else 0 := by
    intro p x hx
    let P : V → Prop := fun w => G.Adj x w ∧ p w ≠ p x
    have hcard : (Finset.univ.filter P).card = (A.filter P).card + if P v then 1 else 0 := by
      have huniv : insert v A = Finset.univ := by simp [A]
      have hnot : v ∉ A.filter P := by simp [A]
      rw [← huniv, Finset.filter_insert]
      by_cases hp : P v <;> simp [hp, hnot]
    have hsubcard := maxcut_single_vertex_sum_strong_equilibrium_card_filter_subtype A P
    change (Finset.univ.filter P).card = (Finset.univ.filter (fun y : (↑A : Set V) => P y.1)).card + if P v then 1 else 0
    rw [hsubcard]
    exact hcard
  intro S τ hdev
  have hvS : v ∉ S := by
    intro hv
    have hg := hdev.2.2 v hv
    have hu := maxcut_utility_le_degree G τ v
    omega
  let S' : Finset (↑A : Set V) := Finset.univ.filter (fun x => x.1 ∈ S)
  have hdev' : is_maxcut_strong_deviation (G.induce (↑A : Set V)) (fun x => σ x.1) S' (fun x => τ x.1) := by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hdev.1
      have hxne : x ≠ v := by intro h; subst x; exact hvS hx
      exact ⟨⟨x, by simp [A, hxne]⟩, by simp [S', hx]⟩
    · intro x hx
      have hxS : x.1 ∉ S := by simpa [S'] using hx
      exact hdev.2.1 x.1 hxS
    · rintro ⟨x, hxA⟩ hx
      have hxS : x ∈ S := by simpa [S'] using hx
      have hg := hdev.2.2 x hxS
      have ha : (if G.Adj x v ∧ τ v ≠ τ x then 1 else 0 : ℕ) ≤
          (if G.Adj x v ∧ σ v ≠ σ x then 1 else 0 : ℕ) := by
        by_cases hadj : G.Adj x v
        · have hp : σ v ≠ σ x := Ne.symm (hproper x (G.adj_symm hadj))
          simp only [hadj, hp, true_and, if_true]
          split <;> omega
        · simp [hadj]
      rw [hsplit σ x hxA, hsplit τ x hxA] at hg
      omega
  exact hsub S' (fun x => τ x.1) hdev'
