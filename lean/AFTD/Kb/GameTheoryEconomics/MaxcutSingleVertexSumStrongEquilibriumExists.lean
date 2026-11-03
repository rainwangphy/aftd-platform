import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumColorPermutation
import AFTD.Kb.GameTheoryEconomics.MaxcutSingleVertexSumStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_single_vertex_sum_strong_equilibrium_exists

Topic: equilibria   Node: a508829c724c

Provenance: helper lemma. Structural reduction for OP-85, the strong-equilibrium existence problem; the two-piece gluing step is maxcut_single_vertex_sum_strong_equilibrium.

For two induced subgraphs covering a finite graph, meeting in exactly one vertex, with no edges between their exclusive parts, strong equilibria on the two subgraphs imply a strong equilibrium on the whole graph.
-/

open Finset

theorem maxcut_single_vertex_sum_strong_equilibrium_exists    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (o : V) (k : ℕ)
    (hcover : A ∪ B = Finset.univ) (hinter : A ∩ B = {o})
    (hsep : ∀ v ∈ A, v ∉ B → ∀ w ∈ B, w ∉ A → ¬ G.Adj v w)
    (hA : ∃ σ : (↑A : Set V) → Fin k, is_maxcut_strong_equilibrium (G.induce (↑A : Set V)) σ)
    (hB : ∃ σ : (↑B : Set V) → Fin k, is_maxcut_strong_equilibrium (G.induce (↑B : Set V)) σ) :
    ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
  classical
  have hoA : o ∈ A := (mem_inter.mp (by rw [hinter]; exact mem_singleton_self o)).1
  have hoB : o ∈ B := (mem_inter.mp (by rw [hinter]; exact mem_singleton_self o)).2
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let p : Equiv.Perm (Fin k) := Equiv.swap (b ⟨o, hoB⟩) (a ⟨o, hoA⟩)
  let b' := fun v => p (b v)
  have hb' : is_maxcut_strong_equilibrium (G.induce (↑B : Set V)) b' := maxcut_strong_equilibrium_color_permutation _ b p hb
  have hroot : b' ⟨o, hoB⟩ = a ⟨o, hoA⟩ := by simp [b', p]
  let s : V → Fin k := fun v => if h : v ∈ A then a ⟨v, h⟩ else b' ⟨v, by
    have : v ∈ A ∪ B := by rw [hcover]; exact mem_univ v
    exact (mem_union.mp this).resolve_left h⟩
  have hsA : (fun v : (↑A : Set V) => s v.1) = a := by
    funext v
    simp [s, v.2]
  have hsB : (fun v : (↑B : Set V) => s v.1) = b' := by
    funext v
    by_cases hv : v.1 ∈ A
    · have heq : v.1 = o := by
        have hm : v.1 ∈ A ∩ B := mem_inter.mpr ⟨hv, v.2⟩
        rw [hinter] at hm
        exact mem_singleton.mp hm
      subst heq
      simpa [s, hoA] using hroot.symm
    · simp [s, hv]
  exact ⟨s, maxcut_single_vertex_sum_strong_equilibrium G A B o k s hcover hinter hsep (hsA ▸ ha) (hsB ▸ hb')⟩
