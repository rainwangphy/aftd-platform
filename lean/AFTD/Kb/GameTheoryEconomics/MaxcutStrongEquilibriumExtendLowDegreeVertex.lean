import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfSaturatedVertex
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_strong_equilibrium_extend_low_degree_vertex

Topic: equilibria   Node: aa08ea78324f

Provenance: helper lemma. Structural reduction for OP-85, the unweighted Max-k-Cut strong-equilibrium existence problem in arXiv:2610.04948, Section 4.

If a vertex has degree strictly smaller than the number k of available colors, a strong equilibrium of the induced graph obtained by deleting it extends to a strong equilibrium of the original finite graph.
-/

open Finset

theorem maxcut_strong_equilibrium_extend_low_degree_vertex
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (k : ℕ) (hd : G.degree v < k)
    (hsub : ∃ s : (↑(Finset.univ.erase v) : Set V) → Fin k,
      is_maxcut_strong_equilibrium (G.induce (↑(Finset.univ.erase v) : Set V)) s) :
    ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
  classical
  let A : Finset V := Finset.univ.erase v
  obtain ⟨s, hs⟩ := hsub
  have hk : 0 < k := by omega
  let s0 : V → Fin k := fun w => if hw : w ∈ A then s ⟨w, hw⟩ else ⟨0, hk⟩
  let used := (G.neighborFinset v).image s0
  have hcard : used.card < Fintype.card (Fin k) := by
    calc
      used.card ≤ (G.neighborFinset v).card := Finset.card_image_le
      _ = G.degree v := G.card_neighborFinset_eq_degree v
      _ < Fintype.card (Fin k) := by simpa using hd
  have hc : ∃ c : Fin k, c ∉ used := by
    by_contra h
    push Not at h
    have heq : used = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [heq] at hcard
    exact (Nat.lt_irrefl _ hcard)
  obtain ⟨c, hc⟩ := hc
  let σ : V → Fin k := fun w => if w = v then c else s0 w
  have hproper : ∀ w, G.Adj v w → σ w ≠ σ v := by
    intro w hw
    have hwne : w ≠ v := (G.ne_of_adj hw).symm
    have hwused : s0 w ∈ used := by
      exact Finset.mem_image.mpr ⟨w, (G.mem_neighborFinset v w).mpr hw, rfl⟩
    have hne : s0 w ≠ c := by
      intro heq
      apply hc
      simpa [heq] using hwused
    simpa [σ, hwne] using hne
  have hs_eq : (fun x : (↑A : Set V) => σ x.1) = s := by
    funext x
    have hxne : x.1 ≠ v := (Finset.mem_erase.mp x.2).1
    simp [σ, s0, hxne, x.2]
  apply Exists.intro σ
  apply maxcut_strong_equilibrium_of_saturated_vertex G v σ hproper
  exact hs_eq ▸ hs
