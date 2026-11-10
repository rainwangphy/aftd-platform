import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumOfProperColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityOfProperColoring
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityLeDegree
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.IsMaxcutNeutralPivotSafe
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_unused_color_or_safe_pivot_of_proper_coloring

Topic: equilibria   Node: f5b6c3fa83c9

Provenance: helper lemma. Colorable-graph case of maxcut_exists_unused_color_or_safe_pivot.

If a finite graph admits a proper k-coloring and N has fewer than 2k vertices, there is a strong equilibrium with an unused color on N or a singleton color whose vertex is neutral-pivot safe.
-/

open scoped Classical
lemma in688_pigeonhole {V : Type} [Fintype V] [DecidableEq V]
    (N : Finset V) (k : ℕ) (hN : N.card < 2 * k) (s : V → Fin k) :
    ∃ c : Fin k, (N.filter fun w => s w = c).card = 0 ∨ (N.filter fun w => s w = c).card = 1 := by
  by_contra! h
  have h_ge : ∀ c : Fin k, 2 ≤ (N.filter fun w => s w = c).card := by
    intro c
    have := h c
    omega
  have h_sum : N.card = ∑ c : Fin k, (N.filter fun w => s w = c).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have h_sum_ge : 2 * k ≤ ∑ c : Fin k, (N.filter fun w => s w = c).card := by
    calc 2 * k = ∑ c : Fin k, 2 := by simp [Finset.sum_const, mul_comm]
    _ ≤ ∑ c : Fin k, (N.filter fun w => s w = c).card := Finset.sum_le_sum fun c _ => h_ge c
  omega

theorem maxcut_unused_color_or_safe_pivot_of_proper_coloring {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : Finset V) (k : ℕ)
    (hN : N.card < 2*k) (s : V → Fin k)
    (hproper : ∀ v w, G.Adj v w → s v ≠ s w) :
    ∃ t : V → Fin k, is_maxcut_strong_equilibrium G t ∧
      ∃ c : Fin k, (N.filter fun w => t w = c).card = 0 ∨
        ∃ u : V, (N.filter fun w => t w = c) = {u} ∧ is_maxcut_neutral_pivot_safe G t u := by
  classical
  obtain ⟨c, hc0 | hc1⟩ := in688_pigeonhole N k hN s
  · exact ⟨s, maxcut_strong_equilibrium_of_proper_coloring G s hproper, c, Or.inl hc0⟩
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc1
  by_cases hsafe : is_maxcut_neutral_pivot_safe G s u
  · exact ⟨s, maxcut_strong_equilibrium_of_proper_coloring G s hproper, c, Or.inr ⟨u, hu, hsafe⟩⟩
  unfold is_maxcut_neutral_pivot_safe at hsafe
  push_neg at hsafe
  obtain ⟨C, t, huC, hchange, hout, hweak, hstrong⟩ := hsafe
  have houtu : ∀ x, x ≠ u → t x = s x := by
    intro x hxu
    apply hout x
    intro hxC
    have hsmax := maxcut_utility_of_proper_coloring G s hproper x
    have htmax := maxcut_utility_le_degree G t x
    have hgain := hstrong.1 x hxC hxu
    omega
  have humax : maxcut_utility G t u = G.degree u := by
    have hsmax := maxcut_utility_of_proper_coloring G s hproper u
    have htmax := maxcut_utility_le_degree G t u
    omega
  have hmono : (Finset.univ.filter fun w => G.Adj u w ∧ t w = t u).card = 0 := by
    have heq := maxcut_utility_add_monochromatic_card G t u
    omega
  have hun : ∀ w, G.Adj u w → t u ≠ t w := by
    intro w huw heq
    have hw : w ∈ Finset.univ.filter (fun w => G.Adj u w ∧ t w = t u) := by
      simp [huw, heq]
    rw [Finset.card_eq_zero.mp hmono] at hw
    simp at hw
  have htproper : ∀ v w, G.Adj v w → t v ≠ t w := by
    intro v w hvw
    by_cases hv : v = u
    · subst v; exact hun w hvw
    · by_cases hw : w = u
      · subst w; exact Ne.symm (hun v hvw.symm)
      · rw [houtu v hv, houtu w hw]
        exact hproper v w hvw
  refine ⟨t, maxcut_strong_equilibrium_of_proper_coloring G t htproper, c, Or.inl ?_⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxN, hxc⟩ := Finset.mem_filter.mp hx
  have huc : s u = c := by
    have hmem : u ∈ N.filter (fun w => s w = c) := by rw [hu]; simp
    exact (Finset.mem_filter.mp hmem).2
  by_cases hxu : x = u
  · subst x; exact hchange (hxc.trans huc.symm)
  · have hsx : s x = c := by simpa [houtu x hxu] using hxc
    have hmem : x ∈ N.filter (fun w => s w = c) := Finset.mem_filter.mpr ⟨hxN, hsx⟩
    rw [hu] at hmem
    exact hxu (Finset.mem_singleton.mp hmem)
