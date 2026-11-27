import AFTD.Prelude
import AFTD.Kb.Tcs.HasCooperativeColoringPair
import AFTD.Kb.Tcs.IsCycleFactor
import AFTD.Kb.Tcs.CycleGraphThreeNoCooperativeColoring
import AFTD.Kb.Tcs.CycleGraphIsCycleFactor
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.C
import AFTD.Kb.Tcs.Supp

/-!
# exists_cycle_factors_no_cooperative_coloring

Topic: combinatorics   Node: 5b54a7ec2b4a

Provenance: formalization of a published result. Source: arXiv:2611.34299 Lemma 3.4

For every integer ℓ ≥ 3, there exist two C_ℓ-factors on a common finite vertex set that admit no cooperative coloring.
-/

theorem exists_cycle_factors_no_cooperative_coloring_is_cycle_factor_of_iso (ℓ : ℕ) {G : SimpleGraph (Fin ℓ)}
    (iso : G ≃g SimpleGraph.cycleGraph ℓ) : is_cycle_factor G ℓ := by
  intro c
  have hprec : G.Preconnected := by
    intro u v
    obtain ⟨w⟩ := SimpleGraph.cycleGraph_preconnected (iso u) (iso v)
    have w' := w.map iso.symm.toHom
    have hu : iso.symm.toHom (iso u) = u := iso.symm_apply_apply u
    have hv : iso.symm.toHom (iso v) = v := iso.symm_apply_apply v
    rw [hu, hv] at w'
    exact ⟨w'⟩
  have hsupp : c.supp = (Set.univ : Set (Fin ℓ)) := by
    obtain ⟨w, rfl⟩ := c.exists_rep
    ext v
    simp only [Set.mem_univ, iff_true]
    exact SimpleGraph.ConnectedComponent.sound (hprec v w)
  have h1 : G.induce c.supp ≃g G.induce Set.univ := by rw [hsupp]
  exact ⟨h1.trans ((SimpleGraph.induceUnivIso G).trans iso)⟩

/-- For every ℓ ≥ 3, there exist two C_ℓ-factors on a common finite vertex set with no cooperative coloring. -/
theorem exists_cycle_factors_no_cooperative_coloring (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    ∃ (V : Type) (_ : Fintype V),
      ∃ G₁ G₂ : SimpleGraph V,
        is_cycle_factor G₁ ℓ ∧ is_cycle_factor G₂ ℓ ∧ ¬ has_cooperative_coloring_pair G₁ G₂ := by
  rcases hℓ.eq_or_lt with rfl | h4
  · refine ⟨Fin 3, inferInstance, SimpleGraph.cycleGraph 3, SimpleGraph.cycleGraph 3,
      cycleGraph_is_cycle_factor 3 (by decide), cycleGraph_is_cycle_factor 3 (by decide),
      cycleGraph_three_no_cooperative_coloring⟩
  · have hℓ4 : 4 ≤ ℓ := h4
    let v₀ : Fin ℓ := ⟨0, by omega⟩
    let v₁ : Fin ℓ := ⟨1, by omega⟩
    let v₂ : Fin ℓ := ⟨2, by omega⟩
    let v₃ : Fin ℓ := ⟨3, by omega⟩
    let τ : Fin ℓ ≃ Fin ℓ := Equiv.swap v₁ v₂
    let G₁ := SimpleGraph.cycleGraph ℓ
    let G₂ := SimpleGraph.map τ G₁
    refine ⟨Fin ℓ, inferInstance, G₁, G₂, cycleGraph_is_cycle_factor ℓ (by omega),
      exists_cycle_factors_no_cooperative_coloring_is_cycle_factor_of_iso ℓ
        (SimpleGraph.Iso.map τ G₁).symm, ?_⟩
    rintro ⟨I₁, I₂, hI₁, hI₂, hunion⟩
    have hv01 : G₁.Adj v₀ v₁ := by
      apply SimpleGraph.pathGraph_le_cycleGraph
      rw [SimpleGraph.pathGraph_adj]
      left; rfl
    have hv12 : G₁.Adj v₁ v₂ := by
      apply SimpleGraph.pathGraph_le_cycleGraph
      rw [SimpleGraph.pathGraph_adj]
      left; rfl
    have hv23 : G₁.Adj v₂ v₃ := by
      apply SimpleGraph.pathGraph_le_cycleGraph
      rw [SimpleGraph.pathGraph_adj]
      left; rfl
    have hadj_iff (x y : Fin ℓ) : G₂.Adj (τ x) (τ y) ↔ G₁.Adj x y :=
      (SimpleGraph.Iso.map τ G₁).map_rel_iff'
    have hv02' : G₂.Adj v₀ v₂ := by
      have h0 : τ v₀ = v₀ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; injection h with h; omega
        · intro h; injection h with h; omega
      have h1 : τ v₁ = v₂ := Equiv.swap_apply_left v₁ v₂
      rw [← h0, ← h1]
      exact (hadj_iff v₀ v₁).mpr hv01
    have hv21' : G₂.Adj v₂ v₁ := by
      have h1 : τ v₁ = v₂ := Equiv.swap_apply_left v₁ v₂
      have h2 : τ v₂ = v₁ := Equiv.swap_apply_right v₁ v₂
      rw [← h1, ← h2]
      exact (hadj_iff v₁ v₂).mpr hv12
    have hv13' : G₂.Adj v₁ v₃ := by
      have h2 : τ v₂ = v₁ := Equiv.swap_apply_right v₁ v₂
      have h3 : τ v₃ = v₃ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; injection h with h; omega
        · intro h; injection h with h; omega
      rw [← h2, ← h3]
      exact (hadj_iff v₂ v₃).mpr hv23
    have mem_cov (x : Fin ℓ) : x ∈ I₁ ∨ x ∈ I₂ :=
      Set.mem_or_mem_of_mem_union (by rw [hunion]; exact Set.mem_univ x)
    have na01 : ¬ (v₀ ∈ I₁ ∧ v₁ ∈ I₁) := fun ⟨ha, hb⟩ => hI₁ ha hb hv01.ne hv01
    have na12 : ¬ (v₁ ∈ I₁ ∧ v₂ ∈ I₁) := fun ⟨ha, hb⟩ => hI₁ ha hb hv12.ne hv12
    have na23 : ¬ (v₂ ∈ I₁ ∧ v₃ ∈ I₁) := fun ⟨ha, hb⟩ => hI₁ ha hb hv23.ne hv23
    have nb02 : ¬ (v₀ ∈ I₂ ∧ v₂ ∈ I₂) := fun ⟨ha, hb⟩ => hI₂ ha hb hv02'.ne hv02'
    have nb21 : ¬ (v₂ ∈ I₂ ∧ v₁ ∈ I₂) := fun ⟨ha, hb⟩ => hI₂ ha hb hv21'.ne hv21'
    have nb13 : ¬ (v₁ ∈ I₂ ∧ v₃ ∈ I₂) := fun ⟨ha, hb⟩ => hI₂ ha hb hv13'.ne hv13'
    have h0 := mem_cov v₀
    have h1 := mem_cov v₁
    have h2 := mem_cov v₂
    have h3 := mem_cov v₃
    tauto
