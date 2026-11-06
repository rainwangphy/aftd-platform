import AFTD.Prelude
import AFTD.Kb.Tcs.TableauWeight
import AFTD.Kb.Tcs.AntiRibbonDiagram
import AFTD.Kb.Tcs.StandardYoungTableauDescentSet
import AFTD.Kb.Tcs.AntiRibbonMap
import AFTD.Kb.Tcs.StandardizationBlock
import AFTD.Kb.Tcs.StandardYoungTableauBox
import AFTD.Kb.Tcs.StandardYoungTableau

/-!
# anti_ribbon_map_preserves_weight

Topic: combinatorics   Node: 606dc73f2628

Provenance: helper lemma. arXiv:2611.07715 Theorem 4.3(2) and Section 5.1

For any finite diagram D : Finset (ℕ × ℕ), any standard Young tableau T on D, and any filling M : D → ℕ belonging to standardization_block T, the monomial weight tableau_weight of anti_ribbon_map T M on the anti-ribbon diagram anti_ribbon_diagram D.card (standard_young_tableau_descent_set T) equals tableau_weight D M.
-/

/-- The anti-ribbon map preserves the monomial weight of fillings in each standardization block. -/
theorem anti_ribbon_map_preserves_weight {D : Finset (ℕ × ℕ)} (T : StandardYoungTableau D)
    (M : D → ℕ) (hM : M ∈ standardization_block T) :
    tableau_weight (anti_ribbon_diagram D.card (standard_young_tableau_descent_set T)) (anti_ribbon_map T M) =
      tableau_weight D M := by
  set S := standard_young_tableau_descent_set T with hS
  set g : ℕ → ℕ × ℕ := fun j => (1 + ((Finset.Ico 1 j).filter (fun x => x ∈ S)).card,
        1 + (j - 1 - ((Finset.Ico 1 j).filter (fun x => x ∈ S)).card)) with hgdef
  have hanti : anti_ribbon_diagram D.card S = (Finset.Icc 1 D.card).image g := rfl
  have h_gmem : ∀ k ∈ Finset.Icc 1 D.card, g k ∈ anti_ribbon_diagram D.card S := by
    intro k hk
    rw [hanti]
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  have h_phi_g : ∀ k ∈ Finset.Icc 1 D.card, (g k).1 + (g k).2 - 1 = k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hle : ((Finset.Ico 1 k).filter (fun x => x ∈ S)).card ≤ k - 1 := by
      calc ((Finset.Ico 1 k).filter (fun x => x ∈ S)).card ≤ (Finset.Ico 1 k).card := Finset.card_filter_le _ _
        _ = k - 1 := by rw [Nat.card_Ico]
    simp only [hgdef]
    set a := ((Finset.Ico 1 k).filter (fun x => x ∈ S)).card with ha
    have h1 : a + (k - 1 - a) = k - 1 := Nat.add_sub_of_le hle
    omega
  have h_g_phi : ∀ p ∈ anti_ribbon_diagram D.card S, g (p.1 + p.2 - 1) = p := by
    intro p hp
    rw [hanti, Finset.mem_image] at hp
    obtain ⟨k, hk, hgk⟩ := hp
    have hpk : p.1 + p.2 - 1 = k := by
      rw [← hgk]
      exact h_phi_g k hk
    rw [hpk]; exact hgk
  have h_mem : ∀ p ∈ anti_ribbon_diagram D.card S, p.1 + p.2 - 1 ∈ Finset.Icc 1 D.card := by
    intro p hp
    rw [hanti, Finset.mem_image] at hp
    obtain ⟨k, hk, hgk⟩ := hp
    have hpk : p.1 + p.2 - 1 = k := by
      rw [← hgk]; exact h_phi_g k hk
    rw [hpk]; exact hk
  let f : ↥(anti_ribbon_diagram D.card S) → ↥(Finset.Icc 1 D.card) :=
    fun p => ⟨p.val.1 + p.val.2 - 1, h_mem p.val p.property⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    have h1 : p.val.1 + p.val.2 - 1 = q.val.1 + q.val.2 - 1 := by
      have h := congrArg (Subtype.val) hpq
      simpa [f] using h
    have hgg : g (p.val.1 + p.val.2 - 1) = g (q.val.1 + q.val.2 - 1) := by rw [h1]
    rw [h_g_phi p.val p.property, h_g_phi q.val q.property] at hgg
    exact Subtype.ext hgg
  have hf_surj : Function.Surjective f := by
    intro k
    refine ⟨⟨g k.val, h_gmem k.val k.property⟩, ?_⟩
    apply Subtype.ext
    simp only [f]
    exact h_phi_g k.val k.property
  let e : ↥(anti_ribbon_diagram D.card S) ≃ ↥D :=
    (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).trans T.toEquiv.symm
  have he_apply : ∀ p, e p = T.toEquiv.symm (f p) := by
    intro p; rfl
  have hpoint : ∀ p : ↥(anti_ribbon_diagram D.card S), anti_ribbon_map T M p = M (e p) := by
    intro p
    have hbox : standard_young_tableau_box T (p.val.1 + p.val.2 - 1) (h_mem p.val p.property) = e p := by
      rw [he_apply]
      rfl
    simp only [anti_ribbon_map]
    rw [dif_pos (h_mem p.val p.property)]
    rw [hbox]
  simp only [tableau_weight]
  exact (Fintype.prod_equiv e (fun p => MvPolynomial.X (anti_ribbon_map T M p))
    (fun u => MvPolynomial.X (M u)) (fun p => by rw [hpoint p]))
