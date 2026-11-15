import AFTD.Prelude
import AFTD.Kb.Tcs.IsOrientedStar
import AFTD.Kb.Tcs.IsOsOrientedStar
import AFTD.Kb.Tcs.IsOasOrientedStar
import AFTD.Kb.Tcs.DigraphonSymmetrization
import AFTD.Kb.Tcs.IsDigraphon
import AFTD.Kb.Tcs.DigraphonInMarginal
import AFTD.Kb.Tcs.DigraphInDegree
import AFTD.Kb.Tcs.DigraphonOutMarginal
import AFTD.Kb.Tcs.DigraphOutDegree
import AFTD.Kb.Tcs.OrientedStarDensity

/-!
# oriented_star_one_edge_os_and_oas

Topic: combinatorics   Node: 6c73438b95dc

Provenance: formalization of a published result. Source: arXiv:2611.15027 Theorem 1.9 (1)

If an oriented star D has one edge (two vertices), then D is both OS and OAS.
-/

open MeasureTheory

lemma oriented_star_one_edge_os_and_oas_integrable (W : ℝ → ℝ → ℝ) (hW : is_digraphon W) :
    Integrable (fun z : ℝ × ℝ => W z.1 z.2)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
  have : IsFiniteMeasure ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) :=
    inferInstance
  apply Integrable.of_bound (hW.2.aestronglyMeasurable) 1
  rw [Measure.prod_restrict]
  have hmeas : MeasurableSet (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  apply ae_restrict_of_forall_mem hmeas
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  dsimp
  have := hW.1 x y hx hy
  rw [abs_le]
  exact ⟨by linarith [this.1], this.2⟩

lemma oriented_star_one_edge_os_and_oas_symm_in (W : ℝ → ℝ → ℝ) (hW : is_digraphon W) :
    (∫ x in Set.Icc (0:ℝ) 1, digraphon_in_marginal (digraphon_symmetrization W) x) =
      ∫ x in Set.Icc (0:ℝ) 1, digraphon_in_marginal W x := by
  dsimp [digraphon_in_marginal, digraphon_symmetrization]
  have h1 : Integrable (fun z : ℝ × ℝ => W z.1 z.2)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) :=
    oriented_star_one_edge_os_and_oas_integrable W hW
  have h2 : Integrable (fun z : ℝ × ℝ => W z.2 z.1)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) :=
    h1.swap
  have h_add : Integrable (fun z : ℝ × ℝ => (W z.2 z.1 + W z.1 z.2) / 2)
      ((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) :=
    (h2.add h1).div_const 2
  rw [integral_integral (f := fun x y => (W y x + W x y) / 2) h_add]
  rw [integral_integral (f := fun x y => W y x) h2]
  have eq_swap : ∫ z, W z.2 z.1 ∂((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) =
      ∫ z, W z.1 z.2 ∂((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))) :=
    integral_prod_swap (Function.uncurry W)
  have h_lin : (∫ z, (W z.2 z.1 + W z.1 z.2) / 2 ∂((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1)))) =
      ((∫ z, W z.2 z.1 ∂((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1)))) +
       (∫ z, W z.1 z.2 ∂((volume.restrict (Set.Icc (0:ℝ) 1)).prod (volume.restrict (Set.Icc (0:ℝ) 1))))) / 2 := by
    rw [integral_div, integral_add h2 h1]
  rw [h_lin, eq_swap]
  ring

lemma oriented_star_one_edge_os_and_oas_symm_out (W : ℝ → ℝ → ℝ) (hW : is_digraphon W) :
    (∫ x in Set.Icc (0:ℝ) 1, digraphon_out_marginal (digraphon_symmetrization W) x) =
      ∫ x in Set.Icc (0:ℝ) 1, digraphon_out_marginal W x := by
  have h_symm : digraphon_out_marginal (digraphon_symmetrization W) =
                digraphon_in_marginal (digraphon_symmetrization W) := by
    ext x
    dsimp [digraphon_out_marginal, digraphon_in_marginal, digraphon_symmetrization]
    congr 1 with y
    ring
  rw [h_symm, oriented_star_one_edge_os_and_oas_symm_in W hW]
  dsimp [digraphon_in_marginal, digraphon_out_marginal]
  have hint := oriented_star_one_edge_os_and_oas_integrable W hW
  exact (integral_integral_swap hint).symm

lemma oriented_star_one_edge_os_and_oas_degrees
    {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (c : V)
    (hstar : is_oriented_star D c) (hcard : Fintype.card V = 2) :
    (digraph_in_degree D c = 1 ∧ digraph_out_degree D c = 0) ∨
    (digraph_in_degree D c = 0 ∧ digraph_out_degree D c = 1) := by
  classical
  have h_univ : (Finset.univ : Finset V).card = 2 := hcard
  have hc : c ∈ (Finset.univ : Finset V) := Finset.mem_univ c
  have h_erase : ((Finset.univ : Finset V).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hc, h_univ]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h_erase
  have hvc : v ≠ c := by
    intro h
    have hmem : v ∈ (Finset.univ : Finset V).erase c := by
      rw [hv]
      exact Finset.mem_singleton_self v
    rw [Finset.mem_erase] at hmem
    exact hmem.1 h
  have h_all : ∀ u : V, u = c ∨ u = v := by
    intro u
    by_cases h : u = c
    · left; exact h
    · right
      have : u ∈ (Finset.univ : Finset V).erase c := Finset.mem_erase.mpr ⟨h, Finset.mem_univ u⟩
      rw [hv] at this
      exact Finset.mem_singleton.mp this
  have h_loop := hstar.1
  have h_star_edge := hstar.2.2.2 v hvc
  have h_asymm := hstar.2.2.1
  dsimp [digraph_in_degree, digraph_out_degree]
  cases h_star_edge with
  | inl hcv =>
    have hnvc : ¬ D.Adj v c := h_asymm c v hcv
    right
    constructor
    · have : Finset.filter (fun u => D.Adj u c) Finset.univ = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro u _
        rcases h_all u with rfl | rfl
        · exact h_loop u
        · exact hnvc
      rw [this, Finset.card_empty]
    · have : Finset.filter (D.Adj c) Finset.univ = {v} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hu
          rcases h_all u with rfl | rfl
          · exact (h_loop u hu).elim
          · rfl
        · rintro rfl
          exact hcv
      rw [this, Finset.card_singleton]
  | inr hvc_edge =>
    have hncv : ¬ D.Adj c v := h_asymm v c hvc_edge
    left
    constructor
    · have : Finset.filter (fun u => D.Adj u c) Finset.univ = {v} := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hu
          rcases h_all u with rfl | rfl
          · exact (h_loop u hu).elim
          · rfl
        · rintro rfl
          exact hvc_edge
      rw [this, Finset.card_singleton]
    · have : Finset.filter (D.Adj c) Finset.univ = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro u _
        rcases h_all u with rfl | rfl
        · exact h_loop u
        · exact hncv
      rw [this, Finset.card_empty]

/-- An oriented star with a single edge is both OS and OAS. -/
theorem oriented_star_one_edge_os_and_oas
    {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (c : V)
    (hstar : is_oriented_star D c) (hcard : Fintype.card V = 2) :
    is_os_oriented_star D c ∧ is_oas_oriented_star D c := by
  have hdeg := oriented_star_one_edge_os_and_oas_degrees D c hstar hcard
  have h_eq : ∀ W : ℝ → ℝ → ℝ, is_digraphon W →
      oriented_star_density D c (digraphon_symmetrization W) = oriented_star_density D c W := by
    intro W hW
    rcases hdeg with ⟨hin, hout⟩ | ⟨hin, hout⟩
    · dsimp [oriented_star_density]
      rw [hin, hout]
      simp only [pow_one, pow_zero, mul_one]
      exact oriented_star_one_edge_os_and_oas_symm_in W hW
    · dsimp [oriented_star_density]
      rw [hin, hout]
      simp only [pow_one, pow_zero, one_mul]
      exact oriented_star_one_edge_os_and_oas_symm_out W hW
  constructor
  · intro W hW
    rw [h_eq W hW]
  · intro W hW
    rw [h_eq W hW]
