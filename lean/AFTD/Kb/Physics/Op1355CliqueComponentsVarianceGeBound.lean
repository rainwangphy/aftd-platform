import AFTD.Prelude
import AFTD.Kb.Physics.HardCoreWeightedVar
import AFTD.Kb.Physics.HardCoreWeightedClosedNeighborhoodBound
import AFTD.Kb.Physics.Op1355CompleteGraphVarianceGeBound
import AFTD.Kb.Tcs.FiniteVarianceRecurrenceAdditive
import AFTD.Kb.Tcs.SimpleGraphCliqueComponentsIndependentIffInjective
import AFTD.Kb.Tcs.SimpleGraphCliqueComponentsClosedNeighborhood
import AFTD.Kb.Tcs.Supp

/-!
# op_1355_clique_components_variance_ge_bound

Topic: statistical_mechanics   Node: 50e63e0cb5b3

Provenance: formalization of a published result. Source: knowledgebase

For any finite simple graph G on a finite type V with decidable equality whose connected components are all cliques, and for all positive vertex fugacities lam and all nonnegative observable weights a, the weighted hard-core closed-neighborhood bound hardCoreWeightedClosedNeighborhoodBound G lam a is at most the weighted hard-core variance hardCoreWeightedVar G lam a.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace In703
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def compFiber (c : G.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => G.connectedComponentMk v = c)

noncomputable def cliqueIndep (S : Finset G.ConnectedComponent) : Finset (Finset V) :=
  Finset.univ.filter fun I =>
    (∀ v ∈ I, G.connectedComponentMk v ∈ S) ∧ (I : Set V).InjOn G.connectedComponentMk

lemma cliqueIndep_pairwiseDisjoint (c : G.ConnectedComponent) (S : Finset G.ConnectedComponent) (hc : c ∉ S) :
    (↑(compFiber G c) : Set V).PairwiseDisjoint (fun u => (cliqueIndep G S).image (insert u)) := by
  intro u hu v hv hne
  simp only [compFiber, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  dsimp [Function.onFun]
  rw [Finset.disjoint_left]
  intro I hI
  simp only [cliqueIndep, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hI
  rcases hI with ⟨J, ⟨hJ, -⟩, rfl⟩
  intro h_mem
  simp only [cliqueIndep, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h_mem
  rcases h_mem with ⟨K, ⟨hK, -⟩, heq⟩
  have hu_in : u ∈ insert v K := by
    rw [heq]
    exact Finset.mem_insert_self u J
  simp only [Finset.mem_insert] at hu_in
  rcases hu_in with rfl | huK
  · exact hne rfl
  · have hcomp := hK u huK
    rw [hu] at hcomp
    exact hc hcomp

lemma cliqueIndep_insert_injOn (c : G.ConnectedComponent) (S : Finset G.ConnectedComponent) (hc : c ∉ S)
    (u : V) (hu : u ∈ compFiber G c) :
    Set.InjOn (insert u) (cliqueIndep G S : Set (Finset V)) := by
  simp only [compFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  intro J hJ K hK heq
  simp only [cliqueIndep, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hJ hK
  have huJ : u ∉ J := by
    intro h
    have := hJ.1 u h
    rw [hu] at this
    exact hc this
  have huK : u ∉ K := by
    intro h
    have := hK.1 u h
    rw [hu] at this
    exact hc this
  ext x
  have hx : x ∈ insert u J ↔ x ∈ insert u K := by rw [heq]
  simp only [Finset.mem_insert] at hx
  by_cases hxu : x = u
  · subst hxu
    simp [huJ, huK]
  · simp [hxu] at hx
    exact hx

lemma cliqueIndep_insert_decomposition (c : G.ConnectedComponent) (S : Finset G.ConnectedComponent)
    (hc : c ∉ S) : cliqueIndep G (insert c S) =
      cliqueIndep G S ∪ (compFiber G c).biUnion (fun u => (cliqueIndep G S).image (insert u)) := by
  classical
  ext I
  simp only [cliqueIndep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨hS, hinj⟩
    by_cases he : ∃ u ∈ I, G.connectedComponentMk u = c
    · obtain ⟨u,huI,huc⟩ := he
      right
      refine ⟨u, ?_, I.erase u, ?_, Finset.insert_erase huI⟩
      · simp [compFiber, huc]
      · constructor
        · intro v hv
          have hvI := (Finset.mem_erase.mp hv).2
          have hm := hS v hvI
          simp only [Finset.mem_insert] at hm
          rcases hm with hvc | hvS
          · have hvu := hinj hvI huI (hvc.trans huc.symm)
            exact ((Finset.mem_erase.mp hv).1 hvu).elim
          · exact hvS
        · intro v hv w hw heq
          exact hinj (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hw).2 heq
    · left
      refine ⟨?_, hinj⟩
      intro v hv
      have hm := hS v hv
      simp only [Finset.mem_insert] at hm
      rcases hm with hvc | hvS
      · exact (he ⟨v,hv,hvc⟩).elim
      · exact hvS
  · rintro (⟨hS, hinj⟩ | ⟨u,hu,J,⟨hJ,hinj⟩,rfl⟩)
    · refine ⟨?_, hinj⟩
      intro v hv
      exact Finset.mem_insert_of_mem (hS v hv)
    · have huc : G.connectedComponentMk u = c := by simpa [compFiber] using hu
      have huJ : u ∉ J := by
        intro huJ
        apply hc
        simpa [huc] using hJ u huJ
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [Finset.mem_insert] at hv
        rcases hv with rfl | hv
        · simpa [huc]
        · exact Finset.mem_insert_of_mem (hJ v hv)
      · intro v hv w hw heq
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hv hw
        rcases hv with rfl | hv <;> rcases hw with rfl | hw
        · rfl
        · have : G.connectedComponentMk w ∈ S := hJ w hw
          rw [← heq, huc] at this
          exact (hc this).elim
        · have : G.connectedComponentMk v ∈ S := hJ v hv
          rw [heq, huc] at this
          exact (hc this).elim
        · exact hinj hv hw heq

lemma cliqueIndep_disjoint_old_new (c : G.ConnectedComponent) (S : Finset G.ConnectedComponent)
    (hc : c ∉ S) : Disjoint (cliqueIndep G S)
      ((compFiber G c).biUnion (fun u => (cliqueIndep G S).image (insert u))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro I hI hnew
  obtain ⟨u,hu,himg⟩ := Finset.mem_biUnion.mp hnew
  obtain ⟨J,hJ,hJI⟩ := Finset.mem_image.mp himg
  subst I
  have huc : G.connectedComponentMk u = c := by simpa [compFiber] using hu
  have hI' := (Finset.mem_filter.mp hI).2.1 u (Finset.mem_insert_self u J)
  exact hc (huc ▸ hI')

lemma cliqueIndep_sum_insert (c : G.ConnectedComponent) (S : Finset G.ConnectedComponent)
    (hc : c ∉ S) (f : Finset V → ℝ) :
    (∑ I ∈ cliqueIndep G (insert c S), f I) =
      (∑ I ∈ cliqueIndep G S, f I) + ∑ u ∈ compFiber G c, ∑ I ∈ cliqueIndep G S, f (insert u I) := by
  classical
  rw [cliqueIndep_insert_decomposition G c S hc,
    Finset.sum_union (cliqueIndep_disjoint_old_new G c S hc),
    Finset.sum_biUnion (cliqueIndep_pairwiseDisjoint G c S hc)]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  exact Finset.sum_image (cliqueIndep_insert_injOn G c S hc u hu)

lemma cliqueIndep_fresh (c : G.ConnectedComponent) (S : Finset G.ConnectedComponent)
    (hc : c ∉ S) (u : V) (hu : u ∈ compFiber G c) (I : Finset V) (hI : I ∈ cliqueIndep G S) : u ∉ I := by
  intro hui
  have huc : G.connectedComponentMk u = c := by simpa [compFiber] using hu
  have hS := (Finset.mem_filter.mp hI).2.1 u hui
  exact hc (huc ▸ hS)

lemma cliqueIndep_Z_step (lam : V → ℝ) (c : G.ConnectedComponent)
    (S : Finset G.ConnectedComponent) (hc : c ∉ S) :
    (∑ I ∈ cliqueIndep G (insert c S), ∏ v ∈ I, lam v) =
      (1 + ∑ u ∈ compFiber G c, lam u) * (∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v) := by
  classical
  rw [cliqueIndep_sum_insert G c S hc]
  have h : (∑ u ∈ compFiber G c, ∑ I ∈ cliqueIndep G S, ∏ v ∈ insert u I, lam v) =
      (∑ u ∈ compFiber G c, lam u) * (∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    exact Finset.prod_insert (cliqueIndep_fresh G c S hc u hu I hI)
  rw [h]
  ring

lemma cliqueIndep_A_step (lam a : V → ℝ) (c : G.ConnectedComponent)
    (S : Finset G.ConnectedComponent) (hc : c ∉ S) :
    (∑ I ∈ cliqueIndep G (insert c S), (∏ v ∈ I, lam v) * ∑ v ∈ I, a v) =
      (1 + ∑ u ∈ compFiber G c, lam u) *
        (∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * ∑ v ∈ I, a v) +
      (∑ u ∈ compFiber G c, lam u * a u) * (∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v) := by
  classical
  rw [cliqueIndep_sum_insert G c S hc]
  have h : (∑ u ∈ compFiber G c, ∑ I ∈ cliqueIndep G S,
      (∏ v ∈ insert u I, lam v) * ∑ v ∈ insert u I, a v) =
      (∑ u ∈ compFiber G c, lam u) * (∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * ∑ v ∈ I, a v) +
      (∑ u ∈ compFiber G c, lam u * a u) * (∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    have hf := cliqueIndep_fresh G c S hc u hu I hI
    rw [Finset.prod_insert hf, Finset.sum_insert hf]
    ring
  rw [h]
  ring

lemma cliqueIndep_B_step (lam a : V → ℝ) (c : G.ConnectedComponent)
    (S : Finset G.ConnectedComponent) (hc : c ∉ S) :
    (∑ I ∈ cliqueIndep G (insert c S), (∏ v ∈ I, lam v) * (∑ v ∈ I, a v)^2) =
      (1 + ∑ u ∈ compFiber G c, lam u) *
        (∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * (∑ v ∈ I, a v)^2) +
      2 * (∑ u ∈ compFiber G c, lam u * a u) *
        (∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * ∑ v ∈ I, a v) +
      (∑ u ∈ compFiber G c, lam u * a u^2) * (∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v) := by
  classical
  rw [cliqueIndep_sum_insert G c S hc]
  have h : (∑ u ∈ compFiber G c, ∑ I ∈ cliqueIndep G S,
      (∏ v ∈ insert u I, lam v) * (∑ v ∈ insert u I, a v)^2) =
      (∑ u ∈ compFiber G c, lam u) * (∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * (∑ v ∈ I, a v)^2) +
      2 * (∑ u ∈ compFiber G c, lam u * a u) * (∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * ∑ v ∈ I, a v) +
      (∑ u ∈ compFiber G c, lam u * a u^2) * (∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v) := by
    have htwo : 2 * (∑ u ∈ compFiber G c, lam u * a u) =
        ∑ u ∈ compFiber G c, 2 * (lam u * a u) := by rw [Finset.mul_sum]
    rw [htwo, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    have hf := cliqueIndep_fresh G c S hc u hu I hI
    rw [Finset.prod_insert hf, Finset.sum_insert hf]
    ring
  rw [h]
  ring

noncomputable def cliqueZ (lam : V → ℝ) (S : Finset G.ConnectedComponent) : ℝ :=
  ∑ I ∈ cliqueIndep G S, ∏ v ∈ I, lam v
noncomputable def cliqueA (lam a : V → ℝ) (S : Finset G.ConnectedComponent) : ℝ :=
  ∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * ∑ v ∈ I, a v
noncomputable def cliqueB (lam a : V → ℝ) (S : Finset G.ConnectedComponent) : ℝ :=
  ∑ I ∈ cliqueIndep G S, (∏ v ∈ I, lam v) * (∑ v ∈ I, a v)^2

lemma cliqueIndep_empty : cliqueIndep G ∅ = {∅} := by
  ext I
  simp only [cliqueIndep, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    ext x
    simp only [Finset.notMem_empty, iff_false]
    exact fun hx => Finset.notMem_empty _ (h x hx)
  · rintro rfl
    refine ⟨by simp, by simp [Set.InjOn]⟩

lemma cliqueIndep_univ [DecidableRel G.Adj]
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) :
    cliqueIndep G Finset.univ = ({I | G.IsIndepSet (↑I : Set V)} : Finset (Finset V)) := by
  ext I
  simp only [cliqueIndep, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [simple_graph_clique_components_independent_iff_injective G hclique]
  simp

lemma cliqueZ_pos (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (S : Finset G.ConnectedComponent) :
    0 < cliqueZ G lam S := by
  unfold cliqueZ
  refine lt_of_lt_of_le zero_lt_one ?_
  have h_empty : (∏ v ∈ (∅ : Finset V), lam v) = 1 := Finset.prod_empty
  rw [← h_empty]
  have hem : (∅ : Finset V) ∈ cliqueIndep G S := by simp [cliqueIndep, Set.InjOn]
  exact Finset.single_le_sum (f := fun I : Finset V => ∏ v ∈ I, lam v)
    (fun I _ => Finset.prod_nonneg fun v _ => le_of_lt (hlam v)) hem

lemma cliqueBound_eq [DecidableRel G.Adj]
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) (lam a : V → ℝ) :
    hardCoreWeightedClosedNeighborhoodBound G lam a =
      ∑ c : G.ConnectedComponent, (∑ v ∈ compFiber G c, lam v * a v^2) /
        (1 + ∑ u ∈ compFiber G c, lam u)^2 := by
  classical
  unfold hardCoreWeightedClosedNeighborhoodBound
  rw [← Finset.sum_fiberwise Finset.univ G.connectedComponentMk
    (fun v => (a v ^ 2 * lam v) / (1 + ∑ u ∈ insert v (G.neighborFinset v), lam u)^2)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  have hvc : G.connectedComponentMk v = c := by simpa [compFiber] using hv
  rw [simple_graph_clique_components_closed_neighborhood G hclique v, hvc]
  change (a v^2 * lam v) / (1 + ∑ u ∈ compFiber G c, lam u)^2 = _
  ring

lemma cliqueVar_eq_sum [DecidableRel G.Adj]
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) (lam a : V → ℝ)
    (hlam : ∀ v, 0 < lam v) :
    hardCoreWeightedVar G lam a =
      ∑ c : G.ConnectedComponent,
        ((∑ v ∈ compFiber G c, lam v * a v^2) / (1 + ∑ v ∈ compFiber G c, lam v) -
        ((∑ v ∈ compFiber G c, lam v * a v) / (1 + ∑ v ∈ compFiber G c, lam v))^2) := by
  classical
  have hZ : ∀ S, cliqueZ G lam S ≠ 0 := fun S => ne_of_gt (cliqueZ_pos G lam hlam S)
  have hs : ∀ c, 1 + (∑ v ∈ compFiber G c, lam v) ≠ 0 := by
    intro c
    have h : 0 ≤ ∑ v ∈ compFiber G c, lam v := Finset.sum_nonneg fun v _ => le_of_lt (hlam v)
    linarith
  have hb : cliqueA G lam a ∅ = 0 ∧ cliqueB G lam a ∅ = 0 := by
    simp [cliqueA, cliqueB, cliqueIndep_empty]
  have hrec := finite_variance_recurrence_additive (cliqueZ G lam) (cliqueA G lam a) (cliqueB G lam a)
    (fun c => ∑ v ∈ compFiber G c, lam v)
    (fun c => ∑ v ∈ compFiber G c, lam v * a v)
    (fun c => ∑ v ∈ compFiber G c, lam v * a v^2)
    hZ hs hb
    (fun c S hc => cliqueIndep_Z_step G lam c S hc)
    (fun c S hc => cliqueIndep_A_step G lam a c S hc)
    (fun c S hc => cliqueIndep_B_step G lam a c S hc) Finset.univ
  have hv : hardCoreWeightedVar G lam a =
      cliqueB G lam a Finset.univ / cliqueZ G lam Finset.univ -
        (cliqueA G lam a Finset.univ / cliqueZ G lam Finset.univ)^2 := by
    unfold hardCoreWeightedVar cliqueB cliqueA cliqueZ
    rw [cliqueIndep_univ G hclique]
  rw [hv, hrec]

theorem in703_main [DecidableRel G.Adj]
    (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) :
    hardCoreWeightedClosedNeighborhoodBound G lam a ≤ hardCoreWeightedVar G lam a := by
  rw [cliqueBound_eq G hclique lam a, cliqueVar_eq_sum G hclique lam a hlam]
  apply Finset.sum_le_sum
  intro c hc
  apply op_1355_complete_graph_div_sq_le_div_sub_div_sq
  · exact Finset.sum_nonneg fun v _ => le_of_lt (hlam v)
  · exact op_1355_complete_graph_weighted_cauchy_schwarz (compFiber G c) lam a fun v _ => le_of_lt (hlam v)

end In703

/-- On any finite graph whose connected components are cliques, the weighted hard-core closed-neighborhood variance bound holds. -/
theorem op_1355_clique_components_variance_ge_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (lam : V → ℝ) (hlam : ∀ v, 0 < lam v) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hclique : ∀ c : G.ConnectedComponent, G.IsClique c.supp) :
    hardCoreWeightedClosedNeighborhoodBound G lam a ≤ hardCoreWeightedVar G lam a := by
  exact In703.in703_main G lam hlam a ha hclique
