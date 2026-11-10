import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenGraph
import AFTD.Kb.Physics.HardCoreVarSize
import AFTD.Kb.Physics.PetersenPolyVariancePerVertex
import AFTD.Kb.Tcs.Weight

/-!
# petersen_hard_core_var_per_vertex_eq_poly

Topic: statistical_mechanics   Node: 26df004f00dc

Provenance: formalization of a published result. Source: arXiv:1806.02146, folklore

For every real activity x, the per-vertex hard-core variance of the Petersen graph hardCoreVarSize petersen_graph (fun _ => x) / 10 equals petersen_poly_variance_per_vertex x.
-/

/-- The vertex type of the Petersen graph: two-element subsets of `Fin 5`. -/
abbrev petersen_hard_core_var_per_vertex_eq_poly_V : Type := {s : Finset (Fin 5) // s.card = 2}

/-- Decidable adjacency for the Petersen graph (the Kneser graph `K(5,2)`). -/
instance petersen_hard_core_var_per_vertex_eq_poly_decRel : DecidableRel petersen_graph.Adj :=
  fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))

/-- A `Finset`-level form of independence: no two distinct members are adjacent. -/
abbrev petersen_hard_core_var_per_vertex_eq_poly_indep
    (I : Finset petersen_hard_core_var_per_vertex_eq_poly_V) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ petersen_graph.Adj a b

/-- Independence of a finset is the same as being an independent set of the graph. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_isIndepSet_iff
    (I : Finset petersen_hard_core_var_per_vertex_eq_poly_V) :
    petersen_graph.IsIndepSet (I : Set petersen_hard_core_var_per_vertex_eq_poly_V) ↔
      petersen_hard_core_var_per_vertex_eq_poly_indep I := by
  simp only [SimpleGraph.isIndepSet_iff, Set.Pairwise, petersen_hard_core_var_per_vertex_eq_poly_indep,
    Finset.mem_coe]

/-- The independent sets of the Petersen graph, as a finset of finsets of vertices. -/
abbrev petersen_hard_core_var_per_vertex_eq_poly_indepSets :
    Finset (Finset petersen_hard_core_var_per_vertex_eq_poly_V) :=
  Finset.univ.filter (fun I =>
    petersen_graph.IsIndepSet (I : Set petersen_hard_core_var_per_vertex_eq_poly_V))

/-- Independent sets of size `k` are exactly the independent `k`-subsets of all vertices. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_filter_card_eq (k : ℕ) :
    petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = k) =
      Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
        (Finset.powersetCard k
          (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V)) := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_indepSets, Finset.filter_filter,
    Finset.powersetCard_eq_filter, Finset.powerset_univ, Finset.filter_filter]
  exact Finset.filter_congr (fun I _ => by
    rw [petersen_hard_core_var_per_vertex_eq_poly_isIndepSet_iff]
    tauto)

/-- There is exactly one independent set of size `0` in the Petersen graph. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_count_0 :
    (Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 0
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V))).card = 1 := by
  decide

/-- There are exactly ten independent sets of size `1` in the Petersen graph. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_count_1 :
    (Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 1
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V))).card = 10 := by
  decide

/-- There are exactly thirty independent sets of size `2` in the Petersen graph. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_count_2 :
    (Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 2
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V))).card = 30 := by
  decide

/-- There are exactly thirty independent sets of size `3` in the Petersen graph. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_count_3 :
    (Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 3
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V))).card = 30 := by
  decide

/-- There are exactly five independent sets of size `4` in the Petersen graph. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_count_4 :
    (Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 4
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V))).card = 5 := by
  decide

/-- The Petersen graph has no independent set of size `5`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_count_5 :
    (Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 5
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V))).card = 0 := by
  decide

/-- The number of independent sets of size `0`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_0 :
    (petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = 0)).card = 1 := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_filter_card_eq,
    petersen_hard_core_var_per_vertex_eq_poly_count_0]

/-- The number of independent sets of size `1`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_1 :
    (petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = 1)).card = 10 := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_filter_card_eq,
    petersen_hard_core_var_per_vertex_eq_poly_count_1]

/-- The number of independent sets of size `2`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_2 :
    (petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = 2)).card = 30 := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_filter_card_eq,
    petersen_hard_core_var_per_vertex_eq_poly_count_2]

/-- The number of independent sets of size `3`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_3 :
    (petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = 3)).card = 30 := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_filter_card_eq,
    petersen_hard_core_var_per_vertex_eq_poly_count_3]

/-- The number of independent sets of size `4`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_4 :
    (petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = 4)).card = 5 := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_filter_card_eq,
    petersen_hard_core_var_per_vertex_eq_poly_count_4]

/-- A subset of an independent finset is independent. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indep_mono
    {I J : Finset petersen_hard_core_var_per_vertex_eq_poly_V}
    (h : petersen_hard_core_var_per_vertex_eq_poly_indep I) (hJI : J ⊆ I) :
    petersen_hard_core_var_per_vertex_eq_poly_indep J :=
  fun a ha b hb hab => h a (hJI ha) b (hJI hb) hab

/-- Every independent finset of the Petersen graph has at most four vertices. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_card_le_four
    {I : Finset petersen_hard_core_var_per_vertex_eq_poly_V}
    (h : petersen_hard_core_var_per_vertex_eq_poly_indep I) : I.card ≤ 4 := by
  by_contra hc
  rw [Nat.not_le] at hc
  obtain ⟨J, hJ, hJc⟩ := Finset.exists_subset_card_eq (s := I) (n := 5) hc
  have hJmem : J ∈ Finset.filter petersen_hard_core_var_per_vertex_eq_poly_indep
      (Finset.powersetCard 5
        (Finset.univ : Finset petersen_hard_core_var_per_vertex_eq_poly_V)) := by
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ J, hJc⟩, petersen_hard_core_var_per_vertex_eq_poly_indep_mono h hJ⟩
  have hne := Finset.card_ne_zero_of_mem hJmem
  rw [petersen_hard_core_var_per_vertex_eq_poly_count_5] at hne
  exact hne rfl

/-- Every independent set of the Petersen graph has at most four vertices. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_indepSets_card_le_four
    {I : Finset petersen_hard_core_var_per_vertex_eq_poly_V}
    (hI : I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets) : I.card ≤ 4 := by
  rw [petersen_hard_core_var_per_vertex_eq_poly_indepSets, Finset.mem_filter] at hI
  exact petersen_hard_core_var_per_vertex_eq_poly_card_le_four
    ((petersen_hard_core_var_per_vertex_eq_poly_isIndepSet_iff I).mp hI.2)

/-- Independent-set counts of the Petersen graph with the weight `x ^ |I| · g |I|`,
grouped by the size `|I|` of the independent set. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_sum_eq (g : ℕ → ℝ) (x : ℝ) :
    (∑ I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets, x ^ I.card * g I.card) =
      1 * (x ^ 0 * g 0) + 10 * (x ^ 1 * g 1) + 30 * (x ^ 2 * g 2) + 30 * (x ^ 3 * g 3) +
        5 * (x ^ 4 * g 4) := by
  have hstep : ∀ j : ℕ,
      (∑ I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter (fun I => I.card = j),
          x ^ I.card * g I.card) =
        ((petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter
          (fun I => I.card = j)).card : ℝ) * (x ^ j * g j) := by
    intro j
    rw [show ((petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter
          (fun I => I.card = j)).card : ℝ) * (x ^ j * g j) =
        ∑ _I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets.filter
          (fun I => I.card = j), (x ^ j * g j) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_congr rfl (fun I hI => by
      simp only [Finset.mem_filter] at hI
      rw [hI.2])
  have hmem : ∀ I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets,
      I.card ∈ Finset.range 5 := by
    intro I hI
    rw [Finset.mem_range]
    have h := petersen_hard_core_var_per_vertex_eq_poly_indepSets_card_le_four hI
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := petersen_hard_core_var_per_vertex_eq_poly_indepSets)
    (t := Finset.range 5) (g := fun I => I.card) hmem
    (f := fun I => x ^ I.card * g I.card)
  rw [← hfib]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hstep,
    petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_0,
    petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_1,
    petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_2,
    petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_3,
    petersen_hard_core_var_per_vertex_eq_poly_indepSets_count_4]
  push_cast
  ring

/-- The hard-core partition function of the Petersen graph at activity `x`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_sum_Z (x : ℝ) :
    (∑ I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets, x ^ I.card) =
      1 + 10 * x + 30 * x ^ 2 + 30 * x ^ 3 + 5 * x ^ 4 := by
  have h := petersen_hard_core_var_per_vertex_eq_poly_sum_eq (fun _ => (1 : ℝ)) x
  simp only [mul_one] at h
  rw [h]
  ring

/-- The first moment of the independent set size of the Petersen graph at activity `x`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_sum_A1 (x : ℝ) :
    (∑ I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets, x ^ I.card * (I.card : ℝ)) =
      10 * x + 60 * x ^ 2 + 90 * x ^ 3 + 20 * x ^ 4 := by
  have h := petersen_hard_core_var_per_vertex_eq_poly_sum_eq (fun k : ℕ => (k : ℝ)) x
  rw [h]
  push_cast
  ring

/-- The second moment of the independent set size of the Petersen graph at activity `x`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_sum_A2 (x : ℝ) :
    (∑ I ∈ petersen_hard_core_var_per_vertex_eq_poly_indepSets,
      x ^ I.card * (I.card : ℝ) ^ 2) =
      10 * x + 120 * x ^ 2 + 270 * x ^ 3 + 80 * x ^ 4 := by
  have h := petersen_hard_core_var_per_vertex_eq_poly_sum_eq (fun k : ℕ => (k : ℝ) ^ 2) x
  rw [h]
  push_cast
  ring

/-- The per-vertex hard-core variance of the Petersen graph equals the variance computed
from its independence polynomial `1 + 10x + 30x² + 30x³ + 5x⁴`. -/
lemma petersen_hard_core_var_per_vertex_eq_poly_main (x : ℝ) :
    hardCoreVarSize petersen_graph (fun _ => x) / 10 = petersen_poly_variance_per_vertex x := by
  simp only [hardCoreVarSize, petersen_poly_variance_per_vertex, Finset.prod_const]
  rw [petersen_hard_core_var_per_vertex_eq_poly_sum_Z,
    petersen_hard_core_var_per_vertex_eq_poly_sum_A1,
    petersen_hard_core_var_per_vertex_eq_poly_sum_A2]

/-- The combinatorial hard-core variance per vertex of the Petersen graph equals its polynomial expression. -/
theorem petersen_hard_core_var_per_vertex_eq_poly (x : ℝ) :
    letI : DecidableRel petersen_graph.Adj := fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))
    hardCoreVarSize petersen_graph (fun _ => x) / 10 = petersen_poly_variance_per_vertex x := by
  exact petersen_hard_core_var_per_vertex_eq_poly_main x
