import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_idle_measure_sum_eq_one

Topic: graphs   Node: 3858c02582ed

Provenance: helper lemma. Sanity check of the definitions of arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 2.2.

μ_x^α is a probability measure (total mass 1) when x has a neighbour.
-/

theorem graph_idle_measure_sum_eq_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (x : V) (hx : 0 < G.degree x) :
    ∑ v, graph_idle_measure G α x v = 1 := by
  unfold graph_idle_measure
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  simp only [if_true]
  have : ∑ v ∈ Finset.univ.erase x, (if v = x then α else if G.Adj x v then (1 - α) / (G.degree x : ℝ) else 0)
      = ∑ v ∈ Finset.univ.erase x, (if G.Adj x v then (1 - α) / (G.degree x : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [if_neg (Finset.ne_of_mem_erase hv)]
  rw [this, ← Finset.sum_filter]
  have hf : (Finset.univ.erase x).filter (G.Adj x) = G.neighborFinset x := by
    ext v; simp [SimpleGraph.mem_neighborFinset]
    intro h; exact (G.ne_of_adj h).symm
  rw [hf, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp
  ring
