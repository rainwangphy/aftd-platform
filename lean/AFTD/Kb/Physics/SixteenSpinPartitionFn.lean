import AFTD.Prelude
import AFTD.Kb.Physics.SixteenSpinWeight

/-!
# sixteen_spin_partition_fn

Topic: quantum_mechanics   Node: ba6e7d7bc32c

Provenance: formalization of a published result. Source: OP-1695; arXiv:2610.27080

For a simple graph G on a finite type V with decidable equality and decidable adjacency, and an edge angle function θ : Sym2 V → ℝ on unordered pairs of vertices, sixteen_spin_partition_fn G θ is defined as (1 / (16 ^ Fintype.card V : ℂ)) times the sum over all spin configurations s : V → Fin 4 → Fin 2 of the product over all edges e ∈ G.edgeFinset of sixteen_spin_weight (θ e) (fun i => if s u i = s v i then 0 else 1), evaluating on endpoints u, v of e via Sym2.lift.
-/

open scoped Classical in
/-- The sixteen-spin partition function for an edge-weighted graph G with angles on Sym2 V. -/
noncomputable def sixteen_spin_partition_fn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (θ : Sym2 V → ℝ) : ℂ := (1 / (16 ^ Fintype.card V : ℂ)) *
    ∑ s : V → Fin 4 → Fin 2,
      ∏ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => sixteen_spin_weight (θ s(u, v)) (fun i => if s u i = s v i then 0 else 1),
                  fun u v => by
                    have h : (fun i => (if s u i = s v i then (0 : Fin 2) else 1)) =
                             (fun i => (if s v i = s u i then (0 : Fin 2) else 1)) := by
                      funext i; by_cases heq : s u i = s v i <;> simp [heq, eq_comm]
                    simp [h, Sym2.eq_swap]⟩ e
