import AFTD.Prelude
import AFTD.Kb.Physics.RandomIsingGraphMagic
import AFTD.Kb.Physics.ErdosRenyiHalf
import AFTD.Kb.Tcs.PauliLiouvilleMomentTwo
import AFTD.Kb.Physics.IsingGraphState
import AFTD.Kb.Physics.PauliMomentTwoEqFourReplicaSum

/-!
# op_1734_random_ising_magic_one

Topic: quantum_mechanics   Node: d4aca5be2bff

Provenance: formalization of a published result. Source: arXiv:2610.27080, Rényi multi-entropy of graph states and the n -> 1 limit

The expected value of random_ising_graph_magic 1 with respect to the Erdős-Rényi measure erdos_renyi_half 1 equals 2.
-/

open scoped Classical BigOperators

theorem op_1734_random_ising_magic_one_psi (G : SimpleGraph (Fin 1)) (θ : Sym2 (Fin 1) → ℝ) (x : Fin 1 → Fin 2) :
    (ising_graph_state 1 G θ).ofLp x = 1 / Real.sqrt 2 := by
  dsimp [ising_graph_state]
  have hE : G.edgeFinset = ∅ := by
    ext ⟨u, v⟩
    simp
  rw [hE]
  simp

theorem op_1734_random_ising_magic_one_val (G : SimpleGraph (Fin 1)) :
    random_ising_graph_magic 1 G = 2 := by
  dsimp [random_ising_graph_magic]
  have h_four := pauli_moment_two_eq_four_replica_sum 1 (ising_graph_state 1 G (fun _ => Real.pi / 8))
  simp only [op_1734_random_ising_magic_one_psi] at h_four
  have h_star : (starRingEnd ℂ) (1 / (Real.sqrt 2 : ℂ)) = 1 / (Real.sqrt 2 : ℂ) := by simp
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt zero_le_two
    exact_mod_cast this
  have h_pair : (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, h2]
  have h_prod : (starRingEnd ℂ) (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) *
    (starRingEnd ℂ) (1 / (Real.sqrt 2 : ℂ)) * (starRingEnd ℂ) (1 / (Real.sqrt 2 : ℂ)) *
          (1 / (Real.sqrt 2 : ℂ)) *
        (1 / (Real.sqrt 2 : ℂ)) *
      (starRingEnd ℂ) (1 / (Real.sqrt 2 : ℂ)) = 1 / 16 := by
    rw [h_star]
    calc
      (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) *
      (1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ)) *
            (1 / (Real.sqrt 2 : ℂ)) *
          (1 / (Real.sqrt 2 : ℂ)) *
        (1 / (Real.sqrt 2 : ℂ))
      _ = ((1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ))) *
          ((1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ))) *
          ((1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ))) *
          ((1 / (Real.sqrt 2 : ℂ)) * (1 / (Real.sqrt 2 : ℂ))) := by ring
      _ = (1 / 2) * (1 / 2) * (1 / 2) * (1 / 2) := by rw [h_pair]
      _ = 1 / 16 := by ring
  simp only [h_prod] at h_four
  have h_sum : (∑ _x : Fin 1 → Fin 2,
      ∑ _x_1 : Fin 1 → Fin 2,
        ∑ _x_2 : Fin 1 → Fin 2,
          ∑ _x_3 : Fin 1 → Fin 2, (1 / 16 : ℂ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    norm_num
  rw [h_sum] at h_four
  have h_mom : pauliLiouvilleMomentTwo 1 (ising_graph_state 1 G (fun _ => Real.pi / 8)) = 1 := by
    exact_mod_cast h_four
  rw [h_mom]
  norm_num

open scoped MeasureTheory in
/-- OP-1734 (partial): expected magic on G(1, 1/2) is 2. -/
theorem op_1734_random_ising_magic_one :
    ∫ G, random_ising_graph_magic 1 G ∂(erdos_renyi_half 1) = 2 := by
  have h : (fun G => random_ising_graph_magic 1 G) = fun _ => (2 : ℝ) := by
    ext G
    exact op_1734_random_ising_magic_one_val G
  rw [h]
  have : MeasureTheory.IsProbabilityMeasure (erdos_renyi_half 1) := by
    dsimp [erdos_renyi_half]
    infer_instance
  rw [MeasureTheory.integral_const]
  simp
