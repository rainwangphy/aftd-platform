import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy

/-!
# op_2130_converse_from_path_witness

Topic: online_algorithms   Node: ba678c03ee78

Provenance: helper lemma. step towards op_2130_repeated_path_greedy_sharp_cubic_exponential_tail

If for every D ≥ 1 there is a path edge sequence of length at most D³ on P_{2D} and one coin tape whose greedy run reaches maximum prefix discrepancy D, then the converse conjunct of OP-2130 holds with C' = 2.
-/

/-- The deterministic single-tape witness implies the converse conjunct with constant C' = 2. -/
theorem op_2130_converse_from_path_witness
    (hwit : ∀ (D : ℕ), 1 ≤ D →
      ∃ (edges : List (Fin (2 * D) × Fin (2 * D))),
        (∀ e ∈ edges, (SimpleGraph.pathGraph (2 * D)).Adj e.1 e.2) ∧
        edges.length ≤ D ^ 3 ∧
        ∃ coin : Fin edges.length → Bool,
          D ≤ carpool_max_discrepancy (2 * D) edges
                (carpool_greedy_orientations (2 * D) edges (List.ofFn coin))) :
    ∃ (C' : ℝ), 0 < C' ∧
      ∀ (D : ℕ) (hD : 1 ≤ D),
        ∃ (edges : List (Fin (2 * D) × Fin (2 * D))),
          (∀ e ∈ edges, (SimpleGraph.pathGraph (2 * D)).Adj e.1 e.2) ∧
          edges.length ≤ D ^ 3 ∧
          let T := edges.length
          let high_discrepancy := Finset.univ.filter (fun r : Fin T → Bool =>
            D ≤ carpool_max_discrepancy (2 * D) edges
              (carpool_greedy_orientations (2 * D) edges (List.ofFn r)))
          Real.exp (-C' * (D : ℝ) ^ 3) ≤ ((high_discrepancy.card : ℝ) / (2 ^ T : ℝ)) := by
  classical
  refine ⟨2, by norm_num, ?_⟩
  intro D hD
  obtain ⟨edges, he, hlen, coin, hcoin⟩ := hwit D hD
  refine ⟨edges, he, hlen, ?_⟩
  let G := Finset.univ.filter (fun r : Fin edges.length → Bool =>
    D ≤ carpool_max_discrepancy (2 * D) edges
      (carpool_greedy_orientations (2 * D) edges (List.ofFn r)))
  change Real.exp (-(2 : ℝ) * (D : ℝ)^3) ≤ (G.card : ℝ) / (2 ^ edges.length : ℝ)
  have hG : (1 : ℝ) ≤ (G.card : ℝ) := by
    have hn : 1 ≤ G.card := by
      apply Finset.one_le_card.mpr
      exact ⟨coin, by simp [G, hcoin]⟩
    exact_mod_cast hn
  have hexp2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hpow : (2 : ℝ)^edges.length ≤ (Real.exp 2)^edges.length :=
    pow_le_pow_left₀ (by positivity) hexp2 _
  have htime : (edges.length : ℝ) ≤ (D : ℝ)^3 := by exact_mod_cast hlen
  have hbig : (2 : ℝ)^edges.length ≤ Real.exp (2 * (D : ℝ)^3) := by
    apply le_trans hpow
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hrecip : 1 / Real.exp (2 * (D : ℝ)^3) ≤ 1 / (2 : ℝ)^edges.length :=
    one_div_le_one_div_of_le (by positivity) hbig
  have hneg : Real.exp (-(2 : ℝ) * (D : ℝ)^3) = 1 / Real.exp (2 * (D : ℝ)^3) := by
    rw [show -(2 : ℝ) * (D : ℝ)^3 = -(2 * (D : ℝ)^3) by ring, Real.exp_neg]
    ring
  rw [hneg]
  exact le_trans hrecip (div_le_div_of_nonneg_right hG (by positivity))
