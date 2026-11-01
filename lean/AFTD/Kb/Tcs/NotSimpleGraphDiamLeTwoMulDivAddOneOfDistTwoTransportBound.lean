import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphExistsGeodesicVertexFamily
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# not_simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound

Topic: graphs   Node: 18fdcbeb28c2

Provenance: original. Related work: refutes `simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound`

The statement `simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound` is false: The statement is false due to truncated natural number subtraction `k - c : ℕ` in the hypothesis `hbound`.

Specifically, if `c > 2 * k` (e.g. `k = 2`, `c = 5`), then `k - c = 0` in `ℕ`, so the right-hand side `2 * ((k - c : ℕ) : ℝ)` evaluates to `0`.
On `C_4` (the 4-cycle `SimpleGraph.cycleGraph 4`):
- It is regular of degree `k = 2`.
- `0 < c` holds for `c = 5`.
- For any pair `p, q` at distance 2, their neighbor sets are identical: `{0 - 1, 0 + 1} = {1, 3} = {2 - 1, 2 + 1}`. Therefore, for ANY function `f : V → ℝ`, `∑ z ∈ neighborFinset q, f z - ∑ z ∈ neighborFinset p, f z = 0 ≤ 0`. Thus `hbound` is satisfied.
- The diameter of `C_4` is 2.
- But `2 * k / c + 1 = 2 * 2 / 5 + 1 = 0 + 1 = 1`.
Thus the conclusion `G.diam ≤ 2 * k / c + 1` requires `2 ≤ 1`, which is false.
-/

universe u

/-- The 4-cycle as the parity graph on `ULift (Fin 4)`. -/
def ulift_four_cycle_parity : SimpleGraph (ULift.{u} (Fin 4)) where
  Adj a b := a.down.val % 2 ≠ b.down.val % 2
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

instance ulift_four_cycle_parity_dec : DecidableRel (ulift_four_cycle_parity.{u}).Adj := fun a b =>
  decidable_of_iff (a.down.val % 2 ≠ b.down.val % 2) Iff.rfl

theorem ulift_four_cycle_parity_regular : (ulift_four_cycle_parity.{u}).IsRegularOfDegree 2 := by
  intro v
  revert v
  decide

theorem ulift_four_cycle_parity_nbhd_eq : ∀ p q : ULift.{u} (Fin 4), p ≠ q →
    ¬ (ulift_four_cycle_parity.{u}).Adj p q →
    (ulift_four_cycle_parity.{u}).neighborFinset p = (ulift_four_cycle_parity.{u}).neighborFinset q := by
  decide

theorem ulift_four_cycle_parity_two_le_diam : 2 ≤ (ulift_four_cycle_parity.{u}).diam := by
  have hconn : (ulift_four_cycle_parity.{u}).Connected := by
    have h0 : ∀ v : ULift.{u} (Fin 4), (ulift_four_cycle_parity.{u}).Reachable ⟨0⟩ v := by
      have h1 : (ulift_four_cycle_parity.{u}).Adj ⟨0⟩ ⟨1⟩ := by decide
      have h3 : (ulift_four_cycle_parity.{u}).Adj ⟨0⟩ ⟨3⟩ := by decide
      have h12 : (ulift_four_cycle_parity.{u}).Adj ⟨1⟩ ⟨2⟩ := by decide
      rintro ⟨v⟩
      fin_cases v
      · exact SimpleGraph.Reachable.refl _
      · exact h1.reachable
      · exact h1.reachable.trans h12.reachable
      · exact h3.reachable
    exact ⟨fun u v => (h0 u).symm.trans (h0 v)⟩
  have hed : (ulift_four_cycle_parity.{u}).ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have hne : (ulift_four_cycle_parity.{u}).dist ⟨0⟩ ⟨2⟩ ≠ 0 :=
    SimpleGraph.dist_ne_zero_iff_ne_and_reachable.mpr ⟨by decide, hconn.preconnected _ _⟩
  have hn1 : (ulift_four_cycle_parity.{u}).dist ⟨0⟩ ⟨2⟩ ≠ 1 := fun h1 =>
    absurd (SimpleGraph.dist_eq_one_iff_adj.mp h1) (by decide)
  have := SimpleGraph.dist_le_diam (u := ⟨0⟩) (v := ⟨2⟩) hed
  omega

theorem not_simple_graph_diam_le_two_mul_div_add_one_of_dist_two_transport_bound : ¬ (∀ {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k c : ℕ} (hreg : G.IsRegularOfDegree k) (hc : 0 < c)
    (hbound : ∀ (p q : V), G.dist p q = 2 → ∀ f : V → ℝ,
      (∀ a b : V, |f a - f b| ≤ (G.dist a b : ℝ)) →
      ∑ z ∈ G.neighborFinset q, f z - ∑ z ∈ G.neighborFinset p, f z ≤ 2 * ((k - c : ℕ) : ℝ)), G.diam ≤ 2 * k / c + 1) := by
  intro h
  have key := h (G := ulift_four_cycle_parity) (k := 2) (c := 5) ulift_four_cycle_parity_regular
    (by norm_num) (by
      intro p q hpq f _
      have hpq' : p ≠ q := by
        rintro rfl
        simp at hpq
      have hadj : ¬ ulift_four_cycle_parity.Adj p q := fun ha => by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha] at hpq
        omega
      rw [ulift_four_cycle_parity_nbhd_eq p q hpq' hadj]
      norm_num)
  have h2 := ulift_four_cycle_parity_two_le_diam.trans key
  omega
