import AFTD.Prelude
import AFTD.Kb.Tcs.MultidimInstance

/-!
# multidim_instance_exists

Topic: online_algorithms   Node: 2610b0423080

Provenance: helper lemma. arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 2.1

For every natural number D ≥ 1, there exists an instance of multidimensional scheduling with D resources.
-/

/-- Witness that MultidimInstance D is nonempty for D ≥ 1. -/
theorem multidim_instance_exists (D : ℕ) (hD : 1 ≤ D) : Nonempty (MultidimInstance D) := ⟨{
  n := 1
  hn := Nat.zero_lt_one
  p := fun _ => 1
  hp := fun _ => Real.zero_lt_one
  u := fun _ => 1
  hu := fun _ => Real.zero_lt_one
  a := fun _ _ => 1
  ha_nonneg := fun _ _ => zero_le_one
  ha_le_one := fun _ _ => le_rfl
  ha_dominant := fun _ => ⟨⟨0, hD⟩, rfl⟩
}⟩
