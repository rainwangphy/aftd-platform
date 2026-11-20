import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# four_vertex_shores_force_many_complement_walks

Topic: graphs   Node: 47fff9091578

Provenance: helper lemma. Arithmetic step in the saturated-twin bridge-count route for OP-1957.

If a,b are at least four and a+b=d+1, their product is at least 4(d−3).
-/

theorem four_vertex_shores_force_many_complement_walks
    (d a b : ℕ) (ha : 4 ≤ a) (hb : 4 ≤ b)
    (hs : a + b = d + 1) : 4 * (d - 3) ≤ a * b := by
  have hd3 : 3 ≤ d := by omega
  have ha' : (4:ℤ) ≤ (a:ℤ) := by exact_mod_cast ha
  have hb' : (4:ℤ) ≤ (b:ℤ) := by exact_mod_cast hb
  have hnon : (0:ℤ) ≤ ((a:ℤ)-4)*((b:ℤ)-4) := by
    apply mul_nonneg <;> linarith
  have hs' : (a:ℤ)+(b:ℤ) = (d:ℤ)+1 := by exact_mod_cast hs
  have hgoal : 4 * ((d:ℤ) - 3) ≤ (a:ℤ)*(b:ℤ) := by
    nlinarith
  have hsub : ((d - 3 : ℕ) : ℤ) = (d:ℤ) - 3 := Nat.cast_sub hd3
  have hmain : ((4*(d-3):ℕ):ℤ) ≤ ((a*b:ℕ):ℤ) := by
    push_cast
    rw [hsub]
    exact hgoal
  exact_mod_cast hmain
