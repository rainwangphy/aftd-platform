import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverFibreEndpointUnique
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_cycle_power_dyadic_class_model_disjoint_colours

Topic: combinatorics   Node: e841a8308353

Provenance: helper lemma. step towards simple_graph_cycle_power_dyadic_cover_class_model

Two active rooted classes at a common vertex with distinct offsets have distinct layer colours.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- At a common vertex, two distinct active rooted classes of an optimal dyadic cover never share a layer colour. -/
theorem simple_graph_cycle_power_dyadic_class_model_disjoint_colours
    (m n : ℕ) [NeZero n] (hm : 1 ≤ m)
    (hn : 3 * (2 ^ m - 1) + 1 ≤ n)
    (c : Fin (m + 1) → ZMod n → ZMod n)
    (hc : ∀ s u v, u ≠ v → c s u = c s v →
      (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v)
    (hcov : ∀ u v, (simple_graph_cycle_power n (2 ^ m - 1)).Adj u v →
      ∃ s, c s u = c s v)
    (ell : ℤ → Fin (m + 1))
    (hellroot : ∀ p : ℤ,
      c (ell p) ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c (ell p) (p : ZMod n))
    (helluniq : ∀ (p : ℤ) (s : Fin (m + 1)),
      c s ((p : ZMod n) + ((2 ^ m - 1 : ℕ) : ZMod n)) = c s (p : ZMod n) → s = ell p)
    (v : ℤ) (a b : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (hab : a ≠ b)
    (hxa : c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n) + (a : ZMod n)) =
      c (ell (v - (a : ℤ))) (((v - (a : ℤ) : ℤ) : ZMod n)))
    (hxb : c (ell (v - (b : ℤ))) (((v - (b : ℤ) : ℤ) : ZMod n) + (b : ZMod n)) =
      c (ell (v - (b : ℤ))) (((v - (b : ℤ) : ℤ) : ZMod n))) :
    ell (v - (a : ℤ)) ≠ ell (v - (b : ℤ)) := by
  intro he
  have ha0 : ((v-(a : ℤ) : ℤ) : ZMod n)+(a : ZMod n) = (v : ZMod n) := by push_cast; ring
  have hb0 : ((v-(b : ℤ) : ℤ) : ZMod n)+(b : ZMod n) = (v : ZMod n) := by push_cast; ring
  rw [ha0] at hxa
  rw [hb0, ← he] at hxb
  have hpa := (hellroot (v-(a : ℤ))).symm
  have hpb := (hellroot (v-(b : ℤ))).symm
  rw [← he] at hpb
  have hroot := simple_graph_cycle_power_dyadic_cover_fibre_endpoint_unique m n hn
    (c (ell (v-(a : ℤ)))) (hc (ell (v-(a : ℤ))))
    ((v-(a : ℤ) : ℤ) : ZMod n) ((v-(b : ℤ) : ℤ) : ZMod n)
    hpa hpb (hxa.symm.trans hxb)
  simp only [Int.cast_sub, Int.cast_natCast] at hroot
  have hcast : (a : ZMod n) = (b : ZMod n) := sub_right_inj.mp hroot
  have hnat : a=b := Nat.ModEq.eq_of_lt_of_lt
    ((ZMod.natCast_eq_natCast_iff _ _ n).mp hcast) (by omega) (by omega)
  exact hab hnat
